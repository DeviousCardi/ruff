//! Finite graphs of closed type equations, with recursive references confined to private bodies.

use std::cell::RefCell;

use rustc_hash::FxHashMap;
use salsa::plumbing::AsId;

use super::{
    RecursiveGraph, RecursiveMapping, RecursiveOrigin, RecursiveReferences, RecursiveSubstitution,
    RecursiveType, RecursiveVar,
};
use crate::types::set_theoretic::NegativeIntersectionElements;
use crate::types::visitor::TypeKind;
use crate::types::{
    ApplyTypeMappingVisitor, BoundTypeVarIdentity, InternedType, IntersectionType, Type,
    TypeContext, TypeMapping, UnionType,
};
use crate::{Db, FxIndexSet, FxOrderSet, ProgramEnvironment};

/// Maps closed input types to graph nodes; input order does not determine the final node order.
#[derive(Debug, Eq, PartialEq)]
pub(super) struct RecursiveGraphBuilder<'db> {
    inputs: RefCell<FxIndexSet<Type<'db>>>,
    equations: FxHashMap<Type<'db>, Type<'db>>,
    variables: FxHashMap<BoundTypeVarIdentity<'db>, Type<'db>>,
}

impl get_size2::GetSize for RecursiveGraphBuilder<'_> {}

/// Closed types for the input roots and whether any root belongs to a cycle.
pub(super) struct GraphSolution<'db> {
    pub(super) types: Vec<Type<'db>>,
    pub(super) recursive: bool,
}

impl<'db> RecursiveGraphBuilder<'db> {
    /// Keep atoms inline and register other closed types as graph dependencies.
    pub(super) fn reference(&self, db: &'db dyn Db, ty: Type<'db>) -> Type<'db> {
        let ty = match ty {
            Type::TypeVar(variable) => match self.variables.get(&variable.identity(db)) {
                Some(ty) => *ty,
                None => return ty,
            },
            _ if matches!(TypeKind::from(ty), TypeKind::Atomic) => return ty,
            _ => ty,
        };
        let (index, _) = self.inputs.borrow_mut().insert_full(ty);
        Type::RecursiveVar(RecursiveVar::new_internal(db, 0, index, None))
    }

    /// Build and minimize the reachable regular graph, then close each cyclic component.
    /// Constructor operations see closed inputs throughout extraction and mapping.
    pub(super) fn solve(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        roots: &[(Type<'db>, Type<'db>)],
    ) -> Option<GraphSolution<'db>> {
        Self {
            inputs: RefCell::new(roots.iter().map(|(root, _)| *root).collect()),
            equations: roots.iter().copied().collect(),
            variables: roots
                .iter()
                .filter_map(|(root, _)| {
                    let Type::TypeVar(variable) = root else {
                        return None;
                    };
                    Some((variable.identity(db), *root))
                })
                .collect(),
        }
        .finish(db, env, roots.len())
    }

    /// Minimize an already closed type, including a finite prefix of a recursive graph.
    pub(super) fn normalize(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        ty: Type<'db>,
    ) -> Type<'db> {
        Self {
            inputs: RefCell::new([ty].into_iter().collect()),
            equations: FxHashMap::default(),
            variables: FxHashMap::default(),
        }
        .finish(db, env, 1)
        .map_or(ty, |solution| solution.types[0])
    }

    fn finish(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        root_count: usize,
    ) -> Option<GraphSolution<'db>> {
        let builder = self;
        let mapping =
            TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Extract(&builder)));
        let visitor = ApplyTypeMappingVisitor::new(env);
        let mut bodies = Vec::new();
        loop {
            let input = builder.inputs.borrow().get_index(bodies.len()).copied();
            let Some(input) = input else {
                break;
            };
            let body = if let Some(body) = builder.equations.get(&input) {
                builder.reference(db, *body)
            } else if let Type::Recursive(recursive) = input
                && matches!(recursive.origin(db), RecursiveOrigin::ConstraintSolution(_))
            {
                recursive.map_type(db, env, |body| builder.reference(db, body))
            } else {
                input.apply_type_mapping_children(db, &mapping, TypeContext::default(), &visitor)
            };
            bodies.push(body);
        }
        let mut root_indices: Vec<_> = (0..root_count).collect();
        Self::remove_forwarding(db, env, &mut bodies, &mut root_indices)?;
        let unguarded: Vec<_> = bodies
            .iter()
            .map(|body| {
                if matches!(body, Type::Union(_) | Type::Intersection(_)) {
                    RecursiveReferences::indices(db, env, *body)
                } else {
                    Vec::new()
                }
            })
            .collect();
        if Self::components(&unguarded)
            .iter()
            .any(|component| component.len() > 1 || unguarded[component[0]].contains(&component[0]))
        {
            return None;
        }

        loop {
            let previous_len = bodies.len();
            Self::minimize(db, env, &mut bodies, &mut root_indices);
            Self::remove_forwarding(db, env, &mut bodies, &mut root_indices)?;
            if bodies.len() == previous_len {
                break;
            }
        }
        let edges: Vec<_> = bodies
            .iter()
            .map(|body| RecursiveReferences::indices(db, env, *body))
            .collect();
        let mut closed = vec![Type::Never; bodies.len()];
        let mut recursive_roots = vec![false; bodies.len()];
        for mut component in Self::components(&edges) {
            component.sort_unstable();
            let cyclic = component.len() > 1 || edges[component[0]].contains(&component[0]);
            if cyclic {
                for (local, global) in component.iter().enumerate() {
                    closed[*global] =
                        Type::RecursiveVar(RecursiveVar::new_internal(db, 0, local, None));
                    recursive_roots[*global] = true;
                }
            }
            let mapping =
                TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Rebuild(&closed)));
            let visitor = ApplyTypeMappingVisitor::new(env);
            let mut definitions: Vec<_> = component
                .iter()
                .map(|index| {
                    bodies[*index].apply_type_mapping_impl(
                        db,
                        &mapping,
                        TypeContext::default(),
                        &visitor,
                    )
                })
                .collect();
            if cyclic {
                // Canonical numbering is local to the component, so unrelated roots
                // and already-closed dependencies cannot change its interned identity.
                let mut entries: Vec<_> = (0..component.len()).collect();
                Self::minimize(db, env, &mut definitions, &mut entries);
                let graph = RecursiveGraph::new_internal(db, definitions.into_boxed_slice());
                for (local, index) in component.iter().enumerate() {
                    closed[*index] = Type::Recursive(RecursiveType::new_internal(
                        db,
                        RecursiveOrigin::ConstraintSolution(env.program(db)),
                        graph,
                        entries[local],
                        None,
                        None,
                    ));
                }
            } else {
                closed[component[0]] = definitions[0];
            }
        }
        Some(GraphSolution {
            recursive: root_indices.iter().any(|index| recursive_roots[*index]),
            types: root_indices
                .into_iter()
                .map(|index| closed[index])
                .collect(),
        })
    }

    /// Forwarding nodes have no constructor; remove them before comparing node labels.
    fn remove_forwarding(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        bodies: &mut Vec<Type<'db>>,
        roots: &mut [usize],
    ) -> Option<()> {
        let mut targets = vec![None; bodies.len()];
        for start in 0..bodies.len() {
            let mut path = FxIndexSet::default();
            let mut current = start;
            let target = loop {
                if let Some(target) = targets[current] {
                    break target;
                }
                let Type::RecursiveVar(reference) = bodies[current] else {
                    break current;
                };
                if !path.insert(current) {
                    return None;
                }
                debug_assert_eq!(reference.depth(db), 0);
                current = reference.index(db);
            };
            targets[current] = Some(target);
            for index in path {
                targets[index] = Some(target);
            }
        }
        let kept: Vec<_> = (0..bodies.len())
            .filter(|index| targets[*index] == Some(*index))
            .collect();
        let mut indices = vec![0; bodies.len()];
        for (new, old) in kept.iter().enumerate() {
            indices[*old] = new;
        }
        let indices: Vec<_> = targets
            .into_iter()
            .map(|target| indices[target.expect("every forwarding chain was resolved")])
            .collect();
        let mapping =
            TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Reindex(&indices)));
        let visitor = ApplyTypeMappingVisitor::new(env);
        *bodies = kept
            .into_iter()
            .map(|index| {
                bodies[index].apply_type_mapping_impl(
                    db,
                    &mapping,
                    TypeContext::default(),
                    &visitor,
                )
            })
            .collect();
        for root in roots {
            *root = indices[*root];
        }
        Some(())
    }

    /// Refine structural equivalence classes until no class splits. Equality uses
    /// complete labels; origins of inferred binders are absent. Each round splits a
    /// class or terminates, so a graph with N nodes needs at most N rounds.
    fn minimize(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        bodies: &mut Vec<Type<'db>>,
        roots: &mut [usize],
    ) {
        let mut classes = vec![0; bodies.len()];
        let mut class_count = 1;
        loop {
            let mapping =
                TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Reindex(&classes)));
            let visitor = ApplyTypeMappingVisitor::new(env);
            let signatures: Vec<_> = bodies
                .iter()
                .enumerate()
                .map(|(index, body)| {
                    (
                        classes[index],
                        Self::ordered_shape(
                            db,
                            body.apply_type_mapping_impl(
                                db,
                                &mapping,
                                TypeContext::default(),
                                &visitor,
                            ),
                        ),
                    )
                })
                .collect();
            let mut labels = signatures.clone();
            labels.sort_unstable_by_key(|(class, label)| {
                (*class, InternedType::new(db, *label).as_id())
            });
            labels.dedup();
            let lookup: FxHashMap<_, _> = labels
                .iter()
                .enumerate()
                .map(|(index, label)| (*label, index))
                .collect();
            classes = signatures
                .iter()
                .map(|signature| lookup[signature])
                .collect();
            if labels.len() == class_count {
                break;
            }
            class_count = labels.len();
        }
        let mapping =
            TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Reindex(&classes)));
        let visitor = ApplyTypeMappingVisitor::new(env);
        let mut representatives = vec![0; class_count];
        for (index, class) in classes.iter().enumerate() {
            representatives[*class] = index;
        }
        *bodies = representatives
            .into_iter()
            .map(|index| {
                Self::ordered_shape(
                    db,
                    bodies[index].apply_type_mapping_impl(
                        db,
                        &mapping,
                        TypeContext::default(),
                        &visitor,
                    ),
                )
            })
            .collect();
        for root in roots {
            *root = classes[*root];
        }
    }

    /// Use the interner's exact total order within this database. No type operation
    /// inspects these open shapes, and hash collisions cannot identify distinct labels.
    fn ordered_shape(db: &'db dyn Db, ty: Type<'db>) -> Type<'db> {
        match ty {
            Type::Union(union) => {
                let mut elements = union.elements(db).to_vec();
                elements.sort_unstable_by_key(|element| InternedType::new(db, *element).as_id());
                elements.dedup();
                match elements.as_slice() {
                    [element] => *element,
                    _ => Type::Union(UnionType::new(
                        db,
                        elements.into_boxed_slice(),
                        union.recursively_defined(db),
                    )),
                }
            }
            Type::Intersection(intersection) => {
                let mut positive: Vec<_> = intersection.positive(db).iter().copied().collect();
                positive.sort_unstable_by_key(|element| InternedType::new(db, *element).as_id());
                let mut negative: Vec<_> = intersection.negative(db).into_iter().copied().collect();
                negative.sort_unstable_by_key(|element| InternedType::new(db, *element).as_id());
                let mut negatives = NegativeIntersectionElements::default();
                for ty in negative {
                    negatives.insert(ty);
                }
                Type::Intersection(IntersectionType::new(
                    db,
                    positive.into_iter().collect::<FxOrderSet<_>>(),
                    negatives,
                ))
            }
            _ => ty,
        }
    }

    /// Iterative Kosaraju traversal, returning components after their dependencies.
    fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
        let mut reverse = vec![Vec::new(); edges.len()];
        for (source, targets) in edges.iter().enumerate() {
            for target in targets {
                reverse[*target].push(source);
            }
        }
        let mut visited = vec![false; edges.len()];
        let mut order = Vec::new();
        for start in 0..edges.len() {
            if std::mem::replace(&mut visited[start], true) {
                continue;
            }
            let mut pending = vec![(start, 0)];
            while let Some((current, next)) = pending.pop() {
                if let Some(dependent) = reverse[current].get(next) {
                    pending.push((current, next + 1));
                    if !std::mem::replace(&mut visited[*dependent], true) {
                        pending.push((*dependent, 0));
                    }
                } else {
                    order.push(current);
                }
            }
        }
        visited.fill(false);
        let mut components = Vec::new();
        for start in order.into_iter().rev() {
            if std::mem::replace(&mut visited[start], true) {
                continue;
            }
            let mut component = Vec::new();
            let mut pending = vec![start];
            while let Some(current) = pending.pop() {
                component.push(current);
                for dependency in &edges[current] {
                    if !std::mem::replace(&mut visited[*dependency], true) {
                        pending.push(*dependency);
                    }
                }
            }
            components.push(component);
        }
        components
    }
}
