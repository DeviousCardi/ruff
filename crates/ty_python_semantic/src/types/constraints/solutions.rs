use std::cell::RefCell;
use std::collections::VecDeque;
use std::marker::PhantomData;
use std::ops::ControlFlow;

use crate::types::constraints::paths::PathAssignments;
use crate::types::constraints::{
    ALWAYS_FALSE, ALWAYS_TRUE, ConstraintBound, ConstraintBoundsBuilder, ConstraintId,
    ConstraintSetStorage, NodeId, PathBound, PathBounds, SolutionLimits, TypeVarSolution,
};
use crate::types::typevar::TypeVarSet;
use crate::types::{
    BoundTypeVarInstance, GenericContext, RecursiveType, Type, UnionType,
    any_over_type_including_alias_arguments,
};
use crate::{Db, FxIndexMap, FxIndexSet, ProgramEnvironment};

impl<'db> TypeVarSolution<'db> {
    /// Solve dependencies within one path, preserving correlations between paths.
    /// Acyclic bindings are substituted in dependency order. Remaining equations
    /// are eliminated once each, closing self-references with recursive binders.
    /// Returns whether any recursive binder was introduced.
    pub(super) fn resolve_dependencies(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        solution: &mut [Self],
        bounds: &[PathBound<'db>],
        inferable: TypeVarSet<'db>,
    ) -> bool {
        let graph = SolutionDependencies::new(db, env, solution);
        let mut unresolved: Vec<_> = graph.dependencies.iter().map(Vec::len).collect();
        let mut equations = vec![None; solution.len()];
        // Pin cyclic equations before substituting finite dependencies, while their
        // selected lower bounds can still be compared with the original upper bounds.
        // Keep these candidates separate until recursive closure succeeds.
        for component in graph.components(&unresolved) {
            if !graph.is_cyclic(&component)
                || component
                    .iter()
                    .any(|index| !solution[*index].bound_typevar.is_inferable(db, inferable))
            {
                continue;
            }
            for index in component {
                let binding = &solution[index];
                if let Some(bound) = bounds.iter().find(|bound| {
                    bound.bound_typevar.identity(db) == binding.bound_typevar.identity(db)
                }) {
                    let equation = bound.simplify_equation(db, env, binding.solution);
                    if equation != binding.solution {
                        equations[index] = Some(equation);
                    }
                }
            }
        }

        let mut ready: VecDeque<_> = unresolved
            .iter()
            .enumerate()
            .filter_map(|(index, count)| (*count == 0).then_some(index))
            .collect();
        while let Some(index) = ready.pop_front() {
            if graph.dependents[index].is_empty() {
                continue;
            }
            // Specialize stored alias arguments without expanding recursive alias bodies.
            let context =
                GenericContext::from_typevar_instances(db, env, [solution[index].bound_typevar]);
            let specialization = context.specialize(db, &[solution[index].solution]);
            for &dependent in &graph.dependents[index] {
                solution[dependent].solution = solution[dependent]
                    .solution
                    .apply_specialization(db, specialization);
                if let Some(equation) = &mut equations[dependent] {
                    *equation = equation.apply_specialization(db, specialization);
                }
                unresolved[dependent] -= 1;
                if unresolved[dependent] == 0 {
                    ready.push_back(dependent);
                }
            }
        }

        let mut recursive = false;
        for component in graph.components(&unresolved) {
            if component
                .iter()
                .any(|index| !solution[*index].bound_typevar.is_inferable(db, inferable))
            {
                continue;
            }
            let mut candidate: Vec<_> = component
                .iter()
                .map(|index| Self {
                    bound_typevar: solution[*index].bound_typevar,
                    solution: equations[*index].unwrap_or(solution[*index].solution),
                })
                .collect();
            let is_cycle = graph.is_cyclic(&component);
            let newly_recursive = is_cycle && Self::close_component(db, env, &mut candidate);
            if is_cycle && !newly_recursive {
                // Pure type-variable relationships retain their inference policy
                // and free parameters; they do not introduce a recursive type.
                continue;
            }
            recursive |= newly_recursive;
            let context = GenericContext::from_typevar_instances(
                db,
                env,
                candidate.iter().map(|binding| binding.bound_typevar),
            );
            let types: Vec<_> = candidate.iter().map(|binding| binding.solution).collect();
            let specialization = context.specialize(db, &types);
            for (index, binding) in component.iter().zip(candidate) {
                solution[*index] = binding;
                equations[*index] = None;
            }
            // All remaining components see this component's closed solutions.
            for (index, binding) in solution.iter_mut().enumerate() {
                if unresolved[index] != 0
                    && !component.contains(&index)
                    && binding.bound_typevar.is_inferable(db, inferable)
                {
                    binding.solution = binding.solution.apply_specialization(db, specialization);
                    if let Some(equation) = &mut equations[index] {
                        *equation = equation.apply_specialization(db, specialization);
                    }
                }
            }
        }
        recursive
    }

    /// Eliminate each equation once, closing self-references before substitution.
    /// Back-substitution into earlier equations preserves mutual references without
    /// an unbounded expansion loop. The caller publishes the component atomically.
    fn close_component(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        solution: &mut [Self],
    ) -> bool {
        let mut recursive = false;
        for index in 0..solution.len() {
            let variable = solution[index].bound_typevar;
            let equation = solution[index].without_self_constraint(db, env);
            let Some(resolved) = RecursiveType::from_equation(db, env, variable, equation) else {
                return false;
            };
            recursive |= resolved != equation && matches!(resolved, Type::Recursive(_));
            solution[index].solution = resolved;
            let context = GenericContext::from_typevar_instances(db, env, [variable]);
            let specialization = context.specialize(db, &[resolved]);
            for (dependent, binding) in solution.iter_mut().enumerate() {
                if dependent != index {
                    binding.solution = binding.solution.apply_specialization(db, specialization);
                }
            }
        }
        recursive
    }

    /// Drop the tautological part of `T >= T | F(T)`.
    /// References inside constructors remain, and an identity equation stays free.
    fn without_self_constraint(&self, db: &'db dyn Db, env: &ProgramEnvironment<'db>) -> Type<'db> {
        self.normalize_equation(db, env, self.solution, &mut FxIndexSet::default())
    }

    /// Aliases and recursive binders are transparent at the root of an equation.
    /// Unfold them before removing tautologies, but never expand below a constructor.
    fn normalize_equation(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        ty: Type<'db>,
        active: &mut FxIndexSet<Type<'db>>,
    ) -> Type<'db> {
        if !active.insert(ty) {
            return ty;
        }
        let is_self = |ty: Type<'db>| matches!(ty, Type::TypeVar(variable) if variable.identity(db) == self.bound_typevar.identity(db));
        let result = match ty {
            Type::TypeAlias(alias) => {
                self.normalize_equation(db, env, alias.value_type(db), active)
            }
            Type::Recursive(recursive) => recursive.map_type(db, env, |unfolded| {
                self.normalize_equation(db, env, unfolded, active)
            }),
            Type::Union(union) => UnionType::from_elements(
                db,
                env,
                union
                    .elements(db)
                    .iter()
                    .copied()
                    .map(|ty| self.normalize_equation(db, env, ty, active))
                    .filter(|ty| !is_self(*ty)),
            ),
            _ => ty,
        };
        active.swap_remove(&ty);
        result
    }
}

impl<'db> PathBound<'db> {
    /// Prefer a pinned equality to a union of its consequences before elimination.
    /// The original bounds remain available for validating the simultaneous solution.
    fn simplify_equation(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        selected: Type<'db>,
    ) -> Type<'db> {
        let Type::Union(lower) = selected else {
            return selected;
        };
        if selected != self.effective_lower(db, env) || !selected.is_fully_static(db, env) {
            return selected;
        }
        // If A is both a lower-bound element and an upper bound, A <= T <= A.
        self.upper
            .iter_clauses()
            .map(ConstraintBound::ty)
            .find(|upper| lower.elements(db).contains(upper))
            .unwrap_or(selected)
    }
}

/// Edges between the selected bindings in a single solution path.
struct SolutionDependencies {
    dependencies: Vec<Vec<usize>>,
    dependents: Vec<Vec<usize>>,
}

impl SolutionDependencies {
    /// Record dependencies in the selected solution types, including alias arguments.
    fn new<'db>(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        solution: &[TypeVarSolution<'db>],
    ) -> Self {
        let variables: FxIndexMap<_, _> = solution
            .iter()
            .enumerate()
            .map(|(index, binding)| (binding.bound_typevar.identity(db), index))
            .collect();
        let mut dependents = vec![Vec::new(); solution.len()];
        let mut dependencies = Vec::with_capacity(solution.len());
        for (index, binding) in solution.iter().enumerate() {
            let found = RefCell::new(FxIndexSet::default());
            any_over_type_including_alias_arguments(db, env, binding.solution, |ty| {
                if let Type::TypeVar(typevar) = ty
                    && let Some(dependency) = variables.get(&typevar.identity(db))
                {
                    found.borrow_mut().insert(*dependency);
                }
                false
            });
            let found = found.into_inner();
            for &dependency in &found {
                dependents[dependency].push(index);
            }
            dependencies.push(found.into_iter().collect());
        }

        Self {
            dependencies,
            dependents,
        }
    }

    /// Whether a component contains a dependency cycle, including a self-reference.
    fn is_cyclic(&self, component: &[usize]) -> bool {
        component.len() > 1 || self.dependencies[component[0]].contains(&component[0])
    }

    /// Find strongly connected components in dependency order. The two iterative
    /// depth-first walks take linear time and do not consume the Rust call stack.
    fn components(&self, unresolved: &[usize]) -> Vec<Vec<usize>> {
        let mut visited: Vec<_> = unresolved.iter().map(|count| *count == 0).collect();
        let mut order = Vec::new();
        for start in 0..visited.len() {
            if std::mem::replace(&mut visited[start], true) {
                continue;
            }
            let mut pending = vec![(start, 0)];
            while let Some((current, next)) = pending.pop() {
                if let Some(&dependent) = self.dependents[current].get(next) {
                    pending.push((current, next + 1));
                    if !std::mem::replace(&mut visited[dependent], true) {
                        pending.push((dependent, 0));
                    }
                } else {
                    order.push(current);
                }
            }
        }
        let mut assigned: Vec<_> = unresolved.iter().map(|count| *count == 0).collect();
        let mut components = Vec::new();
        for start in order.into_iter().rev() {
            if std::mem::replace(&mut assigned[start], true) {
                continue;
            }
            let mut component = Vec::new();
            let mut pending = vec![start];
            while let Some(current) = pending.pop() {
                component.push(current);
                for &dependency in &self.dependencies[current] {
                    if !std::mem::replace(&mut assigned[dependency], true) {
                        pending.push(dependency);
                    }
                }
            }
            component.sort_unstable();
            components.push(component);
        }
        components
    }
}

pub(super) struct SolutionWalker<'db> {
    source_orders: FxIndexSet<ConstraintId>,
    sorted_paths: Vec<Vec<(ConstraintId, usize)>>,
    _phantom: PhantomData<&'db ()>,
}

impl<'db> SolutionWalker<'db> {
    pub(super) fn new(source_orders: FxIndexSet<ConstraintId>) -> Self {
        Self {
            source_orders,
            sorted_paths: Vec::default(),
            _phantom: PhantomData,
        }
    }

    pub(super) fn visit_node<L: SolutionLimits>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        node: NodeId,
        limits: &mut L,
    ) -> ControlFlow<L::Break> {
        limits.visit_node()?;
        if node == ALWAYS_FALSE {
            return ControlFlow::Continue(());
        }

        // If the current node is ALWAYS_TRUE, we can immediately report the current solution.
        if node == ALWAYS_TRUE {
            limits.satisfied_path()?;
            self.found_satisfied_path(path);
            return ControlFlow::Continue(());
        }

        // At this point we actually have to walk the outgoing edges of this node.
        let interior = storage.interior_node_data(node);
        let constraint = interior.constraint;
        for (assignment, child) in [
            (constraint.when_true(), interior.if_true),
            (constraint.when_unconstrained(), interior.if_uncertain),
            (constraint.when_false(), interior.if_false),
        ] {
            path.walk_edge(
                db,
                env,
                storage,
                assignment,
                |storage, path, _new_range, found_conflict| {
                    if !found_conflict {
                        self.visit_node(db, env, storage, path, child, limits)?;
                    }
                    ControlFlow::Continue(())
                },
            )?;
        }
        ControlFlow::Continue(())
    }

    fn found_satisfied_path(&mut self, path: &PathAssignments) {
        let mut path: Vec<_> = path
            .positive_constraints()
            .map(|(constraint, source_constraint)| {
                let source_order = self
                    .source_orders
                    .get_index_of(&source_constraint)
                    .expect("every TDD constraint should have a source order");
                (constraint, source_order)
            })
            .collect();
        // Sort the constraints in each path by their `source_order`s, to ensure that we construct
        // any unions or intersections in our type mappings in a stable order. Constraints might
        // come out of `PathAssignments` with identical `source_order`s, but if they do, those
        // "tied" constraints will still be ordered in a stable way. So we need a stable sort to
        // retain that stable per-tie ordering.
        path.sort_by_key(|(_, source_order)| *source_order);
        self.sorted_paths.push(path);
    }

    pub(super) fn finish(
        mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        inferable: TypeVarSet<'db>,
    ) -> PathBounds<'db> {
        if self.sorted_paths.is_empty() {
            return PathBounds::Unsatisfiable;
        }

        self.sorted_paths.sort_by(|path1, path2| {
            let source_orders1 = path1.iter().map(|(_, source_order)| *source_order);
            let source_orders2 = path2.iter().map(|(_, source_order)| *source_order);
            source_orders1.cmp(source_orders2)
        });

        let mut result = Vec::with_capacity(self.sorted_paths.len());
        let mut mappings: FxIndexMap<BoundTypeVarInstance<'db>, ConstraintBoundsBuilder<'db>> =
            FxIndexMap::default();

        for path in self.sorted_paths {
            mappings.clear();
            for (constraint, _) in path {
                let constraint = storage.constraint_data(constraint);
                let typevar = constraint.typevar;
                if let Some(lower) = constraint.stored_lower_bound() {
                    let bounds = mappings.entry(typevar).or_default();
                    bounds.add_lower(db, env, lower);

                    if let Type::TypeVar(lower_bound_typevar) = lower.ty() {
                        let bounds = mappings.entry(lower_bound_typevar).or_default();
                        bounds.add_upper(db, env, lower.with_type(Type::TypeVar(typevar)));
                    }
                }

                if let Some(upper) = constraint.stored_upper_bound() {
                    let bounds = mappings.entry(typevar).or_default();
                    bounds.add_upper(db, env, upper);

                    if let Type::TypeVar(upper_bound_typevar) = upper.ty() {
                        let bounds = mappings.entry(upper_bound_typevar).or_default();
                        bounds.add_lower(db, env, upper.with_type(Type::TypeVar(typevar)));
                    }
                }
            }

            let path_bounds = mappings
                .drain(..)
                .map(|(bound_typevar, bounds)| bounds.finish(db, env, bound_typevar))
                .collect();
            result.push(path_bounds);
        }

        PathBounds::Constrained(result.into_boxed_slice(), inferable)
    }
}
