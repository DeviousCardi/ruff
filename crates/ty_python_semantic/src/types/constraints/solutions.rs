use std::cell::RefCell;
use std::collections::VecDeque;
use std::marker::PhantomData;
use std::ops::ControlFlow;

use crate::types::constraints::paths::PathAssignments;
use crate::types::constraints::{
    ALWAYS_FALSE, ALWAYS_TRUE, ConstraintBoundsBuilder, ConstraintId, ConstraintSetStorage, NodeId,
    PathBounds, SolutionLimits, TypeVarSolution,
};
use crate::types::{
    BoundTypeVarInstance, GenericContext, Type, any_over_type_including_alias_arguments,
};
use crate::{Db, FxIndexMap, FxIndexSet, ProgramEnvironment};

impl<'db> TypeVarSolution<'db> {
    /// Substitute resolved bindings within one solution path, preserving correlations between paths.
    /// Bindings that depend on a cycle retain symbolic references for recursive solving.
    pub(super) fn resolve_dependencies(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        solution: &mut [Self],
    ) {
        let variables: FxIndexMap<_, _> = solution
            .iter()
            .enumerate()
            .map(|(index, binding)| (binding.bound_typevar.identity(db), index))
            .collect();
        let mut dependents = vec![Vec::new(); solution.len()];
        let mut unresolved = Vec::with_capacity(solution.len());
        for (index, binding) in solution.iter().enumerate() {
            let dependencies = RefCell::new(FxIndexSet::default());
            any_over_type_including_alias_arguments(db, env, binding.solution, |ty| {
                if let Type::TypeVar(typevar) = ty
                    && let Some(dependency) = variables.get(&typevar.identity(db))
                {
                    dependencies.borrow_mut().insert(*dependency);
                }
                false
            });
            let dependencies = dependencies.into_inner();
            unresolved.push(dependencies.len());
            for dependency in dependencies {
                dependents[dependency].push(index);
            }
        }

        let mut ready: VecDeque<_> = unresolved
            .iter()
            .enumerate()
            .filter_map(|(index, count)| (*count == 0).then_some(index))
            .collect();
        while let Some(index) = ready.pop_front() {
            if dependents[index].is_empty() {
                continue;
            }
            // Specialize stored alias arguments without expanding recursive alias bodies.
            let context =
                GenericContext::from_typevar_instances(db, env, [solution[index].bound_typevar]);
            let specialization = context.specialize(db, &[solution[index].solution]);
            for &dependent in &dependents[index] {
                solution[dependent].solution = solution[dependent]
                    .solution
                    .apply_specialization(db, specialization);
                unresolved[dependent] -= 1;
                if unresolved[dependent] == 0 {
                    ready.push_back(dependent);
                }
            }
        }
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

        PathBounds::Constrained(result.into_boxed_slice())
    }
}
