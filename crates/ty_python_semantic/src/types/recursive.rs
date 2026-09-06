//! Binding and capture-avoiding substitution for structural recursive types.
//!
//! `RecursiveVar` is syntax, with no standalone type semantics. Only structural
//! substitutions may inspect an open body. Ordinary type operations receive its
//! closed unfolding, including during intermediate normalization steps.

use std::cell::{Cell, RefCell};

use rustc_hash::FxHashSet;
use ty_python_core::definition::Definition;
use ty_python_core::place_table;

use super::generics::{ApplySpecialization, Specialization, walk_specialization_types};
use super::variance::{VarianceInferable, VarianceOrigin};
use super::visitor::{TypeKind, TypeVisitor, walk_non_atomic_type};
use super::{
    ApplyTypeMappingVisitor, BindingContext, BoundTypeVarIdentity, BoundTypeVarInstance,
    GenericContext, MaterializationKind, Type, TypeAliasType, TypeContext, TypeMapping,
    VarianceTerm,
};
use crate::{Db, ProgramEnvironment};

/// A recursive variable, indexed by the number of intervening recursive binders.
/// Zero refers to the nearest binder. An escaping reference has no type semantics;
/// in particular, it is neither a gradual type nor an assignability operand.
/// Only binding and substitution operations may construct recursive variables.
#[salsa::interned(debug, constructor=new_internal, heap_size=ruff_memory_usage::heap_size)]
pub struct RecursiveVar<'db> {
    /// Zero-based de Bruijn index: the number of recursive binders between this
    /// occurrence and its binder. In `μa. μb. tuple[a, b]`, `a` has index 1 and
    /// `b` has index 0. This is relative to the occurrence, not the root of the type.
    #[returns(copy)]
    depth: u32,
    #[returns(copy)]
    arguments: Option<Specialization<'db>>,
}

impl get_size2::GetSize for RecursiveVar<'_> {}

impl<'db> RecursiveVar<'db> {
    /// Unfold references whose index equals the number of nested binders entered
    /// by the visitor. Smaller indices belong to inner binders and stay unchanged.
    /// Larger indices escape the closed input; binding also rejects equal indices,
    /// since its input cannot already refer to the binder being introduced.
    pub(super) fn apply_type_mapping(
        self,
        db: &'db dyn Db,
        mapping: &TypeMapping<'_, 'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> Type<'db> {
        let TypeMapping::Recursive(_) = mapping else {
            unreachable!("semantic operation on an unbound recursive variable");
        };
        let arguments = self
            .arguments(db)
            .map(|arguments| arguments.apply_type_mapping_impl(db, mapping, &[], visitor));
        match mapping {
            TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Unfold(recursive)))
                if self.depth(db) == visitor.recursive_depth =>
            {
                Type::Recursive(recursive.with_arguments(db, arguments))
            }
            TypeMapping::Recursive(_) if self.depth(db) < visitor.recursive_depth => {
                Type::RecursiveVar(Self::new_internal(db, self.depth(db), arguments))
            }
            _ => unreachable!("semantic operation on an unbound recursive variable"),
        }
    }
}

/// A structural substitution that only the recursive-type binder can construct.
#[derive(Debug, Clone, Copy, PartialEq, Eq, get_size2::GetSize)]
pub struct RecursiveMapping<'db>(RecursiveSubstitution<'db>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, get_size2::GetSize)]
enum RecursiveSubstitution<'db> {
    Unfold(RecursiveType<'db>),
    Bind(RecursiveType<'db>),
    BindTypeVar(BoundTypeVarInstance<'db>),
}

impl<'db> RecursiveMapping<'db> {
    /// Bind a free inference variable at the current de Bruijn depth. The caller
    /// closes the resulting body before any semantic operation can inspect it.
    pub(super) fn apply_typevar(
        self,
        db: &'db dyn Db,
        typevar: BoundTypeVarInstance<'db>,
        depth: u32,
    ) -> Type<'db> {
        match self.0 {
            RecursiveSubstitution::BindTypeVar(variable)
                if variable.identity(db) == typevar.identity(db) =>
            {
                Type::RecursiveVar(RecursiveVar::new_internal(db, depth, None))
            }
            _ => Type::TypeVar(typevar),
        }
    }
}

/// The alias query or inference variable that introduced a recursive binder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, salsa::SalsaValue)]
pub enum RecursiveOrigin<'db> {
    Alias {
        definition: Definition<'db>,
        cycle: salsa::Id,
    },
    Inferred(BoundTypeVarInstance<'db>),
}

impl get_size2::GetSize for RecursiveOrigin<'_> {}

/// A recursive type whose raw body is private. Unfolding substitutes closed types
/// for references before exposing the body to ordinary type operations.
/// Use the binding operations in this module to construct recursive types.
#[salsa::interned(debug, constructor=new_internal, heap_size=ruff_memory_usage::heap_size)]
pub struct RecursiveType<'db> {
    #[returns(copy)]
    origin: RecursiveOrigin<'db>,
    #[returns(copy)]
    body: Type<'db>,
    /// The arguments of a closed application of this recursive constructor.
    #[returns(copy)]
    pub(super) arguments: Option<Specialization<'db>>,
    /// The lazy materialization applied to this recursive alias, if any.
    #[returns(copy)]
    pub(super) materialization_kind: Option<MaterializationKind>,
}

impl get_size2::GetSize for RecursiveType<'_> {}

impl<'db> RecursiveType<'db> {
    /// Seed a query cycle with `μa. a`: index 0 refers to the binder created here.
    pub(super) fn initial(
        db: &'db dyn Db,
        definition: Definition<'db>,
        cycle: salsa::Id,
        parameters: Option<GenericContext<'db>>,
    ) -> Type<'db> {
        let arguments = parameters.map(|parameters| parameters.identity_specialization(db));
        Type::Recursive(Self::new_internal(
            db,
            RecursiveOrigin::Alias { definition, cycle },
            Type::RecursiveVar(RecursiveVar::new_internal(db, 0, arguments)),
            arguments,
            None,
        ))
    }

    /// Close the equation `variable = result` by binding occurrences of `variable`.
    /// Identity equations remain free; noncontractive bodies cannot define a
    /// structural recursive type and are left for the constraint solver to resolve.
    pub(super) fn from_equation(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        variable: BoundTypeVarInstance<'db>,
        result: Type<'db>,
    ) -> Option<Type<'db>> {
        if result == Type::TypeVar(variable) {
            return Some(result);
        }
        result.assert_no_unbound_recursive_vars(db, env);
        let body = result.apply_type_mapping_impl(
            db,
            &TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::BindTypeVar(
                variable,
            ))),
            TypeContext::default(),
            &ApplyTypeMappingVisitor::new(env),
        );
        if Self::has_unguarded_reference(db, body) {
            return None;
        }
        let result = if RecursiveReferences::contains_escaping(db, env, body) {
            Type::Recursive(Self::new_internal(
                db,
                RecursiveOrigin::Inferred(variable),
                body,
                None,
                None,
            ))
        } else {
            body
        };
        result.assert_no_unbound_recursive_vars(db, env);
        Some(result)
    }

    /// Close recursive occurrences after inferring an alias's constructor expression.
    pub(super) fn recover(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        previous: Type<'db>,
        result: Type<'db>,
    ) -> Type<'db> {
        let Type::Recursive(previous) = previous else {
            return result;
        };
        previous.bind(db, env, result)
    }

    /// Bind occurrences of this recursive constructor in a closed result.
    /// An occurrence under `d` existing binders becomes index `d` of the new outer binder.
    fn bind(self, db: &'db dyn Db, env: &ProgramEnvironment<'db>, result: Type<'db>) -> Type<'db> {
        result.assert_no_unbound_recursive_vars(db, env);
        let body = result.apply_type_mapping_impl(
            db,
            &TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Bind(self))),
            TypeContext::default(),
            &ApplyTypeMappingVisitor::new(env),
        );
        let result = self.build(db, env, body);
        result.assert_no_unbound_recursive_vars(db, env);
        result
    }

    fn build(self, db: &'db dyn Db, env: &ProgramEnvironment<'db>, body: Type<'db>) -> Type<'db> {
        if Self::has_unguarded_reference(db, body)
            && let RecursiveOrigin::Alias { cycle, .. } = self.origin(db)
        {
            return Type::divergent(cycle);
        }
        if !RecursiveReferences::contains_escaping(db, env, body) {
            return body;
        }
        Type::Recursive(Self::new_internal(
            db,
            self.origin(db),
            body,
            self.arguments(db),
            None,
        ))
    }

    /// Check a raw body for self-references reachable through Boolean type operations alone.
    /// No nested binders are entered, so index 0 always denotes the body's own binder.
    fn has_unguarded_reference(db: &'db dyn Db, body: Type<'db>) -> bool {
        match body {
            Type::RecursiveVar(reference) => reference.depth(db) == 0,
            Type::Union(union) => union
                .elements(db)
                .iter()
                .any(|element| Self::has_unguarded_reference(db, *element)),
            Type::Intersection(intersection) => intersection
                .positive(db)
                .iter()
                .chain(intersection.negative(db))
                .any(|element| Self::has_unguarded_reference(db, *element)),
            _ => false,
        }
    }

    fn with_arguments(self, db: &'db dyn Db, arguments: Option<Specialization<'db>>) -> Self {
        Self::new_internal(
            db,
            self.origin(db),
            self.body(db),
            arguments,
            self.materialization_kind(db),
        )
    }

    fn with_materialization(
        self,
        db: &'db dyn Db,
        materialization: Option<MaterializationKind>,
    ) -> Self {
        Self::new_internal(
            db,
            self.origin(db),
            self.body(db),
            self.arguments(db),
            materialization,
        )
    }

    /// Parameters bound by this recursive type constructor.
    pub(super) fn parameters(self, db: &'db dyn Db) -> Option<GenericContext<'db>> {
        self.arguments(db)
            .map(|arguments| arguments.generic_context(db))
    }

    /// The source alias's definition and name, if this binder comes from an alias.
    pub(super) fn alias(self, db: &'db dyn Db) -> Option<(Definition<'db>, &'db str)> {
        let RecursiveOrigin::Alias { definition, .. } = self.origin(db) else {
            return None;
        };
        let name = place_table(db, definition.scope(db))
            .symbol(definition.place(db).expect_symbol())
            .name();
        Some((definition, name))
    }

    /// Restore the formal arguments for analysis of the recursive constructor.
    pub(super) fn constructor(self, db: &'db dyn Db) -> Self {
        self.with_arguments(
            db,
            self.parameters(db)
                .map(|parameters| parameters.identity_specialization(db)),
        )
    }

    /// The program in which the recursive type's body was constructed.
    pub fn environment(self, db: &'db dyn Db) -> ProgramEnvironment<'db> {
        match self.origin(db) {
            RecursiveOrigin::Alias { definition, .. } => {
                ProgramEnvironment::from_definition(definition)
            }
            RecursiveOrigin::Inferred(variable) => match variable.binding_context(db) {
                BindingContext::Definition(definition) => {
                    ProgramEnvironment::from_definition(definition)
                }
                BindingContext::Synthetic(program) => ProgramEnvironment::from_program(program),
            },
        }
    }

    /// Substitute closed types for references before exposing the body.
    /// The traversal starts at depth 0 inside this binder; only nested recursive
    /// bodies increase the depth used to identify references to this binder.
    pub fn unfold(self, db: &'db dyn Db, env: &ProgramEnvironment<'db>) -> Type<'db> {
        Type::Recursive(self).assert_no_unbound_recursive_vars(db, env);
        let unfolded = self.body(db).apply_type_mapping_impl(
            db,
            &TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Unfold(self))),
            TypeContext::default(),
            &ApplyTypeMappingVisitor::new(env),
        );
        unfolded.assert_no_unbound_recursive_vars(db, env);
        let unfolded = match self.arguments(db) {
            Some(arguments) => unfolded.apply_type_mapping(
                db,
                env,
                &TypeMapping::ApplySpecialization(ApplySpecialization::TypeAlias(arguments)),
                TypeContext::default(),
            ),
            None => unfolded,
        };
        if self.materialization_kind(db).is_some() && !self.may_have_unbounded_specialization(db) {
            materialized_unfold(db, self)
        } else {
            match self.materialization_kind(db) {
                Some(kind) => unfolded.apply_type_mapping(
                    db,
                    env,
                    &TypeMapping::Materialize(kind),
                    TypeContext::default(),
                ),
                None => unfolded,
            }
        }
    }

    /// Structural binding replaces matching constructors with a reference whose index
    /// equals the visitor's depth. Other recursive bodies add one binder to that depth;
    /// their application arguments use the original depth, outside their own binder.
    pub(super) fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> Type<'db> {
        match mapping {
            TypeMapping::Recursive(RecursiveMapping(RecursiveSubstitution::Bind(target)))
                if self.origin(db) == target.origin(db)
                    && self.body(db) == target.body(db)
                    && self.materialization_kind(db) == target.materialization_kind(db) =>
            {
                let arguments = self
                    .arguments(db)
                    .map(|arguments| arguments.apply_type_mapping_impl(db, mapping, &[], visitor));
                Type::RecursiveVar(RecursiveVar::new_internal(
                    db,
                    visitor.recursive_depth,
                    arguments,
                ))
            }
            TypeMapping::Recursive(_) => {
                let nested = visitor.with_recursive_binder();
                let body = self
                    .body(db)
                    .apply_type_mapping_impl(db, mapping, tcx, &nested);
                let arguments = self
                    .arguments(db)
                    .map(|arguments| arguments.apply_type_mapping_impl(db, mapping, &[], visitor));
                Type::Recursive(Self::new_internal(
                    db,
                    self.origin(db),
                    body,
                    arguments,
                    self.materialization_kind(db),
                ))
            }
            TypeMapping::ApplySpecialization(_)
            | TypeMapping::ApplySpecializationWithMaterialization { .. }
                if self.arguments(db).is_some() =>
            {
                let arguments = self
                    .arguments(db)
                    .map(|arguments| arguments.apply_type_mapping_impl(db, mapping, &[], visitor));
                Type::Recursive(self.with_arguments(db, arguments))
            }
            TypeMapping::Materialize(kind) => {
                Type::Recursive(if self.materialization_kind(db).is_some() {
                    self
                } else {
                    self.with_materialization(db, Some(*kind))
                })
            }
            _ => visitor.visit(db, Type::Recursive(self), mapping, || {
                self.map_type(db, visitor.env, |unfolded| {
                    let mapped = unfolded.apply_type_mapping_impl(db, mapping, tcx, visitor);
                    self.bind(db, visitor.env, mapped)
                })
            }),
        }
    }

    pub(in crate::types) fn variance_equation(
        self,
        db: &'db dyn Db,
        typevar: BoundTypeVarIdentity<'db>,
    ) -> VarianceTerm<'db> {
        let env = self.environment(db);
        self.map_or(db, &env, VarianceTerm::BIVARIANT, |unfolded| {
            unfolded.variance_of(db, &env, typevar)
        })
    }

    pub(crate) fn map_type(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        operation: impl FnOnce(Type<'db>) -> Type<'db>,
    ) -> Type<'db> {
        self.map_or_else(db, env, || Type::Recursive(self), operation)
    }

    pub(crate) fn map_or_else<F>(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        fallback: impl FnOnce() -> F,
        operation: impl FnOnce(Type<'db>) -> F,
    ) -> F {
        self.map_if_unfolded(db, env, operation)
            .unwrap_or_else(fallback)
    }

    pub(crate) fn map_or<F>(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        fallback: F,
        operation: impl FnOnce(Type<'db>) -> F,
    ) -> F {
        self.map_if_unfolded(db, env, operation).unwrap_or(fallback)
    }

    fn map_if_unfolded<F>(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        operation: impl FnOnce(Type<'db>) -> F,
    ) -> Option<F> {
        let unfolded = self.unfold(db, env);
        if unfolded == Type::Recursive(self) {
            None
        } else {
            Some(operation(unfolded))
        }
    }
}

/// Materialize an unfolding lazily, keeping the marked binder as the recursive fallback.
///
/// Comparing a recursive specialization with its materialization can request this same unfolding
/// before it has finished materializing. Returning the marked binder closes that cycle while
/// preserving the requested materialization polarity.
#[salsa::tracked(
    returns(copy),
    cycle_initial=|_, _, recursive: RecursiveType<'db>| Type::Recursive(recursive),
    heap_size=ruff_memory_usage::heap_size
)]
fn materialized_unfold<'db>(db: &'db dyn Db, recursive: RecursiveType<'db>) -> Type<'db> {
    let Some(kind) = recursive.materialization_kind(db) else {
        debug_assert!(
            false,
            "materialized unfolding requires a materialization kind"
        );
        return Type::Recursive(recursive);
    };
    let env = recursive.environment(db);
    let unfolded = recursive.with_materialization(db, None).unfold(db, &env);
    unfolded.apply_type_mapping(
        db,
        &env,
        &TypeMapping::Materialize(kind),
        TypeContext::default(),
    )
}

impl<'db> VarianceInferable<'db> for RecursiveType<'db> {
    fn variance_of(
        self,
        db: &'db dyn Db,
        _env: &ProgramEnvironment<'db>,
        typevar: BoundTypeVarIdentity<'db>,
    ) -> VarianceTerm<'db> {
        VarianceTerm::variable(db, VarianceOrigin::Recursive(self), typevar)
    }
}

/// A syntactic walk that counts binders without unfolding or normalizing types.
struct RecursiveReferences<'env, 'db> {
    env: &'env ProgramEnvironment<'db>,
    /// Number of surrounding recursive binders entered from the inspected root.
    /// A variable is bound within that root exactly when its de Bruijn index is
    /// smaller than this count.
    depth: Cell<u32>,
    found: Cell<bool>,
    /// The same interned subtree can be bound at one depth and escaping at another.
    seen: RefCell<FxHashSet<(Type<'db>, u32)>>,
}

impl<'env, 'db> RecursiveReferences<'env, 'db> {
    /// Inspect a type without assuming any binders outside it. A raw body can have
    /// escaping references even when its enclosing `RecursiveType` is closed.
    fn contains_escaping(
        db: &'db dyn Db,
        env: &'env ProgramEnvironment<'db>,
        ty: Type<'db>,
    ) -> bool {
        let visitor = Self {
            env,
            depth: Cell::new(0),
            found: Cell::new(false),
            seen: RefCell::default(),
        };
        visitor.visit_type(db, ty);
        visitor.found.get()
    }
}

impl<'db> TypeVisitor<'db> for RecursiveReferences<'_, 'db> {
    fn program_environment(&self) -> &ProgramEnvironment<'db> {
        self.env
    }
    fn should_visit_lazy_type_attributes(&self) -> bool {
        false
    }
    /// At depth `d`, only indices below `d` have a binder within the inspected root.
    /// Revisit shared subtrees when the depth changes, since their binding can change.
    fn visit_type(&self, db: &'db dyn Db, ty: Type<'db>) {
        if self.found.get() {
            return;
        }
        if let Type::RecursiveVar(reference) = ty {
            if reference.depth(db) >= self.depth.get() {
                self.found.set(true);
            }
            if let Some(arguments) = reference.arguments(db) {
                walk_specialization_types(db, arguments, self);
            }
        } else if self.seen.borrow_mut().insert((ty, self.depth.get()))
            && let TypeKind::NonAtomic(node) = TypeKind::from(ty)
        {
            walk_non_atomic_type(db, node, self);
        }
    }
    /// Count this binder only inside its body. Application arguments remain in the
    /// surrounding scope, and the original depth is restored before visiting siblings.
    fn visit_recursive_type(&self, db: &'db dyn Db, recursive: RecursiveType<'db>) {
        if let Some(arguments) = recursive.arguments(db) {
            walk_specialization_types(db, arguments, self);
        }
        let depth = self.depth.get();
        self.depth.set(depth + 1);
        self.visit_type(db, recursive.body(db));
        self.depth.set(depth);
    }
    fn visit_type_alias_type(&self, db: &'db dyn Db, alias: TypeAliasType<'db>) {
        if let Some(specialization) = alias.specialization(db) {
            walk_specialization_types(db, specialization, self);
        }
    }
}

impl<'db> Type<'db> {
    pub(super) fn assert_no_unbound_recursive_vars(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) {
        debug_assert!(
            !RecursiveReferences::contains_escaping(db, env, self),
            "semantic operation on an unbound recursive variable"
        );
    }
}
