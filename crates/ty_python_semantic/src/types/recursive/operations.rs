//! Deferred operations on closed inference references.

use super::RecursiveType;
use crate::types::{PromotionKind, PromotionMode, Type, TypeContext, TypeMapping};
use crate::{Db, ProgramEnvironment};

/// Operations apply to the referenced type in order, without changing its defining query.
#[salsa::interned(debug, heap_size=ruff_memory_usage::heap_size)]
pub struct RecursiveOperations<'db> {
    #[returns(ref)]
    steps: Box<[RecursiveOperation]>,
}

impl get_size2::GetSize for RecursiveOperations<'_> {}

/// A deferred operation with the same parameters as its immediate type mapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, get_size2::GetSize)]
pub enum RecursiveOperation {
    Promote(PromotionMode, PromotionKind),
}

impl<'db> RecursiveOperations<'db> {
    /// Apply each step, deferring it again when the body contains query references.
    pub(super) fn apply(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        mut ty: Type<'db>,
    ) -> Type<'db> {
        for step in self.steps(db) {
            let RecursiveOperation::Promote(mode, kind) = *step;
            ty = ty.apply_type_mapping(
                db,
                env,
                &TypeMapping::Promote(mode, kind),
                TypeContext::default(),
            );
        }
        ty
    }
}

impl<'db> RecursiveType<'db> {
    /// Defer promotion while retaining the input query and all earlier operations.
    pub(super) fn with_promotion(
        self,
        db: &'db dyn Db,
        mode: PromotionMode,
        kind: PromotionKind,
    ) -> Self {
        let step = RecursiveOperation::Promote(mode, kind);
        let mut steps = self
            .operations(db)
            .map_or_else(Vec::new, |operations| operations.steps(db).to_vec());
        // Idempotence only removes adjacent equal promotions; intervening operations
        // can introduce new literals or change which children are promoted.
        if steps.last() == Some(&step) {
            return self;
        }
        steps.push(step);
        Self::new_internal(
            db,
            self.origin(db),
            self.graph(db),
            self.entry(db),
            self.arguments(db),
            self.materialization_kind(db),
            Some(RecursiveOperations::new(db, steps.into_boxed_slice())),
        )
    }
}
