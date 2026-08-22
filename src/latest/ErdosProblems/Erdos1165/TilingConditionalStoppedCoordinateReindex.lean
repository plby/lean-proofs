/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingConditionalStoppedCoordinateRefinement

/-!
# Atomwise reindexing of a conditional stopped-coordinate refinement

A typed stopped-coordinate factorization is naturally indexed by its typed
retained trace.  The low Proposition 4.9 family is instead indexed atomwise:
one joint history fixes a trace and exact canonical/opposite candidate sets,
and its candidate factor has a smaller piece and next event.

This file performs precisely that deterministic reindexing.  It uses only
the old datum's spatial fields and unscreened `base_factorization`.  The new
piece containment, cap monotonicity, and pathwise coverage remain explicit
set-theoretic fields.  The conditional product bound is again proved at cost
one from positivity and narrow containment.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingConditionalStoppedCoordinateReindex

open FiniteDominoProductLaw
open PathInsertion PreStoppingFiber SpatialInsertionFiber
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingConditionalStoppedCoordinateRefinement
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

/-- Refine the base predicate of an old typed-trace index after selecting a
possibly different atomwise index. -/
def conditionalReindexedPredicate
    {oldIndex newIndex : Type*}
    {oldPiece : oldIndex → Set WalkPath} {oldNext : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData oldPiece oldNext oldCost)
    (source : newIndex → oldIndex)
    (accepts : ∀ z cap, TruncatedTotals (data.upper (source z) cap) → Bool)
    (z : newIndex) (cap : ℕ)
    (q : TilingCappedCoordinates (data.retainedCount (source z) cap) cap) : Prop :=
  data.basePredicate (source z) cap q ∧
    TilingAwayTotalsScreen (data.tiling (source z) cap)
      (data.start (source z) cap) (data.retained (source z) cap)
      (data.distinguished (source z) cap) (data.upper (source z) cap)
      (fun ell ↦ accepts z cap ell = true)
      ((splitTilingCoordinatesEquiv (data.tiling (source z) cap)
        (data.start (source z) cap) (data.retained (source z) cap)
        (data.distinguished (source z) cap) q).2)

/-- Literal reconstruction form of an atomwise reindexed predicate. -/
theorem conditionalReindexedPredicate_iff_reconstructed
    {oldIndex newIndex : Type*}
    {oldPiece : oldIndex → Set WalkPath} {oldNext : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData oldPiece oldNext oldCost)
    (source : newIndex → oldIndex)
    (accepts : ∀ z cap, TruncatedTotals (data.upper (source z) cap) → Bool)
    (z : newIndex) (cap : ℕ)
    (q : TilingCappedCoordinates (data.retainedCount (source z) cap) cap)
    (hupper : ∀ b,
      tilingDominoTotal (data.tiling (source z) cap)
        (data.start (source z) cap) (data.retained (source z) cap)
        (fun j ↦ (q j : ℕ)) b.1 < data.upper (source z) cap b) :
    conditionalReindexedPredicate data source accepts z cap q ↔
      data.basePredicate (source z) cap q ∧
        accepts z cap
          (reconstructedTilingAwayTotalsOfCoordinates
            (data.tiling (source z) cap) (data.start (source z) cap)
            (data.retained (source z) cap)
            (data.distinguished (source z) cap)
            (data.upper (source z) cap) q hupper) = true := by
  unfold conditionalReindexedPredicate
  rw [tilingAwayTotalsScreen_split_iff_reconstructed]

/-- The atomwise factorization is inherited from the selected old typed
trace and strengthened only by the reconstructed away-total screen. -/
theorem conditionalReindexedPredicate_factorization
    {oldIndex newIndex : Type*}
    {oldPiece : oldIndex → Set WalkPath} {oldNext : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData oldPiece oldNext oldCost)
    (source : newIndex → oldIndex)
    (accepts : ∀ z cap, TruncatedTotals (data.upper (source z) cap) → Bool)
    (z : newIndex) (cap : ℕ)
    (q : TilingCappedCoordinates (data.retainedCount (source z) cap) cap) :
    conditionalReindexedPredicate data source accepts z cap q ∧
        TilingStoppingAccepted (data.stoppingTime (source z) cap)
          (data.tiling (source z) cap) (data.start (source z) cap)
          (data.retained (source z) cap) (fun j ↦ (q j : ℕ))
          (data.tail (source z) cap) ↔
      data.selected (source z) cap
          ((splitTilingCoordinatesEquiv (data.tiling (source z) cap)
            (data.start (source z) cap) (data.retained (source z) cap)
            (data.distinguished (source z) cap) q).1) ∧
        TilingAwayTotalsScreen (data.tiling (source z) cap)
          (data.start (source z) cap) (data.retained (source z) cap)
          (data.distinguished (source z) cap) (data.upper (source z) cap)
          (fun ell ↦ accepts z cap ell = true)
          ((splitTilingCoordinatesEquiv (data.tiling (source z) cap)
            (data.start (source z) cap) (data.retained (source z) cap)
            (data.distinguished (source z) cap) q).2) := by
  constructor
  · rintro ⟨⟨hbase, hscreen⟩, haccepted⟩
    have hold := (data.base_factorization (source z) cap q).1
      ⟨hbase, haccepted⟩
    exact ⟨hold.1, hscreen⟩
  · rintro ⟨hselected, hscreen⟩
    have htrue := tilingAwayTotalsScreen_true_of_screen hscreen
    have hold := (data.base_factorization (source z) cap q).2
      ⟨hselected, htrue⟩
    exact ⟨⟨hold.1, hscreen⟩, hold.2⟩

/-- Data needed to reindex an old typed stopped-coordinate skeleton onto
smaller atomwise carriers and install broad/narrow reconstructed acceptors. -/
structure TilingConditionalReindexedRefinementData
    {oldIndex newIndex : Type*}
    {oldPiece : oldIndex → Set WalkPath} {oldNext : Set WalkPath}
    {newPiece : newIndex → Set WalkPath} {newNext : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData oldPiece oldNext oldCost)
    (source : newIndex → oldIndex) where
  baseAccepts : ∀ z cap, TruncatedTotals (data.upper (source z) cap) → Bool
  screenedAccepts : ∀ z cap,
    TruncatedTotals (data.upper (source z) cap) → Bool
  screenedAccepts_subset_base : ∀ z cap ell,
    screenedAccepts z cap ell = true → baseAccepts z cap ell = true
  base_mass_pos : ∀ z cap,
    0 < screenMass
      (tilingAwayPointMass (cap := cap) (data.tiling (source z) cap)
        (data.start (source z) cap) (data.retained (source z) cap)
        (data.distinguished (source z) cap))
      (data.upper (source z) cap)
      (fun ell ↦ baseAccepts z cap ell = true)
  base_subset_piece : ∀ z cap,
    walkLift (tilingPreStoppingFiberEvent
      (data.stoppingTime (source z) cap) (data.tiling (source z) cap)
      (data.start (source z) cap) (data.retained (source z) cap) cap
      (data.tail (source z) cap)
      (conditionalReindexedPredicate data source baseAccepts z cap)) ⊆
        newPiece z
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (tilingPreStoppingFiberEvent
      (data.stoppingTime (source z) cap) (data.tiling (source z) cap)
      (data.start (source z) cap) (data.retained (source z) cap) cap
      (data.tail (source z) cap)
      (conditionalReindexedPredicate data source screenedAccepts z cap))
  transition_covered : ∀ z, newPiece z ∩ newNext ⊆ ⋃ cap,
    walkLift (tilingPreStoppingFiberEvent
      (data.stoppingTime (source z) cap) (data.tiling (source z) cap)
      (data.start (source z) cap) (data.retained (source z) cap) cap
      (data.tail (source z) cap)
      (conditionalReindexedPredicate data source screenedAccepts z cap))

/-- Construct a genuine atomwise conditional datum after reindexing an old
typed stopped-coordinate base factorization. -/
noncomputable def conditionalFactoredDataOfReindexedRefinement
    {oldIndex newIndex : Type*}
    {oldPiece : oldIndex → Set WalkPath} {oldNext : Set WalkPath}
    {newPiece : newIndex → Set WalkPath} {newNext : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData oldPiece oldNext oldCost)
    (source : newIndex → oldIndex)
    (refinement : TilingConditionalReindexedRefinementData
      (newPiece := newPiece) (newNext := newNext) data source) :
    TilingConditionalFactoredStoppedCoordinateData
      newPiece newNext (1 : ℝ≥0∞) where
  tiling := fun z ↦ data.tiling (source z)
  retainedCount := fun z ↦ data.retainedCount (source z)
  start := fun z ↦ data.start (source z)
  retained := fun z ↦ data.retained (source z)
  tail := fun z ↦ data.tail (source z)
  stoppingTime := fun z ↦ data.stoppingTime (source z)
  isStoppingTime := fun z ↦ data.isStoppingTime (source z)
  basePredicate :=
    conditionalReindexedPredicate data source refinement.baseAccepts
  screenedPredicate :=
    conditionalReindexedPredicate data source refinement.screenedAccepts
  screened_subset_base := by
    intro z cap q hq
    exact ⟨hq.1, tilingAwayTotalsScreen_mono
      (fun ell ↦ refinement.screenedAccepts_subset_base z cap ell) hq.2⟩
  base_subset_piece := refinement.base_subset_piece
  distinguished := fun z ↦ data.distinguished (source z)
  selected := fun z ↦ data.selected (source z)
  upper := fun z ↦ data.upper (source z)
  baseAccepts := refinement.baseAccepts
  screenedAccepts := refinement.screenedAccepts
  screenedAccepts_subset_base := refinement.screenedAccepts_subset_base
  base_factorization :=
    conditionalReindexedPredicate_factorization data source
      refinement.baseAccepts
  screened_factorization :=
    conditionalReindexedPredicate_factorization data source
      refinement.screenedAccepts
  upper_pos := fun z ↦ data.upper_pos (source z)
  base_mass_ne_zero := fun z cap ↦ ne_of_gt (refinement.base_mass_pos z cap)
  monotone_screened := refinement.monotone_screened
  transition_covered := refinement.transition_covered
  product_bound := by
    intro z cap
    simpa only [ENNReal.toReal_one] using
      conditionalScreenMass_le_one_of_subset
        (tilingAwayPointMass (cap := cap) (data.tiling (source z) cap)
          (data.start (source z) cap) (data.retained (source z) cap)
          (data.distinguished (source z) cap))
        (data.upper (source z) cap)
        (fun ell ↦ refinement.baseAccepts z cap ell = true)
        (fun ell ↦ refinement.screenedAccepts z cap ell = true)
        (fun b v ↦ tilingAwayExactTotalMass_nonneg
          (data.tiling (source z) cap) (data.start (source z) cap)
          (data.retained (source z) cap)
          (data.distinguished (source z) cap) b v)
        (refinement.screenedAccepts_subset_base z cap)
        (refinement.base_mass_pos z cap)

end

end Erdos1165.TilingConditionalStoppedCoordinateReindex
