/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingConditionalCappedMarginalization

/-!
# Refining an unconditional stopped-coordinate factorization

This file turns an ordinary `TilingFactoredStoppedCoordinateData` fiber into
the semantic cost-one skeleton required by the conditional Proposition 4.9
argument.  The old base predicate fixes the retained stopped history.  The
new base predicate additionally fixes a broad predicate on the reconstructed
away-domino totals, while the new screened predicate uses a narrower
predicate on the same reconstructed vector.

The construction is deterministic.  In particular, the two new
factorizations are derived from the old `base_factorization` and the literal
away-total reconstruction; no transition probability estimate is assumed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingConditionalStoppedCoordinateRefinement

open FiniteDominoProductLaw
open PathInsertion PreStoppingFiber SpatialInsertionFiber
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Strengthen an old stopped-history predicate by a predicate on the exact
reconstructed vector of away-domino insertion totals. -/
def conditionalRefinedPredicate
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData piece next oldCost)
    (accepts : ∀ z cap, TruncatedTotals (data.upper z cap) → Bool)
    (z : index) (cap : ℕ)
    (q : TilingCappedCoordinates (data.retainedCount z cap) cap) : Prop :=
  data.basePredicate z cap q ∧
    TilingAwayTotalsScreen (data.tiling z cap) (data.start z cap)
      (data.retained z cap) (data.distinguished z cap) (data.upper z cap)
      (fun ell ↦ accepts z cap ell = true)
      ((splitTilingCoordinatesEquiv (data.tiling z cap) (data.start z cap)
        (data.retained z cap) (data.distinguished z cap) q).2)

/-- Monotonicity of an away-total screen in its predicate. -/
theorem tilingAwayTotalsScreen_mono
    {i cap : ℕ} {t : DominoTiling} {x : Point}
    {r : TilingRetainedWord t x i} {D : Finset Point}
    {upper : TilingAwayDomino t x r D → ℕ}
    {p q : TruncatedTotals upper → Prop}
    (hpq : ∀ ell, p ell → q ell)
    {a : TilingAwayCoordinates (cap := cap) t x r D}
    (h : TilingAwayTotalsScreen t x r D upper p a) :
    TilingAwayTotalsScreen t x r D upper q a := by
  obtain ⟨ell, hell, htotal⟩ := h
  exact ⟨ell, hpq ell hell, htotal⟩

/-- Every screened away-total assignment lies in the unscreened `True`
support used by the old base factorization. -/
theorem tilingAwayTotalsScreen_true_of_screen
    {i cap : ℕ} {t : DominoTiling} {x : Point}
    {r : TilingRetainedWord t x i} {D : Finset Point}
    {upper : TilingAwayDomino t x r D → ℕ}
    {p : TruncatedTotals upper → Prop}
    {a : TilingAwayCoordinates (cap := cap) t x r D}
    (h : TilingAwayTotalsScreen t x r D upper p a) :
    TilingAwayTotalsScreen t x r D upper (fun _ ↦ True) a :=
  tilingAwayTotalsScreen_mono (fun _ _ ↦ trivial) h

/-- Pointwise reconstruction form of the refined predicate.  This is the
precise deterministic bridge used by broad-I₁/D_eta/Theta/exact-S
acceptors. -/
theorem conditionalRefinedPredicate_iff_reconstructed
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData piece next oldCost)
    (accepts : ∀ z cap, TruncatedTotals (data.upper z cap) → Bool)
    (z : index) (cap : ℕ)
    (q : TilingCappedCoordinates (data.retainedCount z cap) cap)
    (hupper : ∀ b,
      tilingDominoTotal (data.tiling z cap) (data.start z cap)
        (data.retained z cap) (fun j ↦ (q j : ℕ)) b.1 <
          data.upper z cap b) :
    conditionalRefinedPredicate data accepts z cap q ↔
      data.basePredicate z cap q ∧
        accepts z cap
          (reconstructedTilingAwayTotalsOfCoordinates
            (data.tiling z cap) (data.start z cap) (data.retained z cap)
            (data.distinguished z cap) (data.upper z cap) q hupper) = true := by
  unfold conditionalRefinedPredicate
  rw [tilingAwayTotalsScreen_split_iff_reconstructed]

/-- The refined deterministic factorization follows solely from the old
unscreened base factorization. -/
theorem conditionalRefinedPredicate_factorization
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData piece next oldCost)
    (accepts : ∀ z cap, TruncatedTotals (data.upper z cap) → Bool)
    (z : index) (cap : ℕ)
    (q : TilingCappedCoordinates (data.retainedCount z cap) cap) :
    conditionalRefinedPredicate data accepts z cap q ∧
        TilingStoppingAccepted (data.stoppingTime z cap)
          (data.tiling z cap) (data.start z cap) (data.retained z cap)
          (fun j ↦ (q j : ℕ)) (data.tail z cap) ↔
      data.selected z cap
          ((splitTilingCoordinatesEquiv (data.tiling z cap)
            (data.start z cap) (data.retained z cap)
            (data.distinguished z cap) q).1) ∧
        TilingAwayTotalsScreen (data.tiling z cap) (data.start z cap)
          (data.retained z cap) (data.distinguished z cap)
          (data.upper z cap) (fun ell ↦ accepts z cap ell = true)
          ((splitTilingCoordinatesEquiv (data.tiling z cap)
            (data.start z cap) (data.retained z cap)
            (data.distinguished z cap) q).2) := by
  constructor
  · rintro ⟨⟨hbase, hscreen⟩, haccepted⟩
    have hold := (data.base_factorization z cap q).1
      ⟨hbase, haccepted⟩
    exact ⟨hold.1, hscreen⟩
  · rintro ⟨hselected, hscreen⟩
    have htrue := tilingAwayTotalsScreen_true_of_screen hscreen
    have hold := (data.base_factorization z cap q).2
      ⟨hselected, htrue⟩
    exact ⟨⟨hold.1, hscreen⟩, hold.2⟩

/-- The path-level inputs which are not consequences of a finite-product
identity: broad/narrow containment, positive broad mass, cap monotonicity,
and coverage of the concrete next event. -/
structure TilingConditionalRefinementData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData piece next oldCost) where
  baseAccepts : ∀ z cap, TruncatedTotals (data.upper z cap) → Bool
  screenedAccepts : ∀ z cap, TruncatedTotals (data.upper z cap) → Bool
  screenedAccepts_subset_base : ∀ z cap ell,
    screenedAccepts z cap ell = true → baseAccepts z cap ell = true
  base_mass_pos : ∀ z cap,
    0 < screenMass
      (tilingAwayPointMass (cap := cap) (data.tiling z cap)
        (data.start z cap) (data.retained z cap)
        (data.distinguished z cap)) (data.upper z cap)
      (fun ell ↦ baseAccepts z cap ell = true)
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (tilingPreStoppingFiberEvent (data.stoppingTime z cap)
      (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
      (data.tail z cap)
      (conditionalRefinedPredicate data screenedAccepts z cap))
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap,
    walkLift (tilingPreStoppingFiberEvent (data.stoppingTime z cap)
      (data.tiling z cap) (data.start z cap) (data.retained z cap) cap
      (data.tail z cap)
      (conditionalRefinedPredicate data screenedAccepts z cap))

/-- Refine an ordinary factored stopped-coordinate fiber into a genuine
conditional broad/narrow fiber.  The universal cost `1` is proved from
nonnegative point masses and narrow ⊆ broad; it is not an infinite-cost
placeholder (whose real coercion would be zero). -/
noncomputable def conditionalFactoredDataOfRefinement
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {oldCost : ℝ≥0∞}
    (data : TilingFactoredStoppedCoordinateData piece next oldCost)
    (refinement : TilingConditionalRefinementData data) :
    TilingConditionalFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞) where
  tiling := data.tiling
  retainedCount := data.retainedCount
  start := data.start
  retained := data.retained
  tail := data.tail
  stoppingTime := data.stoppingTime
  isStoppingTime := data.isStoppingTime
  basePredicate := conditionalRefinedPredicate data refinement.baseAccepts
  screenedPredicate :=
    conditionalRefinedPredicate data refinement.screenedAccepts
  screened_subset_base := by
    intro z cap q hq
    exact ⟨hq.1, tilingAwayTotalsScreen_mono
      (fun ell ↦ refinement.screenedAccepts_subset_base z cap ell) hq.2⟩
  base_subset_piece := by
    intro z cap s hs
    apply data.base_subset_piece z cap
    exact ⟨hs.1, tilingPreStoppingFiberEvent_mono
      (data.stoppingTime z cap) (data.tiling z cap) (data.start z cap)
      (data.retained z cap) (data.tail z cap)
      (fun _ hq ↦ hq.1) hs.2⟩
  distinguished := data.distinguished
  selected := data.selected
  upper := data.upper
  baseAccepts := refinement.baseAccepts
  screenedAccepts := refinement.screenedAccepts
  screenedAccepts_subset_base := refinement.screenedAccepts_subset_base
  base_factorization :=
    conditionalRefinedPredicate_factorization data refinement.baseAccepts
  screened_factorization :=
    conditionalRefinedPredicate_factorization data refinement.screenedAccepts
  upper_pos := data.upper_pos
  base_mass_ne_zero := fun z cap ↦ ne_of_gt (refinement.base_mass_pos z cap)
  monotone_screened := refinement.monotone_screened
  transition_covered := refinement.transition_covered
  product_bound := by
    intro z cap
    simpa only [ENNReal.toReal_one] using
      conditionalScreenMass_le_one_of_subset
        (tilingAwayPointMass (cap := cap) (data.tiling z cap)
          (data.start z cap) (data.retained z cap)
          (data.distinguished z cap))
        (data.upper z cap)
        (fun ell ↦ refinement.baseAccepts z cap ell = true)
        (fun ell ↦ refinement.screenedAccepts z cap ell = true)
        (fun b v ↦ tilingAwayExactTotalMass_nonneg
          (data.tiling z cap) (data.start z cap) (data.retained z cap)
          (data.distinguished z cap) b v)
        (refinement.screenedAccepts_subset_base z cap)
        (refinement.base_mass_pos z cap)

end

end Erdos1165.TilingConditionalStoppedCoordinateRefinement
