/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationCanonicalRefinement

/-!
# Restricting a prefixed all-creation product on distinguished coordinates

The conditional negative-binomial product lives only on the away
coordinates.  Consequently a further condition on the distinguished
coordinate assignment changes the retained carrier, but not the normalized
away-coordinate ratio.  This file packages that exact cancellation.
-/

open Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationDistinguishedRestriction

open TilingCappedMarginalization
open LazyDecomposition
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Replace only the selected distinguished-coordinate predicate of an
all-creation stopped fibre. -/
noncomputable def withSelected
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.external.start z.external.retained
        (supportComplementDistinguished t z.external.start
          z.external.retained S) → Prop) :
    OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z where
  coordinateCap := data.coordinateCap
  capStart := data.capStart
  coordinateCap_eq := data.coordinateCap_eq
  totalCap := data.totalCap
  totalCap_le_capStart := data.totalCap_le_capStart
  retainedCount_le_totalCap := data.retainedCount_le_totalCap
  stoppingTime := data.stoppingTime
  isStoppingTime := data.isStoppingTime
  atomPredicate := data.atomPredicate
  support_represented := data.support_represented
  selected := selected
  upper := data.upper
  upper_pos := data.upper_pos
  totalCap_lt_upper := data.totalCap_lt_upper
  atom_measurable := data.atom_measurable
  atom_sound := data.atom_sound
  atom_complete := data.atom_complete
  atom_monotone := data.atom_monotone

/-- Add a predicate on the distinguished projection to a full-coordinate
predicate. -/
def restrictPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (safe : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.external.start z.external.retained
        (data.distinguished cap) → Prop)
    (predicate : ∀ cap, TilingCappedCoordinates z.external.retainedCount
      (data.coordinateCap cap) → Prop)
    (cap : ℕ) (q : TilingCappedCoordinates z.external.retainedCount
      (data.coordinateCap cap)) : Prop :=
  predicate cap q ∧ safe cap
    ((splitTilingCoordinatesEquiv t (data.start cap) (data.retained cap)
      (data.distinguished cap) q).1)

/-- Restrict an exact conditional refinement only through its distinguished
carrier.  The away-coordinate screen masses, and therefore their ratio, are
definitionally unchanged.  Event containment and cap monotonicity are kept
as explicit deterministic obligations because their path-space formulation
depends on the caller's chosen distinguished predicate. -/
noncomputable def restrictRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    {piece next restrictedPiece restrictedNext : Set WalkPath}
    {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      data piece next cost)
    (safe : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.external.start z.external.retained
        (data.distinguished cap) → Prop)
    (base_subset_restrictedPiece : ∀ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent (data.stoppingTime cap)
        (data.initial cap) t (data.start cap) (data.retained cap)
        (data.coordinateCap cap) (data.tail cap)
        (restrictPredicate data safe refinement.basePredicate cap)) ⊆
          restrictedPiece)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent (data.stoppingTime cap)
        (data.initial cap) t (data.start cap) (data.retained cap)
        (data.coordinateCap cap) (data.tail cap)
        (restrictPredicate data safe refinement.screenedPredicate cap)))
    (transition_covered : restrictedPiece ∩ restrictedNext ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent (data.stoppingTime cap)
        (data.initial cap) t (data.start cap) (data.retained cap)
        (data.coordinateCap cap) (data.tail cap)
        (restrictPredicate data safe refinement.screenedPredicate cap))) :
    OrientedAllCreationConditionalRefinementData
      (withSelected data (fun cap d ↦ data.selected cap d ∧ safe cap d))
      restrictedPiece restrictedNext cost where
  basePredicate := restrictPredicate data safe refinement.basePredicate
  screenedPredicate := restrictPredicate data safe refinement.screenedPredicate
  base_subset_atom := by
    intro cap q hq
    exact refinement.base_subset_atom cap q hq.1
  screened_subset_basePredicate := by
    intro cap q hq
    exact ⟨refinement.screened_subset_basePredicate cap q hq.1, hq.2⟩
  baseAccepts := refinement.baseAccepts
  screenedAccepts := refinement.screenedAccepts
  screened_subset_base := refinement.screened_subset_base
  base_factorization := by
    intro cap q
    change
      ((refinement.basePredicate cap q ∧
          safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).1)) ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap)) ↔
      (data.selected cap ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).1) ∧
        safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).1)) ∧
      TilingAwayTotalsScreen t (data.start cap) (data.retained cap)
        (data.distinguished cap) (data.upper cap)
        (fun ell ↦ refinement.baseAccepts cap ell = true)
        ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).2)
    rw [show
      ((refinement.basePredicate cap q ∧
          safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).1)) ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap)) =
      ((refinement.basePredicate cap q ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap)) ∧
        safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).1)) by
            apply propext
            tauto]
    rw [refinement.base_factorization cap q]
    tauto
  screened_factorization := by
    intro cap q
    change
      ((refinement.screenedPredicate cap q ∧
          safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).1)) ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap)) ↔
      (data.selected cap ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).1) ∧
        safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).1)) ∧
      TilingAwayTotalsScreen t (data.start cap) (data.retained cap)
        (data.distinguished cap) (data.upper cap)
        (fun ell ↦ refinement.screenedAccepts cap ell = true)
        ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).2)
    rw [show
      ((refinement.screenedPredicate cap q ∧
          safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).1)) ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap)) =
      ((refinement.screenedPredicate cap q ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap)) ∧
        safe cap ((splitTilingCoordinatesEquiv t (data.start cap)
          (data.retained cap) (data.distinguished cap) q).1)) by
            apply propext
            tauto]
    rw [refinement.screened_factorization cap q]
    tauto
  base_mass_pos := refinement.base_mass_pos
  base_subset_piece := base_subset_restrictedPiece
  monotone_screened := monotone_screened
  transition_covered := transition_covered
  product_bound := refinement.product_bound

end

end Erdos1165.HLOZPrefixedAllCreationDistinguishedRestriction
