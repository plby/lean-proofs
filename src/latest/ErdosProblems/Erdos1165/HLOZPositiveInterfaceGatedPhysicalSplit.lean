/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceGatedPhysicalScreenedEvent

/-!
# Exact split at the coordinate-gated physical interface

The gated product removes both physical rows at an ineligible coordinate.
This does not introduce an unclassified product remainder: an ungated
physical upper-tail vector either remains in the gated upper tail, or one of
its actual upper-row coordinates is ineligible.  Removing only ineligible
lower-row coordinates can decrease the adjacent-pair total, hence can only
decrease the thresholded growth cut.

This is a finite-coordinate statement.  Identifying the raw path-space band
occupancy with the ungated physical stopped-coordinate predicate is a
separate reconstruction theorem.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfaceGatedPhysicalSplit

open FiniteDominoProductLaw
open HeterogeneousProductTail
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllSixBandProductClosure
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceGatedPhysicalScreenedEvent
open HLOZPositiveInterfacePhysicalWindows
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open HLOZProposition48Candidates
open LazyDecomposition
open NearFavoriteShells
open NearFavoriteThresholded
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The ungated upper physical row on one exact positive-interface fibre. -/
def positiveInterfacePhysicalUpper
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (width shell : ℕ)
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap))
    (v : Fin ((PositiveInterfaceFiber eta).upper cap b)) : Prop :=
  (v : ℕ) ∈ physicalDeficitFailureWindow m width
    (Fintype.card (TilingCoordinatesAt t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1)

/-- The ungated lower physical row on one exact positive-interface fibre. -/
def positiveInterfacePhysicalLower
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (width shell : ℕ)
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap))
    (v : Fin ((PositiveInterfaceFiber eta).upper cap b)) : Prop :=
  (v : ℕ) ∈ physicalDeficitFailureWindow m width
    (Fintype.card (TilingCoordinatesAt t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) b.1)) shell

/-- Removing ineligible coordinates from both rows either preserves an
ungated thresholded upper tail, or exposes an actual ineligible upper-row
coordinate.  Ineligible lower coordinates alone only decrease the pair
total and therefore cannot destroy the upper-tail inequality. -/
theorem physicalTail_gated_or_exists_ineligible_upper
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (threshold : ℕ → ℕ) (width shell bound cap : ℕ)
    (ell : TruncatedTotals ((PositiveInterfaceFiber eta).upper cap))
    (hraw : allCreationRandomTotalThresholdedUpperTail
      (PositiveInterfaceFiber eta) cap
      (positiveInterfacePhysicalUpper width shell eta cap)
      (positiveInterfacePhysicalLower width shell eta cap)
      threshold shellGrowth48 shell bound ell) :
    allCreationRandomTotalThresholdedUpperTail
        (PositiveInterfaceFiber eta) cap
        (fun b v ↦ positiveInterfacePhysicalEligible width shell eta cap b ∧
          positiveInterfacePhysicalUpper width shell eta cap b v)
        (fun b v ↦ positiveInterfacePhysicalEligible width shell eta cap b ∧
          positiveInterfacePhysicalLower width shell eta cap b v)
        threshold shellGrowth48 shell bound ell ∨
      ∃ b, ¬ positiveInterfacePhysicalEligible width shell eta cap b ∧
        positiveInterfacePhysicalUpper width shell eta cap b (ell b) := by
  classical
  by_cases hbad : ∃ b, ¬ positiveInterfacePhysicalEligible width shell eta cap b ∧
      positiveInterfacePhysicalUpper width shell eta cap b (ell b)
  · exact Or.inr hbad
  · apply Or.inl
    let _ : Fintype (TilingAwayDomino t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap)
        ((PositiveInterfaceFiber eta).distinguished cap)) :=
      instFintypeTilingAwayDomino t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap)
        ((PositiveInterfaceFiber eta).distinguished cap)
    unfold allCreationRandomTotalThresholdedUpperTail at hraw ⊢
    unfold randomTotalThresholdedUpperTail at hraw ⊢
    let rawUpper := positiveInterfacePhysicalUpper width shell eta cap
    let rawLower := positiveInterfacePhysicalLower width shell eta cap
    let eligible := positiveInterfacePhysicalEligible width shell eta
    let gatedUpper := fun b v ↦ eligible cap b ∧ rawUpper b v
    let gatedLower := fun b v ↦ eligible cap b ∧ rawLower b v
    have heligible : ∀ b, rawUpper b (ell b) → eligible cap b := by
      intro b hb
      by_contra hne
      exact hbad ⟨b, hne, hb⟩
    have hpair : pairSupport gatedUpper gatedLower ell ⊆
        pairSupport rawUpper rawLower ell := by
      intro b hb
      simp only [pairSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        gatedUpper, gatedLower] at hb ⊢
      exact hb.elim (fun h ↦ Or.inl h.2) (fun h ↦ Or.inr h.2)
    have hcard : (pairSupport gatedUpper gatedLower ell).card ≤
        (pairSupport rawUpper rawLower ell).card := Finset.card_le_card hpair
    have hupper : upperCount gatedUpper ell = upperCount rawUpper ell := by
      unfold upperCount
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hu : rawUpper b (ell b)
      · have he := heligible b hu
        simp [gatedUpper, hu, he]
      · simp [gatedUpper, hu]
    have hcut : thresholdedGrowthCut threshold shellGrowth48 shell
          (pairSupport gatedUpper gatedLower ell).card ≤
        thresholdedGrowthCut threshold shellGrowth48 shell
          (pairSupport rawUpper rawLower ell).card := by
      unfold thresholdedGrowthCut growthCut
      gcongr
    constructor
    · exact lt_of_le_of_lt hcard hraw.1
    · rw [hupper]
      exact hcut.trans hraw.2

end

end Erdos1165.HLOZPositiveInterfaceGatedPhysicalSplit
