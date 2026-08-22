/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaWalkCap

/-!
# Multiplicity facts for positive-interface pair caps

The actual endpoint-increment index has exactly the rank multiplicity used
by the weighted product estimate.  Moreover, a nonempty source cap has fewer
than `bound + 1` exposed pair coordinates, because its random-total screen
uses every exposed coordinate.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePairMultiplicity

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingFiber StoppedInsertion
open TilingCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The honest actual-increment type has precisely the multiplicity appearing
in the rank-weighted pair estimate. -/
noncomputable def positiveInterfaceExternalPairActualDeltaEquiv
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :
    SourceActualDeltaIndex (PositiveInterfaceExternalPairFiber eta) ≃
      Fin (positiveInterfaceExternalPairRankMultiplicity eta) := by
  classical
  apply finCongr
  rfl

@[simp] theorem positiveInterfaceExternalPairActualDeltaEquiv_apply_val
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta)) :
    ((positiveInterfaceExternalPairActualDeltaEquiv eta delta :
      Fin (positiveInterfaceExternalPairRankMultiplicity eta)) : ℕ) =
      (delta : ℕ) := by
  classical
  unfold positiveInterfaceExternalPairActualDeltaEquiv
  exact finCongr_apply_coe _ delta

@[simp] theorem positiveInterfaceExternalPairActualDeltaEquiv_symm_val
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (delta : Fin (positiveInterfaceExternalPairRankMultiplicity eta)) :
    (((positiveInterfaceExternalPairActualDeltaEquiv eta).symm delta :
      SourceActualDeltaIndex (PositiveInterfaceExternalPairFiber eta)) : ℕ) =
      (delta : ℕ) := by
  let e := positiveInterfaceExternalPairActualDeltaEquiv eta
  have h := positiveInterfaceExternalPairActualDeltaEquiv_apply_val eta
    (e.symm delta)
  simpa only [e, Equiv.apply_symm_apply] using h.symm

/-- A nonempty source cap exposes at most `bound` pair coordinates. -/
theorem coordinate_card_lt_bound_add_one_of_mem_sourceCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) {s : WalkPath}
    (hs : s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    Fintype.card (PositiveInterfaceExternalPairCoordinate eta) < bound + 1 := by
  classical
  rcases hs with ⟨_hvalid, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨qacc, _hqstop⟩
  rcases qacc with ⟨q, hpredicate, _haccepted⟩
  rcases hpredicate.2 with ⟨ell, hscreen, _htotal⟩
  have htail := hscreen.2.1
  unfold randomTotalThresholdedUpperTail at htail
  let J : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    inferInstance
  let I := instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained eta.1.2)
  have htailCard := htail.1
  rw [hscreen.2.2] at htailCard
  have htailI :
      @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) I <
        bound + 1 := by
    simpa only [Finset.card_univ] using htailCard
  have hcard : @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) J =
      @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) I :=
    @Fintype.card_congr _ _ J I (Equiv.refl _)
  change @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) J <
    bound + 1
  exact hcard.le.trans_lt htailI

/-- The rank multiplicity of a nonempty source cap is bounded by
`2 * bound + 1`. -/
theorem rankMultiplicity_le_two_mul_bound_add_one_of_mem_sourceCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) {s : WalkPath}
    (hs : s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold bound) :
    positiveInterfaceExternalPairRankMultiplicity eta ≤ 2 * bound + 1 := by
  have hcard := coordinate_card_lt_bound_add_one_of_mem_sourceCap eta cap
    threshold bound hs
  let J : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    inferInstance
  change @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) J <
    bound + 1 at hcard
  let I := instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained eta.1.2)
  have hcardEq :
      @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) I =
        @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) J :=
    @Fintype.card_congr _ _ I J (Equiv.refl _)
  have hcardI :
      @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) I <
        bound + 1 := hcardEq.le.trans_lt hcard
  unfold positiveInterfaceExternalPairRankMultiplicity
  change 2 * @Fintype.card (PositiveInterfaceExternalPairCoordinate eta) I +
    1 ≤ 2 * bound + 1
  omega

end

end Erdos1165.HLOZPositiveInterfacePairMultiplicity
