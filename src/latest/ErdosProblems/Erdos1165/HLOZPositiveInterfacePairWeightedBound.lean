/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWeightedScreen

set_option linter.style.haveILetI false

/-!
# Uniform rank-weighted bound on the positive-interface pair screen
-/

namespace Erdos1165.HLOZPositiveInterfacePairWeightedBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure HLOZAllSixExactCoordinateProductClosure
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates HLOZSharpProductNumerics
open HLOZSourceOrientedThetaExternalProduct
open HLOZWeightedRandomTotalProductBound
open LazyDecomposition TilingCappedMarginalization
open TilingOrientedSupportAwayCoordinates TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The total-dependent weighted pair tail is bounded by the uniform strict
sharp-interface envelope. -/
theorem positiveInterfaceExternalPairWeightedTailMass_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap) :
    positiveInterfaceExternalPairWeightedTailMass eta cap threshold bound ≤
      sharpRankConstant * sharpInterfaceCost threshold shell := by
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  letI pairFintype : Fintype
      (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let weight := tilingAwayPointMass (cap := data.coordinateCap cap) t
    eta.1.1.start eta.1.1.retained D
  have hnonneg : ∀
      (c : TilingAwayDomino t eta.1.1.start eta.1.1.retained D)
      (v : Fin (data.upper cap c)),
      0 ≤ coordinateMass weight (data.upper cap) c v := by
    intro c v
    exact coordinateMass_nonneg_of_pointMass_nonneg weight (data.upper cap)
      (by
        intro c' v'
        simpa only [weight, D] using
          externalTheta_pointMass_nonneg data cap c' v') c v
  rw [positiveInterfaceExternalPairWeightedTailMass_eq]
  apply rankMultiplicityWeightedRandomTotal_product_bound_sharp
  · exact hnonneg
  · exact fun c ↦ (externalTheta_coordinate_sum_eq_one data cap c).le
  · exact positiveInterfaceExternalPairUpper_lower_disjoint eta cap
  · exact positiveInterfaceRatioConstant_nonneg
  · exact le_rfl
  · exact positiveInterfaceExternalPair_coordinateMass_ratio eta cap arith

/-- The source subscreen pays its full actual-rank multiplicity inside the
weighted tail. -/
theorem pairRankMultiplicity_mul_sourceScreenMass_le_weightedTailMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) :
    (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
        positiveInterfaceExternalPairSourceScreenMass eta cap threshold bound ≤
      positiveInterfaceExternalPairWeightedTailMass eta cap threshold bound := by
  classical
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  letI pairFintype : Fintype
      (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let weight := tilingAwayPointMass (cap := data.coordinateCap cap) t
    eta.1.1.start eta.1.1.retained D
  have hnonneg : ∀
      (c : PositiveInterfaceExternalPairCoordinate eta)
      (v : Fin (data.upper cap c)),
      0 ≤ coordinateMass weight (data.upper cap) c v := by
    intro c v
    exact coordinateMass_nonneg_of_pointMass_nonneg weight (data.upper cap)
      (by
        intro c' v'
        simpa only [weight, D] using
          externalTheta_pointMass_nonneg data cap c' v') c v
  unfold positiveInterfaceExternalPairSourceScreenMass
  rw [screenMass_eq_product]
  unfold positiveInterfaceExternalPairRankMultiplicity
  unfold positiveInterfaceExternalPairWeightedTailMass
  exact fullSupportScreen_rankMultiplicity_le_weightedTail
    (fun (c : TilingAwayDomino t eta.1.1.start eta.1.1.retained D)
      (v : Fin (data.upper cap c)) ↦
        coordinateMass weight (data.upper cap) c v)
    (positiveInterfaceExternalPairUpper eta cap)
    (positiveInterfaceExternalPairLower eta cap)
    threshold shell bound
    (positiveInterfaceExternalPairSourceScreen eta cap threshold bound)
    hnonneg (fun ell hs ↦ ⟨hs.2.1, hs.2.2⟩)

/-- The actual-rank multiplicity times the normalized source-screen mass is
uniformly absorbed by the strict sharp-interface envelope. -/
theorem pairRankMultiplicity_mul_positiveInterfaceExternalPairSourceScreenMass_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap) :
    (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
        positiveInterfaceExternalPairSourceScreenMass eta cap threshold bound ≤
      sharpRankConstant * sharpInterfaceCost threshold shell :=
  (pairRankMultiplicity_mul_sourceScreenMass_le_weightedTailMass eta cap
    threshold bound).trans
      (positiveInterfaceExternalPairWeightedTailMass_le eta cap threshold
        bound arith)

end

end Erdos1165.HLOZPositiveInterfacePairWeightedBound
