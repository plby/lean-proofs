/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWeightedBound

/-!
# Support-preserving positive-interface pair bound

The strict product estimate can retain the event that every exposed
coordinate belongs to the two adjacent physical rows.  This is the key
form needed for actual-rank summation: on the replacement path that full
pair support is observable, so histories remain disjoint at a fixed rank.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfacePairSupportPreservingBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure
open HLOZAllSixExactCoordinateProductClosure
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedBound
open HLOZPositiveInterfacePairWeightedScreen
open HLOZProposition48Candidates
open HLOZSharpProductNumerics
open HLOZSourceOrientedThetaExternalProduct
open HLOZWeightedRandomTotalProductBound
open LazyDecomposition TilingCappedMarginalization
open NearFavoriteThresholded
open TilingOrientedSupportAwayCoordinates TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The replacement law is restricted to vectors whose adjacent-row support
is exactly the whole exposed pair support. -/
def positiveInterfaceExternalPairReplacementScreen
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (ell : TruncatedTotals
      ((PositiveInterfaceExternalPairFiber eta).upper cap)) : Prop :=
  ∀ c, positiveInterfaceExternalPairUpper eta cap c (ell c) ∨
    positiveInterfaceExternalPairLower eta cap c (ell c)

noncomputable instance instDecidablePredPositiveInterfaceExternalPairReplacementScreen
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ) :
    DecidablePred (positiveInterfaceExternalPairReplacementScreen eta cap) :=
  Classical.decPred _

/-- Normalized mass of the support-preserving replacement screen. -/
noncomputable def positiveInterfaceExternalPairReplacementScreenMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ) : ℝ :=
  let data := PositiveInterfaceExternalPairFiber eta
  @screenMass
    (PositiveInterfaceExternalPairCoordinate eta)
    (instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t eta.1.1.start
      eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2))
    (data.upper cap)
    (positiveInterfaceExternalPairReplacementScreen eta cap)
    (Classical.decPred _)

/-- Generic full-support form of the strict weighted tail bound. -/
theorem rankMultiplicity_mul_fullSupportTail_le_fullSupportMass
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (j bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ positiveInterfaceRatioConstant)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0) :
    ((2 * Fintype.card Coordinate + 1 : ℕ) : ℝ) *
        (∑ ell : ∀ c, State c,
          if randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j bound ell ∧
              pairSupport upper lower ell = Finset.univ then
            productPointMass weight ell else 0) ≤
      (sharpRankConstant * sharpInterfaceCost threshold j) *
        ∑ ell : ∀ c, State c,
          if pairSupport upper lower ell = Finset.univ then
            productPointMass weight ell else 0 := by
  classical
  let total := Fintype.card Coordinate
  let cut := thresholdedGrowthCut threshold shellGrowth48 j total
  let replacementMass := ∑ ell : ∀ c, State c,
    if pairSupport upper lower ell = Finset.univ then
      productPointMass weight ell else 0
  let tailMass := ∑ ell : ∀ c, State c,
    if pairSupport upper lower ell = Finset.univ ∧
        cut ≤ upperCount upper ell then
      productPointMass weight ell else 0
  have hreplacement_nonneg : 0 ≤ replacementMass := by
    dsimp only [replacementMass]
    exact Finset.sum_nonneg fun ell _ ↦ by
      split_ifs
      · exact productPointMass_nonneg weight hweight ell
      · exact le_rfl
  have hsource_le :
      (∑ ell : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j bound ell ∧
            pairSupport upper lower ell = Finset.univ then
          productPointMass weight ell else 0) ≤ tailMass := by
    dsimp only [tailMass]
    apply Finset.sum_le_sum
    intro ell _hell
    by_cases hs : randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j
        bound ell ∧ pairSupport upper lower ell = Finset.univ
    · rw [if_pos hs]
      have hcard : (pairSupport upper lower ell).card = total := by
        rw [hs.2, Finset.card_univ]
      have hcut : cut ≤ upperCount upper ell := by
        unfold randomTotalThresholdedUpperTail at hs
        simpa only [cut, total, hcard] using hs.1.2
      rw [if_pos ⟨hs.2, hcut⟩]
    · rw [if_neg hs]
      by_cases ht : pairSupport upper lower ell = Finset.univ ∧
          cut ≤ upperCount upper ell
      · rw [if_pos ht]
        exact productPointMass_nonneg weight hweight ell
      · rw [if_neg ht]
  have htail : tailMass ≤
      ((1 + C / (1 + C)) ^ total /
        (2 : ℝ) ^ cut) * replacementMass := by
    have hraw := support_upperTail_le weight upper lower hweight hdisjoint
      (C := C) hC0 hratio Finset.univ cut
    have hsupport : supportMass weight upper lower Finset.univ =
        replacementMass := by
      exact (sum_support_eq_supportMass weight upper lower Finset.univ).symm
    rw [Finset.card_univ, hsupport] at hraw
    simpa only [total, cut, div_mul_eq_mul_div] using hraw
  have henvelope :=
    _root_.Erdos1165.HLOZSharpProductNumerics.rankMultiplicity_mul_thresholdedProductEnvelope_le_sharp
      C hC0 hC threshold j total
  have hmult_nonneg :
      0 ≤ (((2 * Fintype.card Coordinate + 1 : ℕ) : ℝ)) := by positivity
  calc
    ((2 * Fintype.card Coordinate + 1 : ℕ) : ℝ) *
        (∑ ell : ∀ c, State c,
          if randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j bound ell ∧
              pairSupport upper lower ell = Finset.univ then
            productPointMass weight ell else 0) ≤
      ((2 * Fintype.card Coordinate + 1 : ℕ) : ℝ) * tailMass :=
        mul_le_mul_of_nonneg_left hsource_le hmult_nonneg
    _ ≤ ((2 * Fintype.card Coordinate + 1 : ℕ) : ℝ) *
        (((1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ cut) * replacementMass) :=
      mul_le_mul_of_nonneg_left htail hmult_nonneg
    _ = (((2 * total + 1 : ℕ) : ℝ) *
          ((1 + C / (1 + C)) ^ total /
            (2 : ℝ) ^ cut)) * replacementMass := by
      simp only [total]
      ring
    _ ≤ (sharpRankConstant * sharpInterfaceCost threshold j) * replacementMass :=
      mul_le_mul_of_nonneg_right (by simpa only [cut] using henvelope)
        hreplacement_nonneg

/-- The source pair tail is paid by a replacement law which retains the
same full adjacent-pair support. -/
theorem pairRankMultiplicity_mul_sourceScreenMass_le_replacementScreenMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap) :
    (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
        positiveInterfaceExternalPairSourceScreenMass eta cap threshold bound ≤
      (sharpRankConstant * sharpInterfaceCost threshold shell) *
        positiveInterfaceExternalPairReplacementScreenMass eta cap := by
  classical
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  letI pairFintype : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
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
    positiveInterfaceExternalPairReplacementScreenMass
  simp only
  rw [screenMass_eq_product, screenMass_eq_product]
  unfold positiveInterfaceExternalPairRankMultiplicity
  have hfull := rankMultiplicity_mul_fullSupportTail_le_fullSupportMass
      (fun (c : PositiveInterfaceExternalPairCoordinate eta)
        (v : Fin (data.upper cap c)) ↦
          coordinateMass weight (data.upper cap) c v)
      (positiveInterfaceExternalPairUpper eta cap)
      (positiveInterfaceExternalPairLower eta cap)
      threshold shell bound hnonneg
      (positiveInterfaceExternalPairUpper_lower_disjoint eta cap)
      positiveInterfaceRatioConstant_nonneg le_rfl
      (positiveInterfaceExternalPair_coordinateMass_ratio eta cap arith)
  calc
    ((2 * Fintype.card (PositiveInterfaceExternalPairCoordinate eta) + 1 : ℕ) : ℝ) *
        (∑ ell,
          if positiveInterfaceExternalPairSourceScreen eta cap threshold bound ell
          then ∏ c, coordinateMass weight (data.upper cap) c (ell c)
          else 0) ≤
      ((2 * Fintype.card (PositiveInterfaceExternalPairCoordinate eta) + 1 : ℕ) : ℝ) *
        (∑ ell,
          if randomTotalThresholdedUpperTail
                (positiveInterfaceExternalPairUpper eta cap)
                (positiveInterfaceExternalPairLower eta cap)
                threshold shellGrowth48 shell bound ell ∧
              pairSupport (positiveInterfaceExternalPairUpper eta cap)
                (positiveInterfaceExternalPairLower eta cap) ell = Finset.univ
          then ∏ c, coordinateMass weight (data.upper cap) c (ell c)
          else 0) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro ell _hell
        by_cases hs : positiveInterfaceExternalPairSourceScreen eta cap threshold
            bound ell
        · rw [if_pos hs]
          rw [if_pos ⟨hs.2.1, hs.2.2⟩]
        · rw [if_neg hs]
          by_cases ht : randomTotalThresholdedUpperTail
                (positiveInterfaceExternalPairUpper eta cap)
                (positiveInterfaceExternalPairLower eta cap)
                threshold shellGrowth48 shell bound ell ∧
              pairSupport (positiveInterfaceExternalPairUpper eta cap)
                (positiveInterfaceExternalPairLower eta cap) ell = Finset.univ
          · rw [if_pos ht]
            exact Finset.prod_nonneg fun c _ ↦ hnonneg c (ell c)
          · rw [if_neg ht]
      · positivity
    _ ≤ (sharpRankConstant * sharpInterfaceCost threshold shell) *
        ∑ ell,
          if pairSupport (positiveInterfaceExternalPairUpper eta cap)
                (positiveInterfaceExternalPairLower eta cap) ell = Finset.univ
          then ∏ c, coordinateMass weight (data.upper cap) c (ell c)
          else 0 := hfull
    _ = (sharpRankConstant * sharpInterfaceCost threshold shell) *
        ∑ ell,
          if positiveInterfaceExternalPairReplacementScreen eta cap ell
          then ∏ c, coordinateMass weight (data.upper cap) c (ell c)
          else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro ell _hell
      have hsupp :
          pairSupport (positiveInterfaceExternalPairUpper eta cap)
              (positiveInterfaceExternalPairLower eta cap) ell = Finset.univ ↔
            positiveInterfaceExternalPairReplacementScreen eta cap ell := by
        constructor
        · intro h c
          have hc : c ∈ pairSupport (positiveInterfaceExternalPairUpper eta cap)
              (positiveInterfaceExternalPairLower eta cap) ell := by
            rw [h]
            exact Finset.mem_univ c
          simpa only [pairSupport, Finset.mem_filter, Finset.mem_univ,
            true_and] using hc
        · intro h
          ext c
          simp only [pairSupport, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact iff_true_intro (h c)
      by_cases h : pairSupport (positiveInterfaceExternalPairUpper eta cap)
          (positiveInterfaceExternalPairLower eta cap) ell = Finset.univ
      · rw [if_pos h, if_pos (hsupp.mp h)]
      · rw [if_neg h, if_neg (fun hr ↦ h (hsupp.mpr hr))]

end

end Erdos1165.HLOZPositiveInterfacePairSupportPreservingBound
