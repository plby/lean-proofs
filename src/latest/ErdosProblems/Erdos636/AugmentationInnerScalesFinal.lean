/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.AugmentationInnerScalesRisk

/-!
# Uniform final inner-exposure bounds

This module takes the coefficient package and the already uniform partial
exposure bounds and supplies one branch-order threshold after which every
rounded scalar required by the full exposure is valid.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationInnerScales

noncomputable section

open AsymptoticThresholds

/-- One threshold makes the complete inner-exposure numerical package valid,
uniformly in the ambient order and in every admissible branch size, state
count, and crowded-path degree window. -/
theorem exists_innerExposureFinalBounds
    {K : ℕ}
    {a₀ theta Qpartial gapCoeff cBalance innerTheta qGeom badGeomCoeff
      sigmaCoeff globalCoeff qDegree meanRadius lambdaCoeff mCoeff energyCoeff
      qScale kappaCoeff badCollisionCoeff badDegreeCoeff pieceCoeff outputCoeff
      a₂ deltaLower deltaUpper windowCoeff : ℝ}
    (H : InnerExposureCoefficientBounds K a₀ theta Qpartial gapCoeff
      cBalance innerTheta qGeom badGeomCoeff sigmaCoeff globalCoeff qDegree
      meanRadius lambdaCoeff mCoeff energyCoeff qScale kappaCoeff
      badCollisionCoeff badDegreeCoeff pieceCoeff outputCoeff a₂ deltaLower
      deltaUpper windowCoeff) :
    ∃ N : ℕ, ∀ nD ≥ N, ∀ n nZ nS degreeWindow ambient : ℕ,
      deltaLower * Real.sqrt nD ≤ (nZ : ℝ) →
      (nZ : ℝ) ≤ deltaUpper * Real.sqrt nD →
      nS + 1 = nZ →
      (degreeWindow : ℝ) ≤ windowCoeff * Real.sqrt nD →
      ∀ Cpartial LH c₀ : ℝ,
      AugmentationScales.PartialExposureFinalBounds K n nD nZ nS ambient
          a₀ theta Qpartial Cpartial LH c₀ deltaUpper gapCoeff →
      InnerExposureFinalBounds K nD nZ nS degreeWindow a₀ theta Qpartial LH
        gapCoeff cBalance innerTheta (Qpartial * Real.sqrt nD) qGeom
        badGeomCoeff sigmaCoeff globalCoeff qDegree meanRadius lambdaCoeff
        mCoeff energyCoeff qScale kappaCoeff badCollisionCoeff badDegreeCoeff
        pieceCoeff outputCoeff a₂ := by
  obtain ⟨Nrounded, hrounded⟩ :=
    AugmentationInnerScalesRoundingScratch.exists_innerRoundedPackingBounds
      H.a₀_pos H.mCoeff_pos H.energyCoeff_pos H.badGeomCoeff_pos
      H.badCollisionCoeff_pos H.badDegreeCoeff_pos H.pieceCoeff_pos
      H.outputCoeff_pos H.a₂_nonneg H.deltaUpper_nonneg H.survivor_coeff
      H.piece_coeff H.output_gap_coeff H.output_coeff H.output_scale_coeff
  obtain ⟨Nsteps, hsteps⟩ :=
    exists_half_mul_sqrt_le_floor mCoeff H.mCoeff_pos
  obtain ⟨NstepsOne, hstepsOne⟩ :=
    exists_const_le_mul_sqrt (mCoeff / 2) 1
      (div_pos H.mCoeff_pos (by norm_num))
  obtain ⟨Npiece, hpiece⟩ :=
    exists_half_mul_sqrt_le_floor pieceCoeff H.pieceCoeff_pos
  obtain ⟨Noutput, houtput⟩ :=
    exists_nat_rpow_ge 1 (2 / outputCoeff) (by norm_num)
  obtain ⟨Nstate, hstate⟩ :=
    exists_const_le_mul_sqrt deltaLower 2 H.deltaLower_pos
  obtain ⟨Nsmall, hsmall⟩ :=
    exists_const_le_mul_sqrt innerTheta (4 * Qpartial) H.innerTheta_pos
  let N := max 1 (max Nrounded
    (max Nsteps (max NstepsOne (max Npiece (max Noutput
      (max Nstate Nsmall))))))
  refine ⟨N, ?_⟩
  intro nD hnD n nZ nS degreeWindow ambient hnZLower hnZUpper hnS
    hdegreeWindow Cpartial LH c₀ P
  have hnD1 : 1 ≤ nD := (le_max_left _ _).trans hnD
  have htail : max Nrounded
      (max Nsteps (max NstepsOne (max Npiece (max Noutput
        (max Nstate Nsmall))))) ≤ nD :=
    (le_max_right _ _).trans hnD
  have hNrounded : Nrounded ≤ nD := (le_max_left _ _).trans htail
  have htail1 : max Nsteps (max NstepsOne (max Npiece (max Noutput
      (max Nstate Nsmall)))) ≤ nD := (le_max_right _ _).trans htail
  have hNsteps : Nsteps ≤ nD := (le_max_left _ _).trans htail1
  have htail2 : max NstepsOne (max Npiece (max Noutput
      (max Nstate Nsmall))) ≤ nD := (le_max_right _ _).trans htail1
  have hNstepsOne : NstepsOne ≤ nD := (le_max_left _ _).trans htail2
  have htail3 : max Npiece (max Noutput (max Nstate Nsmall)) ≤ nD :=
    (le_max_right _ _).trans htail2
  have hNpiece : Npiece ≤ nD := (le_max_left _ _).trans htail3
  have htail4 : max Noutput (max Nstate Nsmall) ≤ nD :=
    (le_max_right _ _).trans htail3
  have hNoutput : Noutput ≤ nD := (le_max_left _ _).trans htail4
  have htail5 : max Nstate Nsmall ≤ nD := (le_max_right _ _).trans htail4
  have hNstate : Nstate ≤ nD := (le_max_left _ _).trans htail5
  have hNsmall : Nsmall ≤ nD := (le_max_right _ _).trans htail5
  have hnDpos : 0 < nD := Nat.zero_lt_one.trans_le hnD1
  have hnDreal : (0 : ℝ) < nD := by exact_mod_cast hnDpos
  have hsqrtPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDreal
  have hstateLarge : 2 ≤ deltaLower * Real.sqrt nD := hstate nD hNstate
  have hnSLower : deltaLower / 2 * Real.sqrt nD ≤ (nS : ℝ) := by
    have hnSCast : (nZ : ℝ) = nS + 1 := by
      exact_mod_cast hnS.symm
    rw [hnSCast] at hnZLower
    nlinarith
  have hnSposReal : (0 : ℝ) < nS :=
    lt_of_lt_of_le (mul_pos (div_pos H.deltaLower_pos (by norm_num))
      hsqrtPos) hnSLower
  have hnSpos : 0 < nS := by exact_mod_cast hnSposReal
  have hsmallLarge : 4 * Qpartial ≤ innerTheta * Real.sqrt nD :=
    hsmall nD hNsmall
  have hstepsLower : mCoeff / 2 * Real.sqrt nD ≤
      (exposureSteps mCoeff nD : ℝ) := hsteps nD hNsteps
  have hstepsOne' : 1 ≤ mCoeff / 2 * Real.sqrt nD :=
    hstepsOne nD hNstepsOne
  have hpieceLower : pieceCoeff / 2 * Real.sqrt nD ≤
      (exposurePiece pieceCoeff nD : ℝ) := hpiece nD hNpiece
  have houtputRpow := houtput nD hNoutput
  rw [Real.rpow_one] at houtputRpow
  have houtputArgLarge : 2 ≤ outputCoeff * nD := by
    have hscaled := mul_le_mul_of_nonneg_left houtputRpow H.outputCoeff_pos.le
    rw [mul_div_cancel₀ 2 H.outputCoeff_pos.ne'] at hscaled
    simpa [mul_comm] using hscaled
  have houtputLower : outputCoeff / 2 * nD ≤
      (exposureOutput outputCoeff nD : ℝ) := by
    dsimp only [exposureOutput]
    convert half_le_natFloor houtputArgLarge using 1 <;> ring
  have hrounded' := hrounded nD hNrounded nZ hnZUpper
  have hroundedFinal :
      degreeBadBudget badDegreeCoeff nD <
          partialMatchingSize a₀ nD -
            AugmentationScales.partialBadBudget a₀ nD ∧
      exposurePiece pieceCoeff nD *
          (partialMatchingSize a₀ nD +
            2 * collisionEdgeBudget energyCoeff nD) ≤
        (partialMatchingSize a₀ nD -
            AugmentationScales.partialBadBudget a₀ nD -
            degreeBadBudget badDegreeCoeff nD) ^ 2 ∧
      exposureOutput outputCoeff nD ≤
        ((exposureSteps mCoeff nD + 1) -
            (AugmentationScales.geometricBadBudget badGeomCoeff nD +
              collisionBadBudget badCollisionCoeff nD)) *
          exposurePiece pieceCoeff nD ∧
      a₂ * nZ * Real.sqrt nD ≤ exposureOutput outputCoeff nD := by
    simpa only [AugmentationInnerScalesRoundingScratch.degreeBadBudget,
      AugmentationInnerScalesRoundingScratch.exposurePiece,
      AugmentationInnerScalesRoundingScratch.collisionEdgeBudget,
      AugmentationInnerScalesRoundingScratch.exposureOutput,
      AugmentationInnerScalesRoundingScratch.exposureSteps,
      AugmentationInnerScalesRoundingScratch.collisionBadBudget,
      degreeBadBudget, exposurePiece, collisionEdgeBudget, exposureOutput,
      exposureSteps, collisionBadBudget] using hrounded'
  have hdegreeThresholdNonneg :
      0 ≤ candidateDegreeThreshold qDegree nD :=
    mul_nonneg H.qDegree_pos.le (Real.sqrt_nonneg _)
  have hdegreeRadiusNonneg : 0 ≤ Qpartial * Real.sqrt nD :=
    mul_nonneg H.Qpartial_pos.le (Real.sqrt_nonneg _)
  have hgeometry := AugmentationScales.exposureGeometryBounds
    (K := K) (nD := nD) (nZ := nZ) (nS := nS)
    (degreeWindow := degreeWindow)
    (degreeThreshold := candidateDegreeThreshold qDegree nD)
    (degreeRadius := Qpartial * Real.sqrt nD)
    H.K_pos hnDpos hnSpos hnS H.deltaUpper_nonneg hnZUpper
    H.windowCoeff_nonneg hdegreeWindow H.qDegree_pos.le
    hdegreeThresholdNonneg (by exact le_rfl) H.Qpartial_pos.le
    hdegreeRadiusNonneg (by exact le_rfl) H.qGeom_nonneg H.badGeomCoeff_pos
    H.sigmaCoeff_pos H.inner_coeff H.geometric_risk_coeff H.global_coeff
  have hcoeffRest :
      deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff / badCollisionCoeff +
        (a₀ / 4) *
            (2 * Real.exp (-(qDegree ^ 2 /
              (32 * (K : ℝ) ^ 2)))) / badDegreeCoeff +
        deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
            qScale / kappaCoeff ≤ 7 / 48 := by
    linarith [H.risk_coeff]
  have hrisk := exposureRisk_le_one_sixth_of_coefficient_bounds
    H.K_pos H.a₀_pos hnS hnZUpper H.cBalance_pos H.innerTheta_pos
    H.qGeom_nonneg H.badGeomCoeff_pos H.qDegree_pos H.meanRadius_nonneg
    H.energyCoeff_pos H.qScale_pos H.kappaCoeff_pos
    H.badCollisionCoeff_pos H.badDegreeCoeff_pos hgeometry.geometric_risk
    hcoeffRest
  exact innerExposureFinalBounds_of_rounding H P hnDpos hnS hnZLower
    hnZUpper hdegreeWindow hnSLower hsmallLarge hstepsLower hstepsOne'
    hpieceLower houtputLower hroundedFinal hrisk

/-! ## Choice of the fixed inner coefficients -/

/-- A convenient elementary Gaussian-tail chooser.  The square threshold is
chosen from a natural point at which the standard polynomial-exponential
limit estimate applies. -/
private theorem exists_gaussianTail_le
    {A b epsilon : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hepsilon : 0 < epsilon) :
    ∃ q : ℝ, 0 < q ∧ A * Real.exp (-(q ^ 2 / b)) ≤ epsilon := by
  obtain ⟨N, hN⟩ := exists_polynomial_mul_exp_neg_lt A b 0 hA hb epsilon
    hepsilon
  let t : ℕ := max 1 N
  have ht1 : 1 ≤ t := le_max_left _ _
  have hNt : N ≤ t := le_max_right _ _
  have htpos : (0 : ℝ) < t := by
    exact_mod_cast (Nat.zero_lt_one.trans_le ht1)
  have hsqrtPos : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
  have hsqrtSq : (Real.sqrt t) ^ 2 = (t : ℝ) := Real.sq_sqrt htpos.le
  let q : ℝ := b * Real.sqrt t
  have hq : 0 < q := by dsimp [q]; positivity
  have hratio : q ^ 2 / b = b * t := by
    dsimp [q]
    rw [mul_pow, hsqrtSq]
    field_simp
  refine ⟨q, hq, ?_⟩
  have hdecay := (hN t hNt).le
  rw [hratio]
  simpa only [Real.rpow_zero, pow_zero, mul_one, neg_mul] using hdecay

private lemma chosen_outputScale
    {outputCoeff deltaUpper : ℝ}
    (houtputCoeff : 0 ≤ outputCoeff) (hdeltaUpper : 0 ≤ deltaUpper) :
    2 * (outputCoeff / (4 * (deltaUpper + 1))) * deltaUpper ≤
      outputCoeff := by
  have hden : 0 < 2 * (deltaUpper + 1) := by positivity
  have hplus : 0 < deltaUpper + 1 := by positivity
  have hratio : deltaUpper / (2 * (deltaUpper + 1)) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  calc
    2 * (outputCoeff / (4 * (deltaUpper + 1))) * deltaUpper =
        outputCoeff * (deltaUpper / (2 * (deltaUpper + 1))) := by
          field_simp [hplus.ne']
          ring_nf
    _ ≤ outputCoeff * 1 := mul_le_mul_of_nonneg_left hratio houtputCoeff
    _ = outputCoeff := by ring

private lemma chosen_degreeRisk
    {a x epsilon : ℝ} (ha : 0 < a) (h : 16 * x ≤ epsilon) :
    (a / 4) * (2 * x) / (a / 32) ≤ epsilon := by
  have heq : (a / 4) * (2 * x) / (a / 32) = 16 * x := by
    field_simp
    ring
  rw [heq]
  exact h

/-- The chosen fixed coefficients, bundled so downstream assembly can project
the numerical values as well as the proof of every comparison. -/
structure InnerExposureCoefficientChoice
    (K : ℕ)
    (a₀ theta Qpartial gapCoeff cBalance deltaLower deltaUpper
      windowCoeff : ℝ) where
  innerTheta : ℝ
  qGeom : ℝ
  badGeomCoeff : ℝ
  sigmaCoeff : ℝ
  globalCoeff : ℝ
  qDegree : ℝ
  meanRadius : ℝ
  lambdaCoeff : ℝ
  mCoeff : ℝ
  energyCoeff : ℝ
  qScale : ℝ
  kappaCoeff : ℝ
  badCollisionCoeff : ℝ
  badDegreeCoeff : ℝ
  pieceCoeff : ℝ
  outputCoeff : ℝ
  a₂ : ℝ
  a₂_pos : 0 < a₂
  bounds : InnerExposureCoefficientBounds K a₀ theta Qpartial gapCoeff
    cBalance innerTheta qGeom badGeomCoeff sigmaCoeff globalCoeff qDegree
    meanRadius lambdaCoeff mCoeff energyCoeff qScale kappaCoeff
    badCollisionCoeff badDegreeCoeff pieceCoeff outputCoeff a₂ deltaLower
    deltaUpper windowCoeff

/-- The sole nontrivial compatibility condition is the positive endpoint
margin.  Once it holds, all tail, switching, packing, radius, and output
coefficients can be selected.  In particular, `windowCoeff` remains an
arbitrary sufficiently small external input rather than being tied to an
earlier outer-window choice. -/
theorem nonempty_innerExposureCoefficientChoice
    {K : ℕ}
    {a₀ theta Qpartial gapCoeff cBalance deltaLower deltaUpper
      windowCoeff : ℝ}
    (hK : 0 < K) (ha₀ : 0 < a₀) (htheta : 0 < theta)
    (hQpartial : 0 < Qpartial) (hgapCoeff : 0 < gapCoeff)
    (hcBalance : 0 < cBalance) (hcBalanceHalf : cBalance ≤ 1 / 2)
    (hdeltaLower : 0 < deltaLower) (hdeltaUpper : 0 < deltaUpper)
    (hwindowCoeff : 0 ≤ windowCoeff)
    (hendpoint :
      (K : ℝ) ^ 2 * deltaUpper ^ 2 +
          2 * deltaUpper * windowCoeff < deltaLower * gapCoeff / 4) :
    Nonempty (InnerExposureCoefficientChoice K a₀ theta Qpartial gapCoeff
      cBalance deltaLower deltaUpper windowCoeff) := by
  let innerTheta : ℝ := theta / 4
  have hinnerTheta : 0 < innerTheta := by dsimp [innerTheta]; positivity
  let meanRadius : ℝ :=
    2 * windowCoeff + (K : ℝ) ^ 2 * deltaUpper + Qpartial
  have hmeanRadius : 0 < meanRadius := by
    dsimp [meanRadius]
    positivity
  let endpointGap : ℝ := deltaLower * gapCoeff / 4 -
    ((K : ℝ) ^ 2 * deltaUpper ^ 2 + 2 * deltaUpper * windowCoeff)
  have hendpointGap : 0 < endpointGap := by dsimp [endpointGap]; linarith
  let lambdaCoeff : ℝ := endpointGap / 2
  have hlambdaCoeff : 0 < lambdaCoeff := by dsimp [lambdaCoeff]; positivity
  let badDegreeCoeff : ℝ := a₀ / 32
  have hbadDegreeCoeff : 0 < badDegreeCoeff := by
    dsimp [badDegreeCoeff]
    positivity
  obtain ⟨qDegree, hqDegree, hdegreeTail⟩ :=
    exists_gaussianTail_le (A := 16)
      (b := 32 * (K : ℝ) ^ 2) (epsilon := 1 / 96)
      (by norm_num) (by positivity) (by norm_num)
  let sigmaCoeff : ℝ := 2 * ((K : ℝ) ^ 2 * deltaUpper +
    windowCoeff + qDegree + Qpartial / 2) + 1
  have hsigmaCoeff : 0 < sigmaCoeff := by
    dsimp [sigmaCoeff]
    positivity
  let kappaCoeff : ℝ := lambdaCoeff / 4
  have hkappaCoeff : 0 < kappaCoeff := by
    dsimp [kappaCoeff]
    positivity
  let switchRoot : ℝ := Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2)
  have hswitchRoot : 0 < switchRoot := by
    dsimp [switchRoot]
    positivity
  let qScale : ℝ :=
    1 + 96 * deltaUpper * switchRoot / kappaCoeff
  have hqScale : 0 < qScale := by
    dsimp [qScale]
    positivity
  have hswitchRisk :
      deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
          qScale / kappaCoeff ≤ 1 / 96 := by
    have hk : 0 < kappaCoeff := hkappaCoeff
    have hq : 0 < qScale := hqScale
    have hroot : Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) = switchRoot := rfl
    rw [hroot]
    have hqLower : 96 * deltaUpper * switchRoot / kappaCoeff ≤ qScale := by
      dsimp [qScale]
      linarith
    have hscaled : 96 * deltaUpper * switchRoot ≤ qScale * kappaCoeff :=
      (div_le_iff₀ hk).1 (by simpa only [mul_div_assoc] using hqLower)
    rw [div_le_iff₀ hk, div_le_iff₀ hq]
    nlinarith
  let switchSize : ℝ := qScale * switchRoot + sigmaCoeff
  have hswitchSize : 0 < switchSize := by dsimp [switchSize]; positivity
  let mCoeff : ℝ := lambdaCoeff / (4 * switchSize)
  have hmCoeff : 0 < mCoeff := by dsimp [mCoeff]; positivity
  let badGeomCoeff : ℝ := mCoeff / 8
  let badCollisionCoeff : ℝ := mCoeff / 8
  have hbadGeomCoeff : 0 < badGeomCoeff := by
    dsimp [badGeomCoeff]
    positivity
  have hbadCollisionCoeff : 0 < badCollisionCoeff := by
    dsimp [badCollisionCoeff]
    positivity
  obtain ⟨qGeom, hqGeom, hgeomTail⟩ :=
    exists_gaussianTail_le
      (A := 2 * deltaUpper / badGeomCoeff) (b := 32)
      (epsilon := 1 / 48) (by positivity) (by norm_num) (by norm_num)
  let collisionNumerator : ℝ :=
    deltaUpper * (a₀ ^ 2 / 16) *
      AntiConcentration.variancePointMassConstant cBalance
        (innerTheta ^ 2 / 4) K
  have hcollisionNumerator : 0 < collisionNumerator := by
    dsimp [collisionNumerator]
    have hvar := AntiConcentration.variancePointMassConstant_pos
      hcBalance (by positivity : 0 < innerTheta ^ 2 / 4) hK
    positivity
  let energyCoeff : ℝ :=
    1 + 96 * collisionNumerator / badCollisionCoeff
  have henergyCoeff : 0 < energyCoeff := by
    dsimp [energyCoeff]
    positivity
  have hcollisionRisk : collisionNumerator / energyCoeff /
      badCollisionCoeff ≤ 1 / 96 := by
    have henergyLower :
        96 * collisionNumerator / badCollisionCoeff ≤ energyCoeff := by
      dsimp [energyCoeff]
      linarith
    have hscaled : 96 * collisionNumerator ≤
        energyCoeff * badCollisionCoeff :=
      (div_le_iff₀ hbadCollisionCoeff).1
        (by simpa only [mul_div_assoc] using henergyLower)
    rw [div_le_iff₀ hbadCollisionCoeff, div_le_iff₀ henergyCoeff]
    nlinarith
  let pieceCoeff : ℝ :=
    (a₀ / 16 - badDegreeCoeff) ^ 2 /
      (2 * (a₀ / 4 + 2 * energyCoeff))
  have hpieceCoeff : 0 < pieceCoeff := by
    have hdiff : 0 < a₀ / 16 - badDegreeCoeff := by
      dsimp [badDegreeCoeff]
      linarith
    dsimp only [pieceCoeff]
    exact div_pos (sq_pos_of_pos hdiff) (by positivity)
  let outputGap : ℝ := mCoeff - badGeomCoeff - badCollisionCoeff
  have houtputGap : 0 < outputGap := by
    dsimp [outputGap, badGeomCoeff, badCollisionCoeff]
    linarith [hmCoeff]
  let outputCoeff : ℝ := outputGap * pieceCoeff / 4
  have houtputCoeff : 0 < outputCoeff := by
    dsimp [outputCoeff]
    positivity
  let a₂ : ℝ := outputCoeff / (4 * (deltaUpper + 1))
  have ha₂ : 0 < a₂ := by
    dsimp [a₂]
    positivity
  let globalCoeff : ℝ :=
    ((K : ℝ) * deltaUpper) ^ 2 + deltaUpper * windowCoeff +
      qGeom * K * deltaUpper + deltaUpper * Qpartial / 2 +
      ((K : ℝ) ^ 2 * deltaUpper + windowCoeff + qDegree + Qpartial / 2)
  have hglobalCoeff : 0 ≤ globalCoeff := by
    dsimp [globalCoeff]
    positivity
  refine ⟨{
    innerTheta := innerTheta
    qGeom := qGeom
    badGeomCoeff := badGeomCoeff
    sigmaCoeff := sigmaCoeff
    globalCoeff := globalCoeff
    qDegree := qDegree
    meanRadius := meanRadius
    lambdaCoeff := lambdaCoeff
    mCoeff := mCoeff
    energyCoeff := energyCoeff
    qScale := qScale
    kappaCoeff := kappaCoeff
    badCollisionCoeff := badCollisionCoeff
    badDegreeCoeff := badDegreeCoeff
    pieceCoeff := pieceCoeff
    outputCoeff := outputCoeff
    a₂ := a₂
    a₂_pos := ha₂
    bounds := ?_ }⟩
  refine {
    K_pos := hK
    a₀_pos := ha₀
    theta_pos := htheta
    Qpartial_pos := hQpartial
    gapCoeff_pos := hgapCoeff
    cBalance_pos := hcBalance
    cBalance_le_half := hcBalanceHalf
    innerTheta_pos := hinnerTheta
    qGeom_nonneg := hqGeom.le
    badGeomCoeff_pos := hbadGeomCoeff
    sigmaCoeff_pos := hsigmaCoeff
    globalCoeff_nonneg := hglobalCoeff
    qDegree_pos := hqDegree
    meanRadius_nonneg := hmeanRadius.le
    lambdaCoeff_nonneg := hlambdaCoeff.le
    mCoeff_pos := hmCoeff
    energyCoeff_pos := henergyCoeff
    qScale_pos := hqScale
    kappaCoeff_pos := hkappaCoeff
    badCollisionCoeff_pos := hbadCollisionCoeff
    badDegreeCoeff_pos := hbadDegreeCoeff
    pieceCoeff_pos := hpieceCoeff
    outputCoeff_pos := houtputCoeff
    a₂_nonneg := ha₂.le
    deltaLower_pos := hdeltaLower
    deltaUpper_nonneg := hdeltaUpper.le
    windowCoeff_nonneg := hwindowCoeff
    diversity_coeff := ?_
    step_coeff := ?_
    endpoint_coeff := ?_
    inner_coeff := ?_
    geometric_risk_coeff := ?_
    global_coeff := ?_
    switching_coeff := ?_
    survivor_coeff := ?_
    piece_coeff := ?_
    output_gap_coeff := ?_
    output_coeff := ?_
    output_scale_coeff := ?_
    risk_coeff := ?_ }
  · dsimp [innerTheta]
    linarith
  · dsimp [meanRadius]
    exact le_rfl
  · dsimp [lambdaCoeff, endpointGap]
    nlinarith
  · dsimp [sigmaCoeff]
    linarith
  · have h := hgeomTail
    calc
      deltaUpper * (2 * Real.exp (-(qGeom ^ 2 / 32))) / badGeomCoeff =
          (2 * deltaUpper / badGeomCoeff) *
            Real.exp (-(qGeom ^ 2 / 32)) := by ring
      _ ≤ 1 / 48 := h
  · exact le_rfl
  · have hswitchExact : mCoeff *
        (qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) + sigmaCoeff) =
          lambdaCoeff / 4 := by
      rw [show Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) = switchRoot from rfl]
      dsimp [mCoeff, switchSize]
      field_simp
    dsimp [kappaCoeff]
    rw [hswitchExact]
    linarith [hlambdaCoeff]
  · dsimp [badDegreeCoeff]
    linarith [ha₀]
  · dsimp only [pieceCoeff]
    have hden : 0 < a₀ / 4 + 2 * energyCoeff := by positivity
    have heq :
        (a₀ / 16 - badDegreeCoeff) ^ 2 /
              (2 * (a₀ / 4 + 2 * energyCoeff)) *
            (a₀ / 4 + 2 * energyCoeff) =
          (a₀ / 16 - badDegreeCoeff) ^ 2 / 2 := by
      field_simp
    rw [heq]
    linarith only [sq_nonneg (a₀ / 16 - badDegreeCoeff)]
  · dsimp [badGeomCoeff, badCollisionCoeff]
    linarith [hmCoeff]
  · change outputGap * pieceCoeff / 4 ≤ outputGap * pieceCoeff / 2
    have hprod : 0 ≤ outputGap * pieceCoeff :=
      mul_nonneg houtputGap.le hpieceCoeff.le
    linarith only [hprod]
  · dsimp [a₂]
    exact chosen_outputScale houtputCoeff.le hdeltaUpper.le
  · have hdegreeRisk :
        (a₀ / 4) *
            (2 * Real.exp (-(qDegree ^ 2 /
              (32 * (K : ℝ) ^ 2)))) / badDegreeCoeff ≤ 1 / 96 := by
      have htail := hdegreeTail
      dsimp [badDegreeCoeff]
      exact chosen_degreeRisk ha₀ htail
    change
      deltaUpper * (a₀ ^ 2 / 16) *
            AntiConcentration.variancePointMassConstant cBalance
              (innerTheta ^ 2 / 4) K /
            energyCoeff / badCollisionCoeff ≤ 1 / 96 at hcollisionRisk
    linarith only [hcollisionRisk, hdegreeRisk, hswitchRisk]

end

end AugmentationInnerScales
end Erdos636
