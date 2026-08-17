/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.AugmentationScales
import ErdosProblems.Erdos636.AugmentationExposureCrowdFinal
import ErdosProblems.Erdos636.AugmentationInnerScalesRounding

/-!
# Final numerical scales for the inner full exposure

This file closes the numerical bookkeeping between the generalized partial
exposure and the scalar-only crowded-path full exposure.  All integer
parameters are explicit floors.  The only graph-dependent constant appearing
in the probability budget is the already-defined variance point-mass
constant; there are no graph-valued callbacks in this module.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationInnerScales

noncomputable section

open AsymptoticThresholds
open AugmentationExposureAssembly
open AugmentationExposureCrowdFinal

/-- Number of separated intervals retained in the inner switching path. -/
def exposureSteps (mCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊mCoeff * Real.sqrt nD⌋₊

/-- Deletion-degree cutoff for a single candidate cell. -/
def candidateDegreeThreshold (qDegree : ℝ) (nD : ℕ) : ℝ :=
  qDegree * Real.sqrt nD

/-- Linear endpoint rise reserved for the inner switching argument. -/
def exposureLambda (lambdaCoeff : ℝ) (nD : ℕ) : ℝ :=
  lambdaCoeff * nD

/-- Collision energy threshold. -/
def collisionThreshold (energyCoeff : ℝ) (nD : ℕ) : ℝ :=
  energyCoeff * Real.sqrt nD

/-- Linear Markov cutoff for the accumulated switching error. -/
def switchingCutoff (kappaCoeff : ℝ) (nD : ℕ) : ℝ :=
  kappaCoeff * nD

/-- Allowed number of candidate-collision failures. -/
def collisionBadBudget (badCollisionCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊badCollisionCoeff * Real.sqrt nD⌋₊

/-- Allowed number of candidate deletion-degree failures. -/
def degreeBadBudget (badDegreeCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊badDegreeCoeff * Real.sqrt nD⌋₊

/-- Integer collision-energy budget. -/
def collisionEdgeBudget (energyCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊energyCoeff * Real.sqrt nD⌋₊

/-- Size of every retained collision-free candidate piece. -/
def exposurePiece (pieceCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊pieceCoeff * Real.sqrt nD⌋₊

/-- Total number of inner edge counts kept at one outer state. -/
def exposureOutput (outputCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊outputCoeff * nD⌋₊

/-- The partial diversity deviation used in the final assembly.  With this
choice the surviving partial diversity is exactly `theta * nD`. -/
def diversityDeviation (theta : ℝ) (nD : ℕ) : ℝ :=
  theta * nD

/-- Coefficient comparisons which are independent of the branch order.  They
are deliberately strict only where a floor loses an additive constant. -/
structure InnerExposureCoefficientBounds
    (K : ℕ)
    (a₀ theta Qpartial gapCoeff cBalance innerTheta qGeom badGeomCoeff
      sigmaCoeff globalCoeff qDegree meanRadius lambdaCoeff mCoeff energyCoeff
      qScale kappaCoeff badCollisionCoeff badDegreeCoeff pieceCoeff outputCoeff
      a₂ deltaLower deltaUpper windowCoeff : ℝ) : Prop where
  K_pos : 0 < K
  a₀_pos : 0 < a₀
  theta_pos : 0 < theta
  Qpartial_pos : 0 < Qpartial
  gapCoeff_pos : 0 < gapCoeff
  cBalance_pos : 0 < cBalance
  cBalance_le_half : cBalance ≤ 1 / 2
  innerTheta_pos : 0 < innerTheta
  qGeom_nonneg : 0 ≤ qGeom
  badGeomCoeff_pos : 0 < badGeomCoeff
  sigmaCoeff_pos : 0 < sigmaCoeff
  globalCoeff_nonneg : 0 ≤ globalCoeff
  qDegree_pos : 0 < qDegree
  meanRadius_nonneg : 0 ≤ meanRadius
  lambdaCoeff_nonneg : 0 ≤ lambdaCoeff
  mCoeff_pos : 0 < mCoeff
  energyCoeff_pos : 0 < energyCoeff
  qScale_pos : 0 < qScale
  kappaCoeff_pos : 0 < kappaCoeff
  badCollisionCoeff_pos : 0 < badCollisionCoeff
  badDegreeCoeff_pos : 0 < badDegreeCoeff
  pieceCoeff_pos : 0 < pieceCoeff
  outputCoeff_pos : 0 < outputCoeff
  a₂_nonneg : 0 ≤ a₂
  deltaLower_pos : 0 < deltaLower
  deltaUpper_nonneg : 0 ≤ deltaUpper
  windowCoeff_nonneg : 0 ≤ windowCoeff
  diversity_coeff : 2 * innerTheta ≤ theta
  step_coeff :
    2 * windowCoeff + (K : ℝ) ^ 2 * deltaUpper + Qpartial ≤ meanRadius
  endpoint_coeff :
    lambdaCoeff + ((K : ℝ) * deltaUpper) ^ 2 +
        2 * deltaUpper * windowCoeff ≤ deltaLower * gapCoeff / 4
  inner_coeff :
    2 * ((K : ℝ) ^ 2 * deltaUpper + windowCoeff + qDegree +
        Qpartial / 2) < sigmaCoeff
  geometric_risk_coeff :
    deltaUpper * (2 * Real.exp (-(qGeom ^ 2 / 32))) / badGeomCoeff ≤
      1 / 48
  global_coeff :
    ((K : ℝ) * deltaUpper) ^ 2 + deltaUpper * windowCoeff +
        qGeom * K * deltaUpper + deltaUpper * Qpartial / 2 +
        ((K : ℝ) ^ 2 * deltaUpper + windowCoeff + qDegree +
          Qpartial / 2) ≤ globalCoeff
  switching_coeff :
    mCoeff *
        (qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) + sigmaCoeff) +
      kappaCoeff ≤ lambdaCoeff
  survivor_coeff : badDegreeCoeff < a₀ / 16
  piece_coeff :
    pieceCoeff * (a₀ / 4 + 2 * energyCoeff) ≤
      (a₀ / 16 - badDegreeCoeff) ^ 2
  output_gap_coeff : badGeomCoeff + badCollisionCoeff < mCoeff
  output_coeff :
    outputCoeff ≤
      (mCoeff - badGeomCoeff - badCollisionCoeff) * pieceCoeff / 2
  output_scale_coeff : 2 * a₂ * deltaUpper ≤ outputCoeff
  risk_coeff :
    1 / 48 +
      deltaUpper * (a₀ ^ 2 / 16) *
          AntiConcentration.variancePointMassConstant cBalance
            (innerTheta ^ 2 / 4) K /
          energyCoeff / badCollisionCoeff +
      (a₀ / 4) *
          (2 * Real.exp (-(qDegree ^ 2 /
            (32 * (K : ℝ) ^ 2)))) / badDegreeCoeff +
      deltaUpper * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) /
          qScale / kappaCoeff ≤ 1 / 6

lemma graphDegreeRisk_candidateDegreeThreshold
    {K nD : ℕ} {qDegree : ℝ}
    (hK : 0 < K) (hnD : 0 < nD) :
    AugmentationGraphFull.graphDegreeRisk
        (candidateDegreeThreshold qDegree nD) nD K =
      2 * Real.exp (-(qDegree ^ 2 / (32 * (K : ℝ) ^ 2))) := by
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hnDne : (nD : ℝ) ≠ 0 := by exact_mod_cast hnD.ne'
  have hsqrtSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt (by positivity)
  simp only [AugmentationGraphFull.graphDegreeRisk, candidateDegreeThreshold]
  congr 2
  congr 1
  rw [show (qDegree * Real.sqrt nD) ^ 2 =
      qDegree ^ 2 * (Real.sqrt nD) ^ 2 by ring, hsqrtSq]
  field_simp
  ring

lemma sqrt_graphSwitchVariance
    {K nD : ℕ} {meanRadius : ℝ} (hnD : 0 < nD) :
    Real.sqrt (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) =
      Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) * Real.sqrt nD := by
  rw [AugmentationGraphFull.graphSwitchVariance]
  exact Real.sqrt_mul (by positivity) _

/-- The literal four-term failure sum for the chosen inner scales. -/
def exposureRisk (K nD nZ nS : ℕ)
    (a₀ cBalance innerTheta qGeom badGeomCoeff qDegree meanRadius
      energyCoeff qScale kappaCoeff badCollisionCoeff badDegreeCoeff : ℝ) : ℝ :=
  (nS + 1 : ℕ) *
      AugmentationGraphFull.graphDegreeRisk
        (AugmentationScales.geometricThreshold qGeom K nS nD)
        nD (K * nS) /
        (AugmentationScales.geometricBadBudget badGeomCoeff nD + 1 : ℕ) +
    (nS + 1 : ℕ) * (partialMatchingSize a₀ nD).choose 2 *
        (AntiConcentration.variancePointMassConstant cBalance
            (innerTheta ^ 2 / 4) K /
          Real.sqrt (((2 * nD : ℕ) : ℝ))) /
        collisionThreshold energyCoeff nD /
        (collisionBadBudget badCollisionCoeff nD + 1 : ℕ) +
    partialMatchingSize a₀ nD *
        AugmentationGraphFull.graphDegreeRisk
          (candidateDegreeThreshold qDegree nD) nD K /
        (degreeBadBudget badDegreeCoeff nD + 1 : ℕ) +
    (nS *
        (Real.sqrt
          (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
            qScale)) /
        switchingCutoff kappaCoeff nD

/-- The concrete scalar conclusions consumed by
`CrowdLargeNumericBounds`.  The record also retains the two estimates needed
after the probability theorem: the common radius is linear in `nD`, and the
output has the required `nZ * sqrt nD` size. -/
structure InnerExposureFinalBounds
    (K nD nZ nS degreeWindow : ℕ)
    (a₀ theta Qpartial LH gapCoeff cBalance innerTheta degreeRadius : ℝ)
    (qGeom badGeomCoeff sigmaCoeff globalCoeff qDegree meanRadius
      lambdaCoeff mCoeff energyCoeff qScale kappaCoeff badCollisionCoeff
      badDegreeCoeff pieceCoeff outputCoeff a₂ : ℝ) : Prop where
  nS_pos : 0 < nS
  nZ_eq : nS + 1 = nZ
  partial_thresholds :
    AugmentationScales.partialDegreeThreshold a₀ nD ≤
        (AugmentationScales.partialBadBudget a₀ nD : ℝ) + 1 ∧
      AugmentationScales.partialCollisionThreshold LH nD ≤
        (AugmentationScales.partialSelectionEdgeBudget LH nD : ℝ) + 1
  selection_turan :
    (2 * nS + AugmentationScales.partialSelectionGap gapCoeff nD + 1) *
        (partialMatchingSize a₀ nD -
            AugmentationScales.partialBadBudget a₀ nD +
          2 * AugmentationScales.partialSelectionEdgeBudget LH nD) <
      (partialMatchingSize a₀ nD -
        AugmentationScales.partialBadBudget a₀ nD) ^ 2
  cBalance_pos : 0 < cBalance
  cBalance_le_half : cBalance ≤ 1 / 2
  innerTheta_pos : 0 < innerTheta
  diversity_scale :
    innerTheta * ((2 * nD : ℕ) : ℝ) ≤
      partialDiversityThreshold nD theta (diversityDeviation theta nD)
  small_degree_window : 2 * degreeRadius < innerTheta * nD
  geometry : AugmentationScales.ExposureGeometryBounds K nD nZ nS
    degreeWindow (candidateDegreeThreshold qDegree nD) degreeRadius qGeom
    badGeomCoeff sigmaCoeff globalCoeff (1 / 48)
  degreeThreshold_nonneg : 0 ≤ candidateDegreeThreshold qDegree nD
  meanRadius_nonneg : 0 ≤ meanRadius
  qScale_pos : 0 < qScale
  kappa_pos : 0 < switchingCutoff kappaCoeff nD
  energy_pos : 0 < collisionThreshold energyCoeff nD
  step_mean_bound :
    (2 * degreeWindow : ℝ) + (K ^ 2 * nS : ℕ) + degreeRadius ≤
      meanRadius * Real.sqrt nD
  endpoint_rise_bound :
    exposureLambda lambdaCoeff nD + (((K * nS) ^ 2 : ℕ) : ℝ) +
        2 * (nS : ℝ) * degreeWindow ≤
      (nS : ℝ) *
        (AugmentationScales.partialSelectionGap gapCoeff nD + 1 : ℕ) / 2
  steps_pos : 1 ≤ exposureSteps mCoeff nD
  switching_budget :
    (exposureSteps mCoeff nD : ℝ) *
        (qScale * Real.sqrt
            (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) +
          AugmentationScales.innerExposureSigma sigmaCoeff nD) +
      switchingCutoff kappaCoeff nD ≤ exposureLambda lambdaCoeff nD
  collision_budget :
    collisionThreshold energyCoeff nD ≤ collisionEdgeBudget energyCoeff nD + 1
  candidate_survivors :
    degreeBadBudget badDegreeCoeff nD <
      partialMatchingSize a₀ nD -
        AugmentationScales.partialBadBudget a₀ nD
  piece_bound :
    exposurePiece pieceCoeff nD *
        (partialMatchingSize a₀ nD +
          2 * collisionEdgeBudget energyCoeff nD) ≤
      (partialMatchingSize a₀ nD -
          AugmentationScales.partialBadBudget a₀ nD -
          degreeBadBudget badDegreeCoeff nD) ^ 2
  output_bound :
    exposureOutput outputCoeff nD ≤
      ((exposureSteps mCoeff nD + 1) -
          (AugmentationScales.geometricBadBudget badGeomCoeff nD +
            collisionBadBudget badCollisionCoeff nD)) *
        exposurePiece pieceCoeff nD
  risk_budget :
    exposureRisk K nD nZ nS a₀ cBalance innerTheta qGeom badGeomCoeff
      qDegree meanRadius energyCoeff qScale kappaCoeff badCollisionCoeff
      badDegreeCoeff ≤ 1 / 6
  global_radius_scale :
    AugmentationScales.exposureGlobalRadius globalCoeff nD ≤ globalCoeff * nD
  output_scale :
    a₂ * nZ * Real.sqrt nD ≤ exposureOutput outputCoeff nD

/-- Forget the coefficient bookkeeping and obtain exactly the scalar record
used by the graph-facing crowded-path theorem. -/
theorem InnerExposureFinalBounds.toCrowdLargeNumericBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : ℕ}
    {path : OuterSwitchingPath.CrowdedPath S mu degreeWindow}
    {time nD nZ nS : ℕ}
    {a₀ theta Qpartial LH gapCoeff cBalance innerTheta degreeRadius : ℝ}
    {qGeom badGeomCoeff sigmaCoeff globalCoeff qDegree meanRadius
      lambdaCoeff mCoeff energyCoeff qScale kappaCoeff badCollisionCoeff
      badDegreeCoeff pieceCoeff outputCoeff a₂ : ℝ}
    (H : InnerExposureFinalBounds K nD nZ nS degreeWindow a₀ theta
      Qpartial LH gapCoeff cBalance innerTheta degreeRadius qGeom badGeomCoeff
      sigmaCoeff globalCoeff qDegree meanRadius lambdaCoeff mCoeff energyCoeff
      qScale kappaCoeff badCollisionCoeff badDegreeCoeff pieceCoeff outputCoeff
      a₂) :
    CrowdLargeNumericBounds S path time nD nS nZ
      (partialMatchingSize a₀ nD)
      (AugmentationScales.partialSelectionGap gapCoeff nD)
      (AugmentationScales.partialBadBudget a₀ nD)
      (AugmentationScales.partialSelectionEdgeBudget LH nD)
      (exposureSteps mCoeff nD) cBalance theta
      (diversityDeviation theta nD) degreeRadius
      (AugmentationScales.partialDegreeThreshold a₀ nD)
      (AugmentationScales.partialDegreeThreshold a₀ nD)
      (AugmentationScales.partialCollisionThreshold LH nD)
      innerTheta (AugmentationScales.geometricThreshold qGeom K nS nD)
      (candidateDegreeThreshold qDegree nD) meanRadius
      (exposureLambda lambdaCoeff nD) (collisionThreshold energyCoeff nD)
      qScale (switchingCutoff kappaCoeff nD)
      (AugmentationScales.innerExposureSigma sigmaCoeff nD)
      (AugmentationScales.innerExposureRadius K nS degreeWindow
        (candidateDegreeThreshold qDegree nD) degreeRadius)
      (AugmentationScales.exposureGlobalRadius globalCoeff nD)
      (AugmentationScales.geometricBadBudget badGeomCoeff nD)
      (collisionBadBudget badCollisionCoeff nD)
      (degreeBadBudget badDegreeCoeff nD)
      (collisionEdgeBudget energyCoeff nD)
      (exposurePiece pieceCoeff nD) (exposureOutput outputCoeff nD) := by
  refine {
    nS_pos := H.nS_pos
    nZ_eq := H.nZ_eq
    tS_budget := H.partial_thresholds.1
    tX_budget := H.partial_thresholds.1
    selection_collision_budget := H.partial_thresholds.2
    selection_turan := H.selection_turan
    innerTheta_pos := H.innerTheta_pos
    diversity_scale := H.diversity_scale
    small_degree_window := by
      push_cast
      convert H.small_degree_window using 1 <;> ring
    geometricThreshold_nonneg := H.geometry.geometricThreshold_nonneg
    degreeThreshold_nonneg := H.degreeThreshold_nonneg
    meanRadius_nonneg := H.meanRadius_nonneg
    qScale_pos := H.qScale_pos
    kappa_pos := H.kappa_pos
    E_pos := H.energy_pos
    step_mean_bound := H.step_mean_bound
    endpoint_rise_bound := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_mul]
        using H.endpoint_rise_bound
    literal_radius_bound := by
      dsimp only [AugmentationScales.innerExposureRadius]
      push_cast
      exact le_rfl
    global_radius_bound := H.geometry.global_radius
    m_pos := H.steps_pos
    sigma_pos := H.geometry.innerSigma_pos
    R_small := H.geometry.innerRadius_small
    switching_budget := H.switching_budget
    collision_budget := H.collision_budget
    candidate_survivors := H.candidate_survivors
    piece_bound := H.piece_bound
    output_bound := H.output_bound
    risk_budget := ?_ }
  simpa only [exposureRisk, div_eq_mul_inv, mul_assoc] using H.risk_budget

/-- Pointwise constructor once the finitely many floor lower bounds have been
made explicit.  The eventual theorem below supplies all of them from one
threshold. -/
lemma innerExposureFinalBounds_of_rounding
    {K n nD nZ nS degreeWindow ambient : ℕ}
    {a₀ theta Qpartial Cpartial LH c₀ gapCoeff cBalance innerTheta qGeom
      badGeomCoeff sigmaCoeff globalCoeff qDegree meanRadius lambdaCoeff
      mCoeff energyCoeff qScale kappaCoeff badCollisionCoeff badDegreeCoeff
      pieceCoeff outputCoeff a₂ deltaLower deltaUpper windowCoeff : ℝ}
    (H : InnerExposureCoefficientBounds K a₀ theta Qpartial gapCoeff
      cBalance innerTheta qGeom badGeomCoeff sigmaCoeff globalCoeff qDegree
      meanRadius lambdaCoeff mCoeff energyCoeff qScale kappaCoeff
      badCollisionCoeff badDegreeCoeff pieceCoeff outputCoeff a₂ deltaLower
      deltaUpper windowCoeff)
    (P : AugmentationScales.PartialExposureFinalBounds K n nD nZ nS ambient
      a₀ theta Qpartial Cpartial LH c₀ deltaUpper gapCoeff)
    (hnD : 0 < nD) (hnS : nS + 1 = nZ)
    (hnZLower : deltaLower * Real.sqrt nD ≤ (nZ : ℝ))
    (hnZUpper : (nZ : ℝ) ≤ deltaUpper * Real.sqrt nD)
    (hdegreeWindow : (degreeWindow : ℝ) ≤
      windowCoeff * Real.sqrt nD)
    (hnSLower : deltaLower / 2 * Real.sqrt nD ≤ (nS : ℝ))
    (hsmallLarge : 4 * Qpartial ≤ innerTheta * Real.sqrt nD)
    (hstepsLower : mCoeff / 2 * Real.sqrt nD ≤
      (exposureSteps mCoeff nD : ℝ))
    (hstepsOne : 1 ≤ mCoeff / 2 * Real.sqrt nD)
    (hpieceLower : pieceCoeff / 2 * Real.sqrt nD ≤
      (exposurePiece pieceCoeff nD : ℝ))
    (houtputLower : outputCoeff / 2 * nD ≤
      (exposureOutput outputCoeff nD : ℝ))
    (hrounded :
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
      a₂ * nZ * Real.sqrt nD ≤ exposureOutput outputCoeff nD)
    (hrisk : exposureRisk K nD nZ nS a₀ cBalance innerTheta qGeom
      badGeomCoeff qDegree meanRadius energyCoeff qScale kappaCoeff
      badCollisionCoeff badDegreeCoeff ≤ 1 / 6) :
    InnerExposureFinalBounds K nD nZ nS degreeWindow a₀ theta Qpartial LH
      gapCoeff cBalance innerTheta (Qpartial * Real.sqrt nD) qGeom
      badGeomCoeff sigmaCoeff globalCoeff qDegree meanRadius lambdaCoeff
      mCoeff energyCoeff qScale kappaCoeff badCollisionCoeff badDegreeCoeff
      pieceCoeff outputCoeff a₂ := by
  have hnDreal : (0 : ℝ) < nD := by exact_mod_cast hnD
  have hsqrtPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDreal
  have hsqrtSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt hnDreal.le
  have hnSposReal : (0 : ℝ) < nS := by
    exact lt_of_lt_of_le
      (mul_pos (div_pos H.deltaLower_pos (by norm_num)) hsqrtPos) hnSLower
  have hnSpos : 0 < nS := by exact_mod_cast hnSposReal
  have hnSUpper : (nS : ℝ) ≤ deltaUpper * Real.sqrt nD := by
    have hnSle : nS ≤ nZ := by omega
    exact (by exact_mod_cast hnSle : (nS : ℝ) ≤ nZ).trans hnZUpper
  have hdegreeThresholdNonneg :
      0 ≤ candidateDegreeThreshold qDegree nD :=
    mul_nonneg H.qDegree_pos.le (Real.sqrt_nonneg _)
  have hdegreeRadiusNonneg : 0 ≤ Qpartial * Real.sqrt nD :=
    mul_nonneg H.Qpartial_pos.le (Real.sqrt_nonneg _)
  have hgeometry : AugmentationScales.ExposureGeometryBounds K nD nZ nS
      degreeWindow (candidateDegreeThreshold qDegree nD)
      (Qpartial * Real.sqrt nD) qGeom badGeomCoeff sigmaCoeff globalCoeff
      (1 / 48) :=
    AugmentationScales.exposureGeometryBounds
      (K := K) (nD := nD) (nZ := nZ) (nS := nS)
      (degreeWindow := degreeWindow)
      (degreeThreshold := candidateDegreeThreshold qDegree nD)
      (degreeRadius := Qpartial * Real.sqrt nD)
      H.K_pos hnD hnSpos hnS H.deltaUpper_nonneg hnZUpper
      H.windowCoeff_nonneg hdegreeWindow H.qDegree_pos.le
      hdegreeThresholdNonneg (by exact le_rfl) H.Qpartial_pos.le
      hdegreeRadiusNonneg (by exact le_rfl) H.qGeom_nonneg H.badGeomCoeff_pos
      H.sigmaCoeff_pos H.inner_coeff H.geometric_risk_coeff H.global_coeff
  refine {
    nS_pos := hnSpos
    nZ_eq := hnS
    partial_thresholds :=
      ⟨P.risk.degreeThreshold_le_badBudget,
        P.risk.collisionThreshold_le_edgeBudget⟩
    selection_turan := P.selection_turan
    cBalance_pos := H.cBalance_pos
    cBalance_le_half := H.cBalance_le_half
    innerTheta_pos := H.innerTheta_pos
    diversity_scale := ?_
    small_degree_window := ?_
    geometry := hgeometry
    degreeThreshold_nonneg := hdegreeThresholdNonneg
    meanRadius_nonneg := H.meanRadius_nonneg
    qScale_pos := H.qScale_pos
    kappa_pos := by
      dsimp only [switchingCutoff]
      exact mul_pos H.kappaCoeff_pos hnDreal
    energy_pos := by
      dsimp only [collisionThreshold]
      exact mul_pos H.energyCoeff_pos hsqrtPos
    step_mean_bound := ?_
    endpoint_rise_bound := ?_
    steps_pos := ?_
    switching_budget := ?_
    collision_budget := ?_
    candidate_survivors := hrounded.1
    piece_bound := hrounded.2.1
    output_bound := hrounded.2.2.1
    risk_budget := hrisk
    global_radius_scale := by rfl
    output_scale := hrounded.2.2.2 }
  · dsimp only [partialDiversityThreshold, diversityDeviation]
    push_cast
    have hscaled := mul_le_mul_of_nonneg_right H.diversity_coeff hnDreal.le
    nlinarith
  · have hscaled := mul_le_mul_of_nonneg_right hsmallLarge hsqrtPos.le
    have hrewrite : innerTheta * Real.sqrt nD * Real.sqrt nD =
        innerTheta * nD := by
      calc
        innerTheta * Real.sqrt nD * Real.sqrt nD =
            innerTheta * (Real.sqrt nD) ^ 2 := by ring
        _ = innerTheta * nD := by rw [hsqrtSq]
    rw [hrewrite] at hscaled
    have hQsqrt : 0 < Qpartial * Real.sqrt nD :=
      mul_pos H.Qpartial_pos hsqrtPos
    nlinarith
  · push_cast
    calc
      2 * (degreeWindow : ℝ) + (K : ℝ) ^ 2 * nS +
          Qpartial * Real.sqrt nD ≤
        2 * (windowCoeff * Real.sqrt nD) +
          (K : ℝ) ^ 2 * (deltaUpper * Real.sqrt nD) +
          Qpartial * Real.sqrt nD := by gcongr
      _ = (2 * windowCoeff + (K : ℝ) ^ 2 * deltaUpper + Qpartial) *
          Real.sqrt nD := by ring
      _ ≤ meanRadius * Real.sqrt nD := by
        exact mul_le_mul_of_nonneg_right H.step_coeff hsqrtPos.le
  · have hgapFloor : gapCoeff * Real.sqrt nD ≤
        (AugmentationScales.partialSelectionGap gapCoeff nD : ℝ) + 1 := by
      simpa only [AugmentationScales.partialSelectionGap] using
        (Nat.lt_floor_add_one (gapCoeff * Real.sqrt nD)).le
    have hright : deltaLower * gapCoeff / 4 * nD ≤
        (nS : ℝ) *
          (AugmentationScales.partialSelectionGap gapCoeff nD + 1 : ℕ) / 2 := by
      push_cast
      calc
        deltaLower * gapCoeff / 4 * (nD : ℝ) =
            (deltaLower / 2 * Real.sqrt nD) *
              (gapCoeff * Real.sqrt nD) / 2 := by
                calc
                  deltaLower * gapCoeff / 4 * (nD : ℝ) =
                      deltaLower * gapCoeff / 4 * (Real.sqrt nD) ^ 2 := by
                        rw [hsqrtSq]
                  _ = _ := by ring
        _ ≤ (nS : ℝ) *
              ((AugmentationScales.partialSelectionGap gapCoeff nD : ℝ) + 1) /
              2 := by
                exact div_le_div_of_nonneg_right
                  (mul_le_mul hnSLower hgapFloor
                    (mul_nonneg H.gapCoeff_pos.le (Real.sqrt_nonneg _))
                    (by positivity)) (by norm_num)
    have hstateSq : (((K * nS) ^ 2 : ℕ) : ℝ) ≤
        ((K : ℝ) * deltaUpper) ^ 2 * nD := by
      push_cast
      have hmul : (K : ℝ) * nS ≤
          ((K : ℝ) * deltaUpper) * Real.sqrt nD := by
        calc
          (K : ℝ) * nS ≤ (K : ℝ) *
              (deltaUpper * Real.sqrt nD) := by gcongr
          _ = ((K : ℝ) * deltaUpper) * Real.sqrt nD := by ring
      have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ K * nS) hmul
      calc
        ((K : ℝ) * nS) ^ 2 ≤
            (((K : ℝ) * deltaUpper) * Real.sqrt nD) ^ 2 := by
              simpa only [pow_two] using hsq
        _ = ((K : ℝ) * deltaUpper) ^ 2 * nD := by
          rw [mul_pow, hsqrtSq]
    have hwindowTerm : 2 * (nS : ℝ) * degreeWindow ≤
        (2 * deltaUpper * windowCoeff) * nD := by
      have hproduct : (nS : ℝ) * degreeWindow ≤
          (deltaUpper * Real.sqrt nD) *
            (windowCoeff * Real.sqrt nD) :=
        mul_le_mul hnSUpper hdegreeWindow (by positivity)
          (mul_nonneg H.deltaUpper_nonneg (Real.sqrt_nonneg _))
      calc
        2 * (nS : ℝ) * degreeWindow ≤
            2 * (deltaUpper * Real.sqrt nD) *
              (windowCoeff * Real.sqrt nD) := by nlinarith
        _ = (2 * deltaUpper * windowCoeff) * nD := by
          calc
            2 * (deltaUpper * Real.sqrt nD) *
                (windowCoeff * Real.sqrt nD) =
              (2 * deltaUpper * windowCoeff) * (Real.sqrt nD) ^ 2 := by ring
            _ = _ := by rw [hsqrtSq]
    have hleft : exposureLambda lambdaCoeff nD +
          (((K * nS) ^ 2 : ℕ) : ℝ) + 2 * (nS : ℝ) * degreeWindow ≤
        (lambdaCoeff + ((K : ℝ) * deltaUpper) ^ 2 +
          2 * deltaUpper * windowCoeff) * nD := by
      dsimp only [exposureLambda]
      nlinarith
    exact hleft.trans ((mul_le_mul_of_nonneg_right H.endpoint_coeff
      hnDreal.le).trans hright)
  · have hreal : (1 : ℝ) ≤ exposureSteps mCoeff nD :=
      hstepsOne.trans hstepsLower
    exact_mod_cast hreal
  · have hmUpper : (exposureSteps mCoeff nD : ℝ) ≤
        mCoeff * Real.sqrt nD := by
      exact Nat.floor_le (mul_nonneg H.mCoeff_pos.le (Real.sqrt_nonneg _))
    rw [sqrt_graphSwitchVariance hnD]
    dsimp only [AugmentationScales.innerExposureSigma, switchingCutoff,
      exposureLambda]
    have hfirst : (exposureSteps mCoeff nD : ℝ) *
          (qScale *
              (Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) * Real.sqrt nD) +
            sigmaCoeff * Real.sqrt nD) ≤
        (mCoeff *
          (qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) +
            sigmaCoeff)) * nD := by
      have hfactorNonneg : 0 ≤
          (qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) + sigmaCoeff) *
            Real.sqrt nD :=
        mul_nonneg
          (add_nonneg
            (mul_nonneg H.qScale_pos.le (Real.sqrt_nonneg _))
            H.sigmaCoeff_pos.le) hsqrtPos.le
      calc
        (exposureSteps mCoeff nD : ℝ) *
            (qScale *
                (Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) * Real.sqrt nD) +
              sigmaCoeff * Real.sqrt nD) ≤
          (mCoeff * Real.sqrt nD) *
            ((qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) +
              sigmaCoeff) * Real.sqrt nD) := by
                have hfactorEq :
                    qScale *
                        (Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) *
                          Real.sqrt nD) + sigmaCoeff * Real.sqrt nD =
                    (qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) +
                      sigmaCoeff) * Real.sqrt nD := by ring
                rw [hfactorEq]
                exact mul_le_mul_of_nonneg_right hmUpper hfactorNonneg
        _ = (mCoeff *
            (qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) +
              sigmaCoeff)) * nD := by
                calc
                  (mCoeff * Real.sqrt nD) *
                      ((qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) +
                        sigmaCoeff) * Real.sqrt nD) =
                    (mCoeff *
                      (qScale * Real.sqrt ((K : ℝ) ^ 2 + meanRadius ^ 2) +
                        sigmaCoeff)) * (Real.sqrt nD) ^ 2 := by ring
                  _ = _ := by rw [hsqrtSq]
    have hcoeff := mul_le_mul_of_nonneg_right H.switching_coeff hnDreal.le
    nlinarith
  · have hfloor := Nat.lt_floor_add_one (energyCoeff * Real.sqrt nD)
    dsimp only [collisionThreshold, collisionEdgeBudget]
    linarith

end

end AugmentationInnerScales
end Erdos636
