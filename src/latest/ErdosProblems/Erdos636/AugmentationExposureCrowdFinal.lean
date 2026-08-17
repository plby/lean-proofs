/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.AugmentationExposureScalar
import ErdosProblems.Erdos636.AugmentationExposureStepBounds
import ErdosProblems.Erdos636.AugmentationExposureEndpointBounds
import ErdosProblems.Erdos636.AugmentationExposureWindowBounds

/-!
# Closed finite exposure theorem on a crowded path

This module is the final finite interface for the large-state branch.  Its
numeric record is uniform in the intermediate reservoir and in the selected
switching data.  All graph-valued fields of the full-exposure certificate are
proved internally from `PartialGood`, the crowded path, and the selected
high-to-low path.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationExposureCrowdFinal

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open AugmentationExposureAssembly
open AugmentationExposureCrowd
open AugmentationExposureScalar

/-- Scalar hypotheses for one large-state crowded exposure.  Every field is
independent of the intermediate `2*nD` reservoir and of the switching data
selected from it. -/
structure CrowdLargeNumericBounds
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ)
    (nD nS nZ s0 gap badBudget selectionEdgeBudget m : ℕ)
    (c theta divDev degreeDev tS tX tCollision : ℝ)
    (innerTheta geometricThreshold degreeThreshold meanRadius lam E qScale
      kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ) : Prop where
  nS_pos : 0 < nS
  nZ_eq : nS + 1 = nZ
  tS_budget : tS ≤ (badBudget : ℝ) + 1
  tX_budget : tX ≤ (badBudget : ℝ) + 1
  selection_collision_budget :
    tCollision ≤ (selectionEdgeBudget : ℝ) + 1
  selection_turan :
    (2 * nS + gap + 1) *
        (s0 - badBudget + 2 * selectionEdgeBudget) <
      (s0 - badBudget) ^ 2
  innerTheta_pos : 0 < innerTheta
  diversity_scale :
    innerTheta * ((2 * nD : ℕ) : ℝ) ≤
      partialDiversityThreshold nD theta divDev
  small_degree_window :
    2 * degreeDev < innerTheta / 2 * ((2 * nD : ℕ) : ℝ)
  geometricThreshold_nonneg : 0 ≤ geometricThreshold
  degreeThreshold_nonneg : 0 ≤ degreeThreshold
  meanRadius_nonneg : 0 ≤ meanRadius
  qScale_pos : 0 < qScale
  kappa_pos : 0 < kappa
  E_pos : 0 < E
  step_mean_bound :
    (2 * degreeWindow : ℝ) + (K ^ 2 * nS : ℕ) + degreeDev ≤
      meanRadius * Real.sqrt nD
  endpoint_rise_bound :
    lam + (((K * nS) ^ 2 : ℕ) : ℝ) +
        2 * (nS : ℝ) * degreeWindow ≤
      (nS : ℝ) * (gap + 1 : ℝ) / 2
  literal_radius_bound :
    (K ^ 2 * (nS + 1) : ℕ) + degreeWindow + degreeThreshold +
        degreeDev / 2 ≤ R
  global_radius_bound :
    (K * nS : ℕ) ^ 2 + nS * degreeWindow + geometricThreshold +
        nS * degreeDev / 2 + R ≤ globalRadius
  m_pos : 1 ≤ m
  sigma_pos : 0 < sigma
  R_small : 2 * R < sigma
  switching_budget :
    (m : ℝ) *
        (qScale * Real.sqrt
          (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) +
          sigma) + kappa ≤ lam
  collision_budget : E ≤ edgeBudget + 1
  candidate_survivors : badDegree < s0 - badBudget
  piece_bound :
    piece * (s0 + 2 * edgeBudget) ≤
      (s0 - badBudget - badDegree) ^ 2
  output_bound : L ≤ ((m + 1) - (badGeom + badCollision)) * piece
  risk_budget :
    (nS + 1 : ℕ) *
        AugmentationGraphFull.graphDegreeRisk geometricThreshold nD (K * nS) /
          (badGeom + 1 : ℕ) +
      (nS + 1 : ℕ) *
          (s0.choose 2 *
            (AntiConcentration.variancePointMassConstant c
                (innerTheta ^ 2 / 4) K /
              Real.sqrt (((2 * nD : ℕ) : ℝ))) / E) /
            (badCollision + 1 : ℕ) +
      s0 * AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
          (badDegree + 1 : ℕ) +
      (nS *
          (Real.sqrt
            (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
              qScale)) /
          kappa ≤ 1 / 6

/-- The complete per-time large-state conclusion.  No quantified graph
callback remains: the only assumptions beyond the structural and partial
exposure certificates are the scalar fields of `CrowdLargeNumericBounds`. -/
theorem one_fourth_le_layerProbability_innerWindowGood_large_of_numeric
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW)
    (nD nS nZ s0 gap badBudget selectionEdgeBudget m : ℕ)
    (c theta divDev degreeDev tS tX tCollision : ℝ)
    (innerTheta geometricThreshold degreeThreshold meanRadius lam E qScale
      kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (P : PartialExposureCertificate G S.U0 (path.crowd time) K nD s0 S.d0
      c theta divDev degreeDev tS tX tCollision)
    (N : CrowdLargeNumericBounds S path time nD nS nZ s0 gap badBudget
      selectionEdgeBudget m c theta divDev degreeDev tS tX tCollision
      innerTheta geometricThreshold degreeThreshold meanRadius lam E qScale
      kappa sigma R globalRadius badGeom badCollision badDegree edgeBudget
      piece L) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G (path.W time) S.U0
        (path.crowd time) nZ L
        (canonicalAugmentationCenter G (path.W time) S.U0 D nZ
          (degreeInto G (path.W time) (path.anchor time)) S.d0
          (partialDegreeCenter S.U0 nD S.d0)) globalRadius D) := by
  apply one_fourth_le_layerProbability_innerWindowGood_large_at_crowdedPath
    S path time htime nD nS nZ s0 gap badBudget selectionEdgeBudget m c theta
      divDev degreeDev tS tX tCollision innerTheta geometricThreshold
      degreeThreshold meanRadius lam E qScale kappa sigma R globalRadius
      badGeom badCollision badDegree edgeBudget piece L P N.nZ_eq N.tS_budget
      N.tX_budget N.selection_collision_budget N.selection_turan
  intro D1 hD1 hpartial source rawCandidates hsource hraw hrawCard hdiverse
    selected
  have hlayer := NestedUniform.mem_layer.mp hD1
  have hhalf : D1.card = 2 * nD := hlayer.2
  have hD1 : D1 ⊆ S.U0 := hlayer.1
  let degreeCenter := partialDegreeCenter S.U0 nD S.d0
  let pathShift : ℝ :=
    (degreeInto G (path.W time) (path.anchor time) : ℝ) + S.d0 -
      degreeCenter / 2
  have hselected : c * D1.card ≤ nD := by
    rw [hhalf]
    have hc := P.c_le_half
    push_cast
    nlinarith
  have hunselected : c * D1.card ≤ D1.card - nD := by
    rw [hhalf]
    push_cast
    nlinarith [P.c_le_half]
  have hcandidateDiverse :
      ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
          degreeCenter degreeDev nS gap badBudget selected,
        ∀ y ∈ graphSelectedGoodCandidates G D1 source rawCandidates
          degreeCenter degreeDev nS gap badBudget selected, x ≠ y →
        innerTheta * D1.card ≤ incidenceDiffMass G D1 x y := by
    intro x hx y hy hxy
    have hscale : innerTheta * D1.card ≤
        partialDiversityThreshold nD theta divDev := by
      rw [hhalf]
      exact N.diversity_scale
    exact hscale.trans
      (graphSelectedGoodCandidates_diverse_of_raw G D1 source rawCandidates
        degreeCenter degreeDev (partialDiversityThreshold nD theta divDev)
        nS gap badBudget selected hdiverse x hx y hy hxy)
  have hstep :=
    AugmentationExposureStepBounds.graphSelectedStepMean_le_of_scalar
      S path time htime D1 source rawCandidates nD nS degreeCenter degreeDev
      meanRadius gap badBudget selected hsource N.step_mean_bound
  have hrise :=
    AugmentationExposureEndpointBounds.mean_rise_of_selectedReverseState
      G (path.W time) S.U0 D1 source rawCandidates (path.crowd time)
      degreeCenter degreeDev lam nS gap badBudget K S.d0 degreeWindow selected
      N.nS_pos hsource (path.crowd_pairwiseDisjoint htime)
      (fun x hx ↦ by
        rw [path.crowd_uniform htime hx]
        exact S.k_le)
      (fun x hx ↦ path.crowd_degree_U0 htime hx)
      (degreeInto G (path.W time) (path.anchor time) : ℤ)
      (fun x hx ↦ path.crowd_degree_window htime hx) N.endpoint_rise_bound
  have hliteral :=
    AugmentationExposureWindowBounds.centered_literal_window_of_radius
      S path time htime D1 source rawCandidates hsource hraw nD nS gap
      badBudget degreeCenter degreeDev degreeThreshold R selected hhalf
      P.nD_pos hD1 N.literal_radius_bound
  have hglobal :=
    AugmentationExposureWindowBounds.centered_global_window_of_crowdedPath
      S path time htime D1 source rawCandidates hsource nD nS nZ gap badBudget
      degreeCenter degreeDev geometricThreshold R globalRadius selected
      N.nZ_eq.symm hD1 N.global_radius_bound
  let B : CrowdLargeScalarBounds S path time D1 source rawCandidates nD nS m
      s0
      (fun D ↦ canonicalAugmentationCenter G (path.W time) S.U0 D nZ
        (degreeInto G (path.W time) (path.anchor time)) S.d0 degreeCenter)
      degreeCenter degreeDev c innerTheta pathShift geometricThreshold
      degreeThreshold meanRadius lam E qScale kappa sigma R globalRadius
      badGeom badCollision badDegree edgeBudget piece L gap badBudget
      selected := {
    half := hhalf
    nD_pos := P.nD_pos
    nS_pos := N.nS_pos
    c_pos := P.c_pos
    c_le_half := P.c_le_half
    theta_pos := N.innerTheta_pos
    selected_balance := hselected
    unselected_balance := hunselected
    geometricThreshold_nonneg := N.geometricThreshold_nonneg
    degreeThreshold_nonneg := N.degreeThreshold_nonneg
    meanRadius_nonneg := N.meanRadius_nonneg
    qScale_pos := N.qScale_pos
    kappa_pos := N.kappa_pos
    E_pos := N.E_pos
    D1_subset := hD1
    candidate_diverse := hcandidateDiverse
    small_degree_window := by
      rw [hhalf]
      exact N.small_degree_window
    step_mean := hstep
    mean_rise := hrise
    literal_window := by
      simpa [pathShift, degreeCenter,
        AugmentationExposureWindowBounds.translatedLiteralGraphPath,
        AugmentationGraphFull.translatedLiteralGraphPath] using hliteral
    global_window := by
      simpa [pathShift, degreeCenter,
        AugmentationExposureWindowBounds.translatedLiteralGraphPath,
        AugmentationGraphFull.translatedLiteralGraphPath] using hglobal
    m_pos := N.m_pos
    sigma_pos := N.sigma_pos
    R_small := N.R_small
    switching_budget := N.switching_budget
    collision_budget := N.collision_budget
    candidate_survivors := N.candidate_survivors
    piece_bound := N.piece_bound
    output_bound := N.output_bound
    risk_budget := by
      unfold AugmentationGraphFull.graphCollisionRisk
      rw [hhalf]
      exact N.risk_budget }
  exact B.toCrowdLargeBounds hrawCard

end

end AugmentationExposureCrowdFinal
end Erdos636
