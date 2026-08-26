import ErdosProblems.Erdos1038.LowKPolynomial
import ErdosProblems.Erdos1038.ResidualWidthInverseBranch

/-!
# Exact inverse-series width of the normalized endpoint component

This module identifies the endpoint component of an endpoint-normalized
polynomial with the two real branches of the residual Lagrange inverse.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set Polynomial Filter

namespace Erdos1038

noncomputable section

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

lemma normalizedRightBoundary_add_one_residualPotential_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    residualPotential (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)
        (h.normalizedRightBoundary + 1) = 0 := by
  have hbnot : h.normalizedRightBoundary ∉
      sublevelSet h.normalizedPolynomial := by
    simpa [normalizedRightBoundary] using!
      sublevelComponent_sSup_not_mem h.normalized_admissible
        (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  have hbnotroot : h.normalizedRightBoundary ∉
      rootSet h.normalizedPolynomial := by
    intro hb
    exact hbnot (rootSet_subset_sublevelSet h.normalizedPolynomial hb)
  have hpotential :=
    h.normalized_residualPotential_eq_log_abs_eval hres hbnotroot
  rw [h.normalizedRightBoundary_abs_eval_eq_one, Real.log_one,
    mul_zero] at hpotential
  exact hpotential

/-- Every shifted point strictly between the endpoint pole and its right
boundary has strictly negative residual potential. -/
lemma normalized_residualPotential_neg_before_rightBoundary
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo 0 (h.normalizedRightBoundary + 1)) :
    residualPotential (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) x < 0 := by
  have hnegOne : (-1 : ℝ) ∈
      sublevelComponent h.normalizedPolynomial (-1) :=
    mem_connectedComponentIn
      (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  rw [h.normalized_endpoint_component_eq_Ioo] at hnegOne
  have hxComponent : x - 1 ∈
      sublevelComponent h.normalizedPolynomial (-1) := by
    rw [h.normalized_endpoint_component_eq_Ioo]
    constructor <;> linarith [hnegOne.1, hx.1, hx.2]
  have hxSublevel : x - 1 ∈ sublevelSet h.normalizedPolynomial :=
    connectedComponentIn_subset _ _ hxComponent
  have hxRoot : x - 1 ∉ rootSet h.normalizedPolynomial := by
    rw [mem_rootSet_iff]
    intro hroot
    rcases (h.shifted_mem_normalized_roots_iff hres x).mp hroot with
        rfl | ⟨i, hi⟩
    · exact (lt_irrefl 0) hx.1
    · have hibound :=
        (h.normalized_boundary_isResidualSeparationPoint hres).2.1 i
      rw [hi] at hx
      exact (not_lt_of_ge hx.2.le) hibound
  apply (h.normalized_residualPotential_neg_iff_empiricalPotential_neg
    hres x).mpr
  exact (empiricalPotential_neg_iff_sublevel
    h.normalized_admissible hxRoot).mpr hxSublevel

/-- The shifted right boundary is on the increasing side of the residual
critical point. -/
lemma normalizedRightBoundary_add_one_le_residualCriticalPoint
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (hk : 0 < normalizedEndpointResidualRatio h) :
    h.normalizedRightBoundary + 1 ≤
      residualCriticalPoint (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) hk := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hsep := h.normalized_boundary_isResidualSeparationPoint hres
  have hscale : residualScale C k ≤ residualPsi C k yc :=
    residualScale_le_psi_critical_of_separation C hk hsep
  have hnonneg : 0 ≤ residualPotential C k yc :=
    (residualPotential_nonneg_iff_scale_le_psi_of_pos
      C hk hyc.1 hyc.2).2 hscale
  have hycbound : h.normalizedRightBoundary + 1 ≤ yc := by
    by_contra hnot
    have hneg := h.normalized_residualPotential_neg_before_rightBoundary
      hres ⟨hyc.1, lt_of_not_ge hnot⟩
    exact (not_lt_of_ge hnonneg) hneg
  simpa only [C, k, yc] using! hycbound

/-- The positive residual Lagrange branch is exactly the shifted right
endpoint of the normalized main component. -/
theorem lagrangeInverseValue_residualScale_eq_normalizedRightBoundary_add_one
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    lagrangeInverseValue
        (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h))
        (h.normalizedResidualConfiguration hres).location
        (residualScale (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) =
      h.normalizedRightBoundary + 1 := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  let b := h.normalizedRightBoundary + 1
  let W := lagrangeInverseValue (residualLagrangeAlpha C k) C.location
    (residualScale C k)
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one
    (h.one_le_normalizedEndpointResidualRatio hres)
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hsep : IsResidualSeparationPoint C k b :=
    h.normalized_boundary_isResidualSeparationPoint hres
  have hbmin : b < residualMinLocation C := by
    rw [← location_residualMinIndex C]
    exact hsep.2.1 (residualMinIndex C)
  have hbpsi : residualPsi C k b = residualScale C k :=
    (residualPotential_eq_zero_iff_psi_eq_scale_of_pos
      C hk.ne' hsep.1 hbmin).mp
      (h.normalizedRightBoundary_add_one_residualPotential_eq_zero hres)
  have hWpsi : residualPsi C k W = residualScale C k :=
    residualPsi_lagrangeInverseValue_eq_scale_of_separation C hk hsep
  have hWle : W ≤ yc :=
    residual_lagrangeInverseValue_le_critical_of_separation C hk hsep
  have hble : b ≤ yc := by
    simpa only [C, k, b, yc] using!
      h.normalizedRightBoundary_add_one_le_residualCriticalPoint hres hk
  have hW0 : 0 ≤ W := by
    unfold W lagrangeInverseValue
    exact tsum_nonneg fun n ↦ mul_nonneg
      (coeff_lagrangeInversePowerSeries_nonneg _ _
        (residualLagrangeAlpha_pos C hk)
        (residual_locations_mem_positiveCoordinates C) n)
      (pow_nonneg (residualScale_pos C k).le n)
  apply (residualPsi_strictMonoOn_left C k hk).injOn
    ⟨hW0, hWle⟩ ⟨hsep.1.le, hble⟩
  rw [hWpsi, hbpsi]

/-- The left endpoint of the normalized main component, shifted by `+1`,
also lies on the residual zero-potential level. -/
lemma normalizedLeftBoundary_add_one_residualPotential_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    residualPotential (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)
        (sInf (sublevelComponent h.normalizedPolynomial (-1)) + 1) = 0 := by
  let a := sInf (sublevelComponent h.normalizedPolynomial (-1))
  have hanot : a ∉ sublevelSet h.normalizedPolynomial := by
    simpa only [a] using!
      sublevelComponent_sInf_not_mem h.normalized_admissible
        (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  have hanotroot : a ∉ rootSet h.normalizedPolynomial := by
    intro ha
    exact hanot (rootSet_subset_sublevelSet h.normalizedPolynomial ha)
  have haeval : |h.normalizedPolynomial.eval a| = 1 := by
    have hend := sublevelComponent_endpoints_frontier
      h.normalized_admissible
      (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
    exact frontier_sublevelSet_abs_eval_eq_one h.normalizedPolynomial hend.1
  have hpotential :=
    h.normalized_residualPotential_eq_log_abs_eval hres hanotroot
  rw [haeval, Real.log_one, mul_zero] at hpotential
  simpa only [a] using! hpotential

lemma normalizedLeftBoundary_add_one_lt_zero :
    sInf (sublevelComponent h.normalizedPolynomial (-1)) + 1 < 0 := by
  have hmem : (-1 : ℝ) ∈
      sublevelComponent h.normalizedPolynomial (-1) :=
    mem_connectedComponentIn
      (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  rw [h.normalized_endpoint_component_eq_Ioo] at hmem
  linarith [hmem.1]

/-- The shifted left endpoint is the negative-side zero of the residual
inverse map. -/
lemma residualPsi_normalizedLeftBoundary_add_one_eq_neg_scale
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    residualPsi (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)
        (sInf (sublevelComponent h.normalizedPolynomial (-1)) + 1) =
      -residualScale (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  let a := sInf (sublevelComponent h.normalizedPolynomial (-1)) + 1
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one
    (h.one_le_normalizedEndpointResidualRatio hres)
  have ha0 : a < 0 := by
    simpa only [a] using! h.normalizedLeftBoundary_add_one_lt_zero
  have hamin : a < residualMinLocation C :=
    ha0.trans (residualMinLocation_pos C)
  have habs : |residualPsi C k a| = residualScale C k :=
    (residualPotential_eq_zero_iff_abs_psi_eq_scale C hk.ne'
      ha0.ne hamin).mp (by
        simpa only [C, k, a] using!
          h.normalizedLeftBoundary_add_one_residualPotential_eq_zero hres)
  have hpsiNeg : residualPsi C k a < 0 := by
    rw [residualPsi]
    exact mul_neg_of_neg_of_pos ha0 (Real.exp_pos _)
  rw [abs_of_neg hpsiNeg] at habs
  have hpsi : residualPsi C k a = -residualScale C k := by
    linarith [habs]
  simpa only [C, k, a] using! hpsi

/-- The negative residual Lagrange branch is exactly the shifted left
endpoint of the normalized main component. -/
theorem lagrangeInverseValue_neg_residualScale_eq_normalizedLeftBoundary_add_one
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    lagrangeInverseValue
        (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h))
        (h.normalizedResidualConfiguration hres).location
        (-residualScale (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) =
      sInf (sublevelComponent h.normalizedPolynomial (-1)) + 1 := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  let a := sInf (sublevelComponent h.normalizedPolynomial (-1)) + 1
  let W := lagrangeInverseValue (residualLagrangeAlpha C k) C.location
    (-residualScale C k)
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one
    (h.one_le_normalizedEndpointResidualRatio hres)
  have hsep : IsResidualSeparationPoint C k
      (h.normalizedRightBoundary + 1) :=
    h.normalized_boundary_isResidualSeparationPoint hres
  have hW0 : W < 0 :=
    residual_lagrangeInverseValue_neg_lt_zero_of_separation C hk hsep
  have ha0 : a < 0 := by
    simpa only [a] using! h.normalizedLeftBoundary_add_one_lt_zero
  have hWpsi : residualPsi C k W = -residualScale C k :=
    residualPsi_lagrangeInverseValue_neg_eq_neg_scale_of_separation
      C hk hsep
  have hapsi : residualPsi C k a = -residualScale C k := by
    simpa only [C, k, a] using!
      h.residualPsi_normalizedLeftBoundary_add_one_eq_neg_scale hres
  apply (residualPsi_strictMonoOn_nonpos C hk).injOn hW0.le ha0.le
  rw [hWpsi, hapsi]

/-- Exact identification of the normalized main-component width with the
convergent odd residual inverse series. -/
theorem normalizedMainComponentWidth_eq_inverseWidthSeries
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    normalizedMainComponentWidth h =
      inverseWidthSeries
        (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h))
        (h.normalizedResidualConfiguration hres).location := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one
    (h.one_le_normalizedEndpointResidualRatio hres)
  have hsep : IsResidualSeparationPoint C k
      (h.normalizedRightBoundary + 1) :=
    h.normalized_boundary_isResidualSeparationPoint hres
  rw [inverseWidthSeries_residual_eq_inverseValue_sub_neg C hk hsep]
  rw [show lagrangeInverseValue (residualLagrangeAlpha C k) C.location
      (residualScale C k) = h.normalizedRightBoundary + 1 by
        simpa only [C, k] using!
          h.lagrangeInverseValue_residualScale_eq_normalizedRightBoundary_add_one
            hres]
  rw [show lagrangeInverseValue (residualLagrangeAlpha C k) C.location
      (-residualScale C k) =
        sInf (sublevelComponent h.normalizedPolynomial (-1)) + 1 by
        simpa only [C, k] using!
          h.lagrangeInverseValue_neg_residualScale_eq_normalizedLeftBoundary_add_one
            hres]
  unfold normalizedMainComponentWidth
  ring

/-- Endpoint separation supplies absolute convergence of the full scaled
Lagrange series at the actual normalized residual locations. -/
theorem summable_normalized_scaledLagrangeCoefficient
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    Summable (fun n ↦ scaledLagrangeCoefficient
      (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)) n
      (h.normalizedResidualConfiguration hres).location) := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one
    (h.one_le_normalizedEndpointResidualRatio hres)
  exact summable_residual_scaledLagrangeCoefficient_of_separation C hk
    (h.normalized_boundary_isResidualSeparationPoint hres)

/-- The exact supporting inequality at the normalized target.  Target
summability is automatic from endpoint separation; only convergence at the
chosen reference and of the reference-to-target directional series remain
as hypotheses. -/
theorem inverseWidthSeries_add_directional_le_normalizedMainComponentWidth
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {reference : NormalizedResidualIndex h → ℝ}
    (href : reference ∈ positiveCoordinates (NormalizedResidualIndex h))
    (hsumReference : Summable (fun n ↦ scaledLagrangeCoefficient
      (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)) n reference))
    (hsumDirectional : Summable (fun j ↦
      scaledLagrangeCoefficientDirectional
        (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) (2 * j + 1) reference
        (h.normalizedResidualConfiguration hres).location)) :
    inverseWidthSeries
        (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) reference +
      inverseWidthSeriesDirectional
        (residualLagrangeAlpha (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) reference
        (h.normalizedResidualConfiguration hres).location ≤
      normalizedMainComponentWidth h := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one
    (h.one_le_normalizedEndpointResidualRatio hres)
  have hsep : IsResidualSeparationPoint C k
      (h.normalizedRightBoundary + 1) :=
    h.normalized_boundary_isResidualSeparationPoint hres
  rw [h.normalizedMainComponentWidth_eq_inverseWidthSeries hres]
  exact inverseWidthSeries_supporting_of_summable
    (residualLagrangeAlpha C k) (residualLagrangeAlpha_pos C hk)
    href (residual_locations_mem_positiveCoordinates C)
    hsumReference
    (summable_residual_scaledLagrangeCoefficient_of_separation C hk hsep)
    hsumDirectional

end EndpointNormalizationHypotheses

end

end Erdos1038
