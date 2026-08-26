import ErdosProblems.Erdos1038.PlatformReferenceMomentLimits
import ErdosProblems.Erdos1038.PlatformReferenceCoefficientLimits
import ErdosProblems.Erdos1038.ResidualWidthUniformComparison
import ErdosProblems.Erdos1038.ResidualWidthSeriesLimits

/-!
# Uniform inverse-branch room for canonical platform meshes

A positive continuum exterior potential leaves a fixed positive margin on
every sufficiently fine mesh.  This file converts that additive logarithmic
margin into the multiplicative comparison ratio needed for a single
geometric coefficient majorant across the changing finite dimensions.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Fixed multiplicative room supplied by half of the positive continuum
potential margin. -/
def platformReferenceComparisonRatio
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (s : ℝ) : ℝ :=
  Real.exp
    (-(platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s / 2))

/-- The coefficient ratio obtained by evaluating the inverse series at the
midpoint between the fixed comparison scale and its boundary. -/
def platformReferenceCoefficientRatio
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (s : ℝ) : ℝ :=
  let q := platformReferenceComparisonRatio C k a
    hk ha ha2 hthreshold s
  2 * q / (1 + q)

/-- Explicit summable majorant for the odd base coefficients. -/
def platformReferenceBaseCoefficientMajorant
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (s : ℝ)
    (j : ℕ) : ℝ :=
  s * platformReferenceCoefficientRatio C k a
    hk ha ha2 hthreshold s ^ (2 * j + 1)

/-- The exponential of minus half the continuum potential is a genuine
geometric ratio. -/
theorem exp_neg_half_platformReferenceExteriorLogPotentialLimit_mem_Ioo
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ}
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    platformReferenceComparisonRatio C k a
        hk ha ha2 hthreshold s ∈ Ioo (0 : ℝ) 1 := by
  unfold platformReferenceComparisonRatio
  constructor
  · exact Real.exp_pos _
  · rw [Real.exp_lt_one_iff]
    linarith

/-- Every sufficiently fine canonical platform mesh lies below its
inverse-branch comparison boundary by the same fixed factor `exp (-L/2)`,
where `L` is the positive continuum exterior potential. -/
theorem eventually_platformResidualRefinement_uniformComparison
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    ∀ᶠ n in atTop,
      inverseMonomial
          (platformResidualRefinementAlpha C k n)
          (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n) ≤
        platformReferenceComparisonRatio C k a
            hk ha ha2 hthreshold s *
          (s / lagrangePhiValue
            (platformResidualRefinementAlpha C k n)
            (platformResidualRefinementReference C k a
              hk ha ha2 hthreshold n) s) := by
  filter_upwards
      [eventually_half_platformReferenceExteriorLogPotentialLimit_le
        C k a hk ha ha2 hthreshold hsa hlimit] with n hn
  apply
    inverseMonomial_le_exp_neg_mul_div_lagrangePhiValue_of_logPotential
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n)
      (platformResidualRefinementReference_mem_positiveCoordinates
        C k a hk ha ha2 hthreshold n)
      hs
  · intro p
    exact hsa.trans_le
      (platformResidualRefinementReference_mem_Icc
        C k a hk ha ha2 hthreshold n p).1
  · exact hn

/-- The midpoint coefficient ratio lies strictly between zero and one. -/
theorem platformReferenceCoefficientRatio_mem_Ioo
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ}
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    platformReferenceCoefficientRatio C k a
        hk ha ha2 hthreshold s ∈ Ioo (0 : ℝ) 1 := by
  let q := platformReferenceComparisonRatio C k a
    hk ha ha2 hthreshold s
  have hq : q ∈ Ioo (0 : ℝ) 1 := by
    simpa only [q] using!
      exp_neg_half_platformReferenceExteriorLogPotentialLimit_mem_Ioo
        C k a hk ha ha2 hthreshold hlimit
  change 2 * q / (1 + q) ∈ Ioo (0 : ℝ) 1
  constructor
  · exact div_pos (mul_pos (by norm_num) hq.1) (by linarith [hq.1])
  · exact (div_lt_one (by linarith [hq.1] : 0 < 1 + q)).2
      (by linarith [hq.2])

/-- The explicit odd base majorant is summable. -/
theorem summable_platformReferenceBaseCoefficientMajorant
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ}
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    Summable (platformReferenceBaseCoefficientMajorant C k a
      hk ha ha2 hthreshold s) := by
  let ratio := platformReferenceCoefficientRatio C k a
    hk ha ha2 hthreshold s
  have hratio : ratio ∈ Ioo (0 : ℝ) 1 := by
    simpa only [ratio] using! platformReferenceCoefficientRatio_mem_Ioo
      C k a hk ha ha2 hthreshold hlimit
  have hnorm : ‖ratio‖ < (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos hratio.1]
    exact hratio.2
  have hfull : Summable (fun n : ℕ ↦ s * ratio ^ n) :=
    (summable_geometric_of_norm_lt_one hnorm).mul_left s
  have hinjective : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro j l hjl
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    exact Nat.add_right_cancel hjl
  simpa only [platformReferenceBaseCoefficientMajorant, ratio] using!
    hfull.comp_injective hinjective

/-- All sufficiently fine canonical meshes are dominated, degree by
degree, by the same explicit summable odd base majorant. -/
theorem eventually_norm_scaledLagrangeCoefficient_platformResidualRefinement_le
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficient
          (platformResidualRefinementAlpha C k n) (2 * j + 1)
          (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n)‖ ≤
        platformReferenceBaseCoefficientMajorant C k a
          hk ha ha2 hthreshold s j := by
  have hq :=
    exp_neg_half_platformReferenceExteriorLogPotentialLimit_mem_Ioo
      C k a hk ha ha2 hthreshold hlimit
  filter_upwards
      [eventually_platformResidualRefinement_uniformComparison
        C k a hk ha ha2 hthreshold hs hsa hlimit] with n hcomparison
  intro j
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have halpha (p : iota × Fin (n + 1)) :
      0 < platformResidualRefinementAlpha C k n p := by
    exact refinedLagrangeWeight_pos (Nat.succ_pos n)
      (residualLagrangeAlpha_pos C hk0) p
  have href := platformResidualRefinementReference_mem_positiveCoordinates
    C k a hk ha ha2 hthreshold n
  have hsd (p : iota × Fin (n + 1)) :
      s < platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n p :=
    hsa.trans_le (platformResidualRefinementReference_mem_Icc
      C k a hk ha ha2 hthreshold n p).1
  rw [Real.norm_eq_abs, abs_of_nonneg
    (scaledLagrangeCoefficient_nonneg
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n) halpha href (2 * j + 1))]
  simpa only [platformReferenceBaseCoefficientMajorant,
    platformReferenceCoefficientRatio] using!
    scaledLagrangeCoefficient_le_uniform_geometric_of_comparison
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n)
      halpha href hs hsd hq hcomparison (2 * j + 1)

/-- The actual inverse-width series on the canonical platform refinements
converges to the odd continuum moment-recurrence series.  Coefficientwise
convergence and uniform tail control are both discharged here. -/
theorem tendsto_inverseWidthSeries_platformResidualRefinement
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    Tendsto
      (fun n ↦ inverseWidthSeries
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n))
      atTop
      (nhds (2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientLimit C k a
          hk ha ha2 hthreshold (2 * j + 1))) := by
  apply tendsto_inverseWidthSeries_of_dominated_coefficients
    (fun n ↦ iota × Fin (n + 1))
    (fun n ↦ platformResidualRefinementAlpha C k n)
    (fun n ↦ platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n)
    (fun j ↦ platformReferenceScaledLagrangeCoefficientLimit C k a
      hk ha ha2 hthreshold (2 * j + 1))
    (platformReferenceBaseCoefficientMajorant C k a
      hk ha ha2 hthreshold s)
  · exact summable_platformReferenceBaseCoefficientMajorant
      C k a hk ha ha2 hthreshold hlimit
  · intro j
    exact tendsto_scaledLagrangeCoefficient_platformResidualRefinement
      C k a hk ha ha2 hthreshold (by omega)
  · exact
      eventually_norm_scaledLagrangeCoefficient_platformResidualRefinement_le
        C k a hk ha ha2 hthreshold hs hsa hlimit

end

end Erdos1038
