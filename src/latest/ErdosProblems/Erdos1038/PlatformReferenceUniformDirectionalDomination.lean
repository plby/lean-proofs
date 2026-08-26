import ErdosProblems.Erdos1038.PlatformReferenceUniformComparison

/-!
# Uniform domination of canonical platform directional coefficients

The base coefficient majorant acquires only one linear degree factor under a
material directional derivative.  This file records an explicit summable
majorant and its eventual domination of every canonical refinement.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Explicit polynomial-times-geometric majorant for the odd directional
coefficients of every sufficiently fine canonical platform refinement. -/
def platformReferenceDirectionalCoefficientMajorant
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (s : ℝ)
    (j : ℕ) : ℝ :=
  (2 / a) * (2 * (((2 * j + 1 : ℕ) : ℝ))) *
    platformReferenceBaseCoefficientMajorant C k a
      hk ha ha2 hthreshold s j

/-- The explicit directional majorant is summable: its extra linear factor
is absorbed by the polynomially weighted geometric series. -/
theorem summable_platformReferenceDirectionalCoefficientMajorant
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ}
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    Summable (platformReferenceDirectionalCoefficientMajorant C k a
      hk ha ha2 hthreshold s) := by
  let ratio := platformReferenceCoefficientRatio C k a
    hk ha ha2 hthreshold s
  have hratio : ratio ∈ Ioo (0 : ℝ) 1 := by
    simpa only [ratio] using! platformReferenceCoefficientRatio_mem_Ioo
      C k a hk ha ha2 hthreshold hlimit
  have hnorm : ‖ratio‖ < (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos hratio.1]
    exact hratio.2
  have hfull : Summable (fun n : ℕ ↦ (n : ℝ) * ratio ^ n) := by
    simpa only [pow_one] using!
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm)
  have hinjective : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro j l hjl
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    exact Nat.add_right_cancel hjl
  have hodd : Summable (fun j : ℕ ↦
      (((2 * j + 1 : ℕ) : ℝ)) * ratio ^ (2 * j + 1)) :=
    hfull.comp_injective hinjective
  exact (hodd.mul_left ((2 / a) * 2 * s)).congr (fun j ↦ by
    simp only [platformReferenceDirectionalCoefficientMajorant,
      platformReferenceBaseCoefficientMajorant, ratio]
    ring)

/-- All sufficiently fine canonical refinements have every odd directional
coefficient dominated in norm by one fixed summable sequence. -/
theorem eventually_norm_scaledLagrangeCoefficientDirectional_platformResidualRefinement_le
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    ∀ᶠ n in atTop, ∀ j,
      ‖scaledLagrangeCoefficientDirectional
          (platformResidualRefinementAlpha C k n) (2 * j + 1)
          (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n)
          (platformResidualRefinementTarget C n)‖ ≤
        platformReferenceDirectionalCoefficientMajorant C k a
          hk ha ha2 hthreshold s j := by
  filter_upwards
      [eventually_norm_scaledLagrangeCoefficient_platformResidualRefinement_le
        C k a hk ha ha2 hthreshold hs hsa hlimit] with n hbase
  intro j
  let alpha := platformResidualRefinementAlpha C k n
  let reference := platformResidualRefinementReference C k a
    hk ha ha2 hthreshold n
  let target := platformResidualRefinementTarget C n
  let degree : ℕ := 2 * j + 1
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have halpha (p : iota × Fin (n + 1)) : 0 < alpha p := by
    exact refinedLagrangeWeight_pos (Nat.succ_pos n)
      (residualLagrangeAlpha_pos C hk0) p
  have href : reference ∈ positiveCoordinates (iota × Fin (n + 1)) := by
    exact platformResidualRefinementReference_mem_positiveCoordinates
      C k a hk ha ha2 hthreshold n
  have hsumAlpha : (∑ p, alpha p) = 1 / k := by
    have hsum :=
      sum_platformResidualRefinementAlpha_mul C k n (fun _p ↦ (1 : ℝ))
    simp only [platformResidualRefinementAlpha, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [one_div, inv_mul_cancel₀ hden] at hsum
    simp only [mul_one] at hsum
    rw [sum_residualLagrangeAlpha] at hsum
    exact hsum
  have hsumAlphaLe : (∑ p, alpha p) ≤ 1 := by
    rw [hsumAlpha]
    exact (div_le_one hk0).2 hk
  have hdegreeSub : (((degree - 1 : ℕ) : ℝ)) ≤ (degree : ℝ) := by
    exact_mod_cast Nat.sub_le degree 1
  have hdegreeNonneg : 0 ≤ (degree : ℝ) := Nat.cast_nonneg degree
  have hdegreeMul : (degree : ℝ) * (∑ p, alpha p) ≤ degree := by
    simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left hsumAlphaLe hdegreeNonneg
  have hdegreeBound :
      (degree : ℝ) * (∑ p, alpha p) + (degree - 1 : ℕ) ≤
        2 * (degree : ℝ) := by
    exact add_le_add hdegreeMul hdegreeSub |>.trans_eq (by ring)
  have hrelative (p : iota × Fin (n + 1)) :
      |(target p - reference p) / reference p| ≤ 2 / a := by
    exact platformResidualRefinement_relativeDisplacement_le
      C hk ha ha2 hthreshold n p
  have hdirection := abs_scaledLagrangeCoefficientDirectional_le
    alpha reference target halpha (n := degree) (by omega)
    (B := 2 / a) hrelative
  have hcoefficientNonneg :
      0 ≤ scaledLagrangeCoefficient alpha degree reference :=
    scaledLagrangeCoefficient_nonneg alpha reference halpha href degree
  have hcoefficientLe :
      scaledLagrangeCoefficient alpha degree reference ≤
        platformReferenceBaseCoefficientMajorant C k a
          hk ha ha2 hthreshold s j := by
    simpa only [alpha, reference, degree, Real.norm_eq_abs,
      abs_of_nonneg hcoefficientNonneg] using! hbase j
  have hBNonneg : 0 ≤ 2 / a := div_nonneg (by norm_num) ha.le
  have htwoDegreeNonneg : 0 ≤ 2 * (degree : ℝ) := by positivity
  rw [Real.norm_eq_abs]
  calc
    |scaledLagrangeCoefficientDirectional alpha degree reference target| ≤
        (2 / a) *
            ((degree : ℝ) * (∑ p, alpha p) + (degree - 1 : ℕ)) *
          scaledLagrangeCoefficient alpha degree reference := hdirection
    _ ≤ (2 / a) * (2 * (degree : ℝ)) *
          scaledLagrangeCoefficient alpha degree reference :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdegreeBound hBNonneg)
        hcoefficientNonneg
    _ ≤ (2 / a) * (2 * (degree : ℝ)) *
          platformReferenceBaseCoefficientMajorant C k a
            hk ha ha2 hthreshold s j :=
      mul_le_mul_of_nonneg_left hcoefficientLe
        (mul_nonneg hBNonneg htwoDegreeNonneg)
    _ = platformReferenceDirectionalCoefficientMajorant C k a
          hk ha ha2 hthreshold s j := by
      rfl

end

end Erdos1038
