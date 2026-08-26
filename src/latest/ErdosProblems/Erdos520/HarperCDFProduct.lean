import ErdosProblems.Erdos520.HarperEsseen

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# From one-block CDF bounds to finite rectangle bounds

The Gaussian replacement is proved one scheduled prime block at a time.
This file records the elementary bookkeeping needed to use those estimates
simultaneously: a Kolmogorov bound controls every half-open interval, and
finite products of interval probabilities lose only the sum of the
one-block errors.
-/

/-- The probability of a half-open interval is the corresponding CDF
increment. -/
theorem measureReal_Ioc_eq_cdf_sub
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    {a b : ℝ} (hab : a ≤ b) :
    rho.real (Ioc a b) = cdf rho b - cdf rho a := by
  rw [← Set.Iic_sdiff_Iic,
    measureReal_diff (Set.Iic_subset_Iic.mpr hab) measurableSet_Iic,
    cdf_eq_real, cdf_eq_real]

/-- A Kolmogorov bound `d` gives a `2d` bound on every half-open interval. -/
theorem abs_measureReal_Ioc_sub_le_two_mul_cdfDistance
    (rho nu : Measure ℝ)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure nu]
    {a b : ℝ} (hab : a ≤ b) :
    |rho.real (Ioc a b) - nu.real (Ioc a b)| ≤
      2 * harperCDFDistance rho nu := by
  have hone : ∀ x : ℝ, |cdf rho x - cdf nu x| ≤ (1 : ℝ) := by
    intro x
    rw [abs_le]
    constructor <;>
      linarith [cdf_nonneg rho x, cdf_le_one rho x,
        cdf_nonneg nu x, cdf_le_one nu x]
  have hb := abs_sub_le_harperKolmogorovDistance hone b
  have ha := abs_sub_le_harperKolmogorovDistance hone a
  rw [measureReal_Ioc_eq_cdf_sub rho hab,
    measureReal_Ioc_eq_cdf_sub nu hab]
  have hrearrange :
      (cdf rho b - cdf rho a) - (cdf nu b - cdf nu a) =
        (cdf rho b - cdf nu b) - (cdf rho a - cdf nu a) := by
    ring
  rw [hrearrange]
  calc
    |(cdf rho b - cdf nu b) - (cdf rho a - cdf nu a)| ≤
        |cdf rho b - cdf nu b| + |cdf rho a - cdf nu a| :=
      abs_sub _ _
    _ ≤ harperCDFDistance rho nu + harperCDFDistance rho nu :=
      add_le_add hb ha
    _ = 2 * harperCDFDistance rho nu := by ring

/-- Real form of the finite-product perturbation estimate. -/
theorem abs_prod_sub_prod_le_sum_abs_sub
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1)
    (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤
      ∑ i ∈ s, |f i - g i| := by
  have h := norm_prod_sub_prod_le_sum_norm_sub s
    (fun i ↦ (f i : ℂ)) (fun i ↦ (g i : ℂ))
    (fun i hi ↦ by simpa using! hf i hi)
    (fun i hi ↦ by simpa using! hg i hi)
  simpa only [← Complex.ofReal_prod, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using! h

/-- Uniform coordinate errors accumulate at most linearly in the number of
coordinates. -/
theorem abs_prod_sub_prod_le_card_mul
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {delta : ℝ}
    (hf : ∀ i ∈ s, |f i| ≤ 1)
    (hg : ∀ i ∈ s, |g i| ≤ 1)
    (hfg : ∀ i ∈ s, |f i - g i| ≤ delta) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤
      s.card * delta := by
  calc
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤
        ∑ i ∈ s, |f i - g i| :=
      abs_prod_sub_prod_le_sum_abs_sub s f g hf hg
    _ ≤ ∑ _i ∈ s, delta :=
      Finset.sum_le_sum fun i hi ↦ hfg i hi
    _ = s.card * delta := by simp

/-- Product-rectangle consequence of one-dimensional CDF comparisons. -/
theorem abs_prod_measureReal_Ioc_sub_prod_le
    {ι : Type*} (s : Finset ι)
    (rho nu : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (rho i)]
    [∀ i, IsProbabilityMeasure (nu i)]
    (a b : ι → ℝ) (hab : ∀ i ∈ s, a i ≤ b i) :
    |∏ i ∈ s, (rho i).real (Ioc (a i) (b i)) -
        ∏ i ∈ s, (nu i).real (Ioc (a i) (b i))| ≤
      ∑ i ∈ s, 2 * harperCDFDistance (rho i) (nu i) := by
  refine (abs_prod_sub_prod_le_sum_abs_sub s
    (fun i ↦ (rho i).real (Ioc (a i) (b i)))
    (fun i ↦ (nu i).real (Ioc (a i) (b i))) ?_ ?_).trans ?_
  · intro i hi
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  · intro i hi
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  · apply Finset.sum_le_sum
    intro i hi
    exact abs_measureReal_Ioc_sub_le_two_mul_cdfDistance
      (rho i) (nu i) (hab i hi)

end Problem520
end Erdos
