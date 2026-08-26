/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Gaussian comparison for finite triangular arrays of small sign weights.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CharacteristicComparison
import ErdosProblems.Erdos521.ProductDifference

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem tendsto_sign_gaussian_products_sub_zero (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |a n i| < r)
    (hvariance : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s n, (a n i) ^ 2 ≤ M) :
    Tendsto (fun n : ℕ ↦ (∏ i ∈ s n, charFun signLaw (a n i)) -
      ∏ i ∈ s n, charFun (gaussianReal 0 1) (a n i)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (M + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨r, hr, hbound⟩ := sign_gaussian_charFun_small hη
  filter_upwards [hsmall r hr, hvariance] with n hnsmall hnvar
  rw [dist_zero_right]
  calc
    ‖(∏ i ∈ s n, charFun signLaw (a n i)) - ∏ i ∈ s n, charFun (gaussianReal 0 1) (a n i)‖ ≤
        ∑ i ∈ s n, ‖charFun signLaw (a n i) - charFun (gaussianReal 0 1) (a n i)‖ :=
      norm_prod_sub_prod_le_sum (s n) _ _ (fun _ _ ↦ norm_charFun_le_one _)
        (fun _ _ ↦ norm_charFun_le_one _)
    _ ≤ ∑ i ∈ s n, η * (a n i) ^ 2 := Finset.sum_le_sum fun i hi ↦ hbound _ (hnsmall i hi)
    _ = η * ∑ i ∈ s n, (a n i) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ η * M := mul_le_mul_of_nonneg_left hnvar hη.le
    _ < ε := by
      have hid : η * (M + 1) = ε := by dsimp [η]; field_simp
      nlinarith

theorem charFun_standardGaussian_real (t : ℝ) :
    charFun (gaussianReal 0 1) t = (Real.exp (-t ^ 2 / 2) : ℂ) := by
  rw [charFun_gaussianReal]
  simp [Complex.ofReal_exp, neg_div]

theorem standardGaussian_charFun_prod (s : Finset ℕ) (a : ℕ → ℝ) :
    (∏ i ∈ s, charFun (gaussianReal 0 1) (a i)) =
      (Real.exp (-(∑ i ∈ s, (a i) ^ 2) / 2) : ℂ) := by
  simp_rw [charFun_standardGaussian_real]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  apply congrArg Complex.ofReal
  apply congrArg Real.exp
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem triangular_cosine_products_tendsto (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    {V : ℝ} (hV : 0 ≤ V)
    (hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |a n i| < r)
    (hvariance : Tendsto (fun n ↦ ∑ i ∈ s n, (a n i) ^ 2) atTop (𝓝 V)) :
    Tendsto (fun n ↦ ∏ i ∈ s n, (Real.cos (a n i) : ℂ)) atTop
      (𝓝 (Real.exp (-V / 2) : ℂ)) := by
  have hbound : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s n, (a n i) ^ 2 ≤ V + 1 :=
    (hvariance.eventually (gt_mem_nhds (by linarith : V < V + 1))).mono fun _ h ↦ h.le
  have herror := tendsto_sign_gaussian_products_sub_zero s a (by linarith : 0 ≤ V + 1) hsmall hbound
  have hgauss : Tendsto (fun n ↦ ∏ i ∈ s n, charFun (gaussianReal 0 1) (a n i)) atTop
      (𝓝 (Real.exp (-V / 2) : ℂ)) := by
    simp_rw [standardGaussian_charFun_prod]
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp (hvariance.neg.div_const 2))
  have h := herror.add hgauss
  simpa only [sub_add_cancel, zero_add, charFun_signLaw] using h

end Erdos521
