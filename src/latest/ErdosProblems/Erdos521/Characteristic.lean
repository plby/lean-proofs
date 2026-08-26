/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Characteristic-function estimates for the fair-sign polynomials in Erdős 521.
Formal proof: Codex.
https://arxiv.org/abs/2403.06353
-/
import ErdosProblems.Erdos521.Model
import ErdosProblems.Erdos521.GeometricVariance
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem charFun_signLaw (t : ℝ) : charFun signLaw t = (Real.cos t : ℂ) := by
  rw [charFun_apply_real, signLaw, integral_bernoulliMeasure]
  norm_num [Complex.real_smul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos]
  rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- The characteristic function of a finite real linear form is the cosine product. -/
theorem charFun_linearForm (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    charFun (sequenceLaw.map (fun ε ↦ ∑ k ∈ s, a k * ε k)) t =
      ∏ k ∈ s, (Real.cos (t * a k) : ℂ) := by
  have hind : iIndepFun (fun k ε ↦ a k * ε k) sequenceLaw := by
    exact independent_coefficients.comp (fun k x ↦ a k * x) (fun _ ↦ by fun_prop)
  have hmeas (k : ℕ) (_ : k ∈ s) :
      AEMeasurable (fun ε : ℕ → ℝ ↦ a k * ε k) sequenceLaw :=
    (measurable_const.mul (measurable_pi_apply k)).aemeasurable
  rw [(hind.restrict s).charFun_map_fun_finsetSum_eq_prod
      hmeas,
    Finset.prod_apply]
  apply Finset.prod_congr rfl
  intro k _
  have hmap : sequenceLaw.map (fun ε ↦ a k * ε k) = signLaw.map (fun x ↦ a k * x) := by
    rw [← sequenceLaw_map_eval k, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, charFun_map_mul, charFun_signLaw, mul_comm]

/-- A Gaussian bound on cosine in its central half period. -/
theorem abs_cos_le_exp_neg_sq {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |Real.cos x| ≤ Real.exp (-(2 / Real.pi ^ 2) * x ^ 2) := by
  have hnonneg : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc (abs_le.mp hx)
  rw [abs_of_nonneg hnonneg]
  have hcos := Real.cos_le_one_sub_mul_cos_sq (hx.trans (by nlinarith [Real.pi_pos]))
  have hexp := Real.add_one_le_exp (-(2 / Real.pi ^ 2) * x ^ 2)
  linarith

theorem norm_charFun_linearForm_le (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ)
    (hsmall : ∀ k ∈ s, |t * a k| ≤ Real.pi / 2) :
    ‖charFun (sequenceLaw.map (fun ε ↦ ∑ k ∈ s, a k * ε k)) t‖ ≤
      Real.exp (-(2 / Real.pi ^ 2) * ∑ k ∈ s, (t * a k) ^ 2) := by
  rw [charFun_linearForm, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  calc
    (∏ k ∈ s, |Real.cos (t * a k)|) ≤
        ∏ k ∈ s, Real.exp (-(2 / Real.pi ^ 2) * (t * a k) ^ 2) :=
      Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun k hk ↦ abs_cos_le_exp_neg_sq (hsmall k hk))
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

/-- Arbitrary complementary coefficients can be discarded in the modulus bound. -/
theorem norm_charFun_linearForm_le_subset (s T : Finset ℕ) (hTs : T ⊆ s)
    (a : ℕ → ℝ) (t : ℝ) (hsmall : ∀ k ∈ T, |t * a k| ≤ Real.pi / 2) :
    ‖charFun (sequenceLaw.map (fun ε ↦ ∑ k ∈ s, a k * ε k)) t‖ ≤
      Real.exp (-(2 / Real.pi ^ 2) * ∑ k ∈ T, (t * a k) ^ 2) := by
  have hprod : (∏ k ∈ s, |Real.cos (t * a k)|) ≤ ∏ k ∈ T, |Real.cos (t * a k)| :=
    Finset.prod_le_prod_of_subset_of_le_one hTs (fun _ _ ↦ abs_nonneg _)
      (fun _ _ _ ↦ Real.abs_cos_le_one _)
  have hT := norm_charFun_linearForm_le T a t hsmall
  rw [charFun_linearForm, norm_prod] at hT ⊢
  simp only [Complex.norm_real, Real.norm_eq_abs] at hT ⊢
  exact hprod.trans hT

/-- Small arguments on a terminal block give a characteristic-function bound
for the whole polynomial, even if earlier arguments are large. -/
theorem norm_charFun_powerSum_le_tail (n m : ℕ) {x t : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (ht : |t| * x ^ m ≤ Real.pi / 2) :
    ‖charFun (sequenceLaw.map (fun ε ↦ powerSum ε (n + 1) x)) t‖ ≤
      Real.exp (-(2 / Real.pi ^ 2) * ∑ k ∈ Finset.Ico m (n + 1), (t * x ^ k) ^ 2) := by
  have heq : (fun ε ↦ powerSum ε (n + 1) x) =
      (fun ε ↦ ∑ k ∈ Finset.range (n + 1), x ^ k * ε k) := by
    funext ε
    simp only [powerSum, mul_comm]
  rw [heq]
  refine norm_charFun_linearForm_le_subset (Finset.range (n + 1))
    (Finset.Ico m (n + 1)) ?_ (fun k ↦ x ^ k) t ?_
  · intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  · intro k hk
    rw [abs_mul, abs_of_nonneg (pow_nonneg hx₀ _)]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hx₀ hx₁ (Finset.mem_Ico.mp hk).1) (abs_nonneg t)).trans ht

/-- A Gaussian characteristic-function estimate on a frequency interval that
grows exponentially with the degree when `x < 1`. This is the fair-sign
specialization of the characteristic-function step in Do's small-ball argument. -/
theorem norm_charFun_powerSum_gaussian_bound (n L : ℕ) (hL : 2 * L ≤ n + 1)
    {x t : ℝ} (hx₀ : 1 / 2 ≤ x) (hx₁ : x ≤ 1) (ht : |t| * x ^ L ≤ 1) :
    ‖charFun (sequenceLaw.map (fun ε ↦ powerSum ε (n + 1) x)) t‖ ≤
      Real.exp (-(1 / (4 * Real.pi ^ 2)) * min (t ^ 2) 1 * geometricVariance x (n + 1)) := by
  classical
  have hxnonneg : 0 ≤ x := by linarith
  have hexists : ∃ m : ℕ, |t| * x ^ m ≤ 1 := ⟨L, ht⟩
  let m := Nat.find hexists
  have hmL : m ≤ L := Nat.find_le ht
  have hm : |t| * x ^ m ≤ 1 := Nat.find_spec hexists
  have hamp : min (t ^ 2) 1 / 4 ≤ (t * x ^ m) ^ 2 := by
    cases hmzero : m with
    | zero =>
      simp only [pow_zero, mul_one]
      nlinarith [min_le_left (t ^ 2) 1, sq_nonneg t]
    | succ k =>
      have hprev : 1 < |t| * x ^ k := by
        exact lt_of_not_ge (Nat.find_min hexists (show k < m by omega))
      have hlarge : 1 / 2 ≤ |t * x ^ m| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hxnonneg _), hmzero, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hprev.le hxnonneg]
      have hsq : 1 / 4 ≤ (t * x ^ m) ^ 2 := by
        nlinarith [sq_abs (t * x ^ m)]
      rw [hmzero] at hsq
      linarith [min_le_right (t ^ 2) 1]
  have htail := sum_tail_square_lower (t := t) hxnonneg hx₁
    (show 2 * m ≤ n + 1 by omega)
  have hampmul := mul_le_mul_of_nonneg_right hamp (geometricVariance_nonneg x (n + 1))
  have hsum : min (t ^ 2) 1 * geometricVariance x (n + 1) / 8 ≤
      ∑ k ∈ Finset.Ico m (n + 1), (t * x ^ k) ^ 2 := by
    linarith
  apply (norm_charFun_powerSum_le_tail n m hxnonneg hx₁
    (hm.trans (by linarith [Real.pi_gt_three]))).trans
  apply Real.exp_le_exp.mpr
  calc
    -(2 / Real.pi ^ 2) * (∑ k ∈ Finset.Ico m (n + 1), (t * x ^ k) ^ 2) ≤
        -(2 / Real.pi ^ 2) * (min (t ^ 2) 1 * geometricVariance x (n + 1) / 8) :=
      mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr (by positivity))
    _ = _ := by ring

end Erdos521
