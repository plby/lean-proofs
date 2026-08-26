import ErdosProblems.Erdos69.FiniteExpectation

/-!
# Exponential moments of the finite independent model
-/

open scoped BigOperators

namespace Erdos69.Elementary

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem exp_le_one_add_add_square {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hx)
  simp only [Real.norm_eq_abs, sq_abs] at h
  have hle := le_abs_self (Real.exp x - 1 - x)
  linarith

theorem mean_exp_le (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ)
    (hmean : μ.mean X = 0) (hsmall : ∀ x, |t * X x| ≤ 1) :
    μ.mean (fun x ↦ Real.exp (t * X x)) ≤
      Real.exp (t ^ 2 * μ.mean (fun x ↦ X x ^ 2)) := by
  calc
    μ.mean (fun x ↦ Real.exp (t * X x)) ≤
        μ.mean (fun x ↦ 1 + t * X x + (t * X x) ^ 2) :=
      μ.mean_mono (fun x ↦ exp_le_one_add_add_square (hsmall x))
    _ = 1 + t ^ 2 * μ.mean (fun x ↦ X x ^ 2) := by
      simp only [mul_pow, μ.mean_add, μ.mean_const, μ.mean_const_mul, hmean,
        mul_zero, add_zero]
    _ ≤ Real.exp (t ^ 2 * μ.mean (fun x ↦ X x ^ 2)) := by
      simpa only [add_comm] using Real.add_one_le_exp (t ^ 2 * μ.mean (fun x ↦ X x ^ 2))

theorem categorical_mean_exp_le {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (hcard : Fintype.card ι ≤ p) (c : ι → ℝ)
    (hzero : ∑ i, c i = 0) (t ε : ℝ)
    (hmass : ∑ i, |c i| ≤ ε) (hsmall : |t| * ε ≤ 1) :
    (categorical ι p hp hcard).mean (fun x ↦ Real.exp (t * optionalValue c x)) ≤
      Real.exp (t ^ 2 * ε ^ 2 / p) := by
  have hε : 0 ≤ ε := (Finset.sum_nonneg fun i _ ↦ abs_nonneg (c i)).trans hmass
  have hm : (categorical ι p hp hcard).mean (optionalValue c) = 0 := by
    rw [categorical_mean, hzero, zero_div]
  have hs (x : Option ι) : |t * optionalValue c x| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left
      ((optionalValue_abs_le c x).trans hmass) (abs_nonneg t)).trans hsmall
  have hvar : (categorical ι p hp hcard).mean (fun x ↦ optionalValue c x ^ 2) ≤ ε ^ 2 / p := by
    rw [categorical_mean_square]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (sum_sq_le_mass_sq c).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ ↦ abs_nonneg (c i)) hmass 2)
  calc
    _ ≤ Real.exp (t ^ 2 *
        (categorical ι p hp hcard).mean (fun x ↦ optionalValue c x ^ 2)) :=
      mean_exp_le _ _ t hm hs
    _ ≤ Real.exp (t ^ 2 * ε ^ 2 / p) := by
      apply Real.exp_le_exp.mpr
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hvar (sq_nonneg t)

theorem independentProduct_mean_exp_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (X : ι → Ω → ℝ) (t : ℝ) :
    (independentProduct μ).mean (fun x ↦ Real.exp (t * ∑ i, X i (x i))) =
      ∏ i, (μ i).mean (fun x ↦ Real.exp (t * X i x)) := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  exact independentProduct_mean_prod μ (fun i x ↦ Real.exp (t * X i x))

theorem independentProduct_mean_exp_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (X : ι → Ω → ℝ) (t : ℝ) (v : ι → ℝ)
    (hlocal : ∀ i, (μ i).mean (fun x ↦ Real.exp (t * X i x)) ≤ Real.exp (v i)) :
    (independentProduct μ).mean (fun x ↦ Real.exp (t * ∑ i, X i (x i))) ≤
      Real.exp (∑ i, v i) := by
  rw [independentProduct_mean_exp_sum, Real.exp_sum]
  exact Finset.prod_le_prod
    (fun i _ ↦ (μ i).mean_nonneg (fun x ↦ (Real.exp_pos _).le))
    (fun i _ ↦ hlocal i)

end FiniteLaw

end Erdos69.Elementary
