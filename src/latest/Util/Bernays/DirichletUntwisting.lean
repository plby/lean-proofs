import Util.Bernays.SmoothedFunctional

/-!
# Uniform removal of a small real Dirichlet twist
-/

namespace Bernays

theorem abs_exp_sub_one_le {u r : ℝ} (hur : |u| ≤ r) :
    |Real.exp u - 1| ≤ Real.exp r - 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hur
  have h₁ := Real.exp_le_exp.mpr hlo
  have h₂ := Real.exp_le_exp.mpr hhi
  have hsum : 2 ≤ Real.exp r + Real.exp (-r) := by
    linarith [Real.add_one_le_exp r, Real.add_one_le_exp (-r)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem dirichletTwist_eq_exp (a : ℕ → ℂ) (δ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    dirichletTwist a δ n = a n * (Real.exp (-δ * Real.log (n : ℝ)) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlogC : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnR.le).symm
  have hpow : (n : ℂ) ^ (δ : ℂ) = (Real.exp (δ * Real.log (n : ℝ)) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hnC, hlogC,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 1
    ring_nf
  rw [dirichletTwist, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC,
    Complex.cpow_one, hpow]
  rw [neg_mul, Real.exp_neg, Complex.ofReal_inv]
  field_simp

theorem dirichletTwist_eq_relative_exp (a : ℕ → ℂ) {δ : ℝ} (hδ : δ ≠ 0)
    {n : ℕ} (hn : n ≠ 0) :
    dirichletTwist a δ n = a n * (Real.exp (-1) : ℂ) *
      (Real.exp (-δ * Real.log ((n : ℝ) / Real.exp (1 / δ))) : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : -δ * Real.log (n : ℝ) =
      -1 + -δ * Real.log ((n : ℝ) / Real.exp (1 / δ)) := by
    rw [Real.log_div hnR.ne' (Real.exp_ne_zero _), Real.log_exp]
    field_simp
    ring
  rw [dirichletTwist_eq_exp a δ hn, hlog, Real.exp_add, Complex.ofReal_mul, mul_assoc]

theorem dirichletTwist_sub_bound (a : ℕ → ℂ) {δ L : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : n ≠ 0)
    (hlog : |Real.log ((n : ℝ) / Real.exp (1 / δ))| ≤ L) :
    ‖dirichletTwist a δ n - (Real.exp (-1) : ℂ) * a n‖ ≤
      ‖a n‖ * Real.exp (-1) * (Real.exp (δ * L) - 1) := by
  rw [dirichletTwist_eq_relative_exp a hδ.ne' hn]
  have hid : a n * (Real.exp (-1) : ℂ) *
      (Real.exp (-δ * Real.log ((n : ℝ) / Real.exp (1 / δ))) : ℂ) -
      (Real.exp (-1) : ℂ) * a n =
      a n * (Real.exp (-1) : ℂ) *
        ((Real.exp (-δ * Real.log ((n : ℝ) / Real.exp (1 / δ))) : ℂ) - 1) := by ring
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  apply abs_exp_sub_one_le
  rw [abs_mul, abs_neg, abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_left hlog hδ.le

end Bernays
