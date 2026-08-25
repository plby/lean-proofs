import ErdosProblems.Erdos67.MRGSA9SmallPrimeDeletion
import ErdosProblems.Erdos67.EulerLower

/-!
# A zeta majorant for ordinary bounded coefficients
-/

open scoped LSeries.notation

namespace Erdos67

noncomputable section

/-- Every Dirichlet series with one-bounded positive-index coefficients is
majorized on `Re s > 1` by zeta on the corresponding real line. -/
theorem norm_LSeries_le_norm_riemannZeta_real_of_bounded
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖LSeries a ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      ‖riemannZeta (sigma : ℂ)‖ := by
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  let one : ℕ → ℂ := fun _ ↦ 1
  have hs : 1 < s.re := by simpa [s] using hsigma
  have ha' : ∀ n, n ≠ 0 → ‖a n‖ ≤ 1 := by
    intro n hn
    exact ha n (Nat.pos_of_ne_zero hn)
  have hsumA : LSeriesSummable a s :=
    LSeriesSummable_of_bounded_of_one_lt_re ha' hs
  have hone' : ∀ n, n ≠ 0 → ‖one n‖ ≤ 1 := by simp [one]
  have hsumOne : LSeriesSummable one (sigma : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re hone' (by simpa using hsigma)
  have htermOne (n : ℕ) :
      ‖LSeries.term one (sigma : ℂ) n‖ = 1 / (n : ℝ) ^ sigma := by
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn, Real.zero_rpow (by linarith : sigma ≠ 0)]
    · simp [hn, one]
  unfold LSeries
  calc
    ‖∑' n : ℕ, LSeries.term a s n‖ ≤
        ∑' n : ℕ, ‖LSeries.term a s n‖ :=
      norm_tsum_le_tsum_norm hsumA.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term one (sigma : ℂ) n‖ := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
        by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, if_false, one, norm_one, s, Complex.add_re,
            Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
          simpa only [add_zero] using div_le_div_of_nonneg_right (ha' n hn)
            (Real.rpow_nonneg (Nat.cast_nonneg n) sigma)
      · exact hsumA.norm
      · exact hsumOne.norm
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ sigma := tsum_congr htermOne
    _ = ‖riemannZeta (sigma : ℂ)‖ :=
      (EulerLower.norm_riemannZeta_real_eq_realZetaSum hsigma).symm

end

end Erdos67
