import Arxiv.Arxiv2411_18291.ShiftedChooseBounds
import Arxiv.Arxiv2411_18291.SharpFractionalCorrection

/-! # The sharp, size-independent cost of fractional regularization -/

namespace Arxiv2411_18291

theorem fractionalBoost_mass_error_bound {q r n : ℕ} (hqr : r ≤ q) (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (ε * ((n : ℝ) ^ (q - r) / (q - r).factorial) / 2) /
        ((n : ℝ) ^ q / (2 * q.factorial)) *
      ((2 : ℝ) ^ r * (n - q).choose r) ≤ (2 : ℝ) ^ r * q.choose r * ε := by
  let A : ℝ := (ε * ((n : ℝ) ^ (q - r) / (q - r).factorial) / 2) /
    ((n : ℝ) ^ q / (2 * q.factorial))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hchoose := shifted_choose_upper n q r
  have hpow : (n : ℝ) ^ (q - r) * (n : ℝ) ^ r = (n : ℝ) ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hqr]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hfac : (q.choose r : ℝ) * r.factorial * (q - r).factorial = q.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hqr
  have hr : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hs : ((q - r).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  change A * ((2 : ℝ) ^ r * (n - q).choose r) ≤ _
  calc
    _ ≤ A * ((2 : ℝ) ^ r * ((n : ℝ) ^ r / r.factorial)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hchoose (by positivity)) hA
    _ = (2 : ℝ) ^ r * ε * (q.factorial / (r.factorial * (q - r).factorial)) *
        ((n : ℝ) ^ (q - r) * (n : ℝ) ^ r / (n : ℝ) ^ q) := by
      dsimp only [A]
      field_simp
    _ = _ := by
      rw [hpow, div_self (pow_ne_zero _ hn'), mul_one, ← hfac]
      field_simp

end Arxiv2411_18291
