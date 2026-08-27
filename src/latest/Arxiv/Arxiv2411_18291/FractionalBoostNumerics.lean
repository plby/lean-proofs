import Arxiv.Arxiv2411_18291.FractionalCorrectionBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp

/-!
# Cancellation of the ambient-size factors in the fractional correction

Clique-count errors have scale `ε*n^(q-r)/(q-r)!`, while the number of
decoding sets has scale `n^q/q!`. At most `n^r` decoding sets through a
fixed clique can contribute. The resulting coefficient loss is a fixed
constant times ε, independent of the ambient size.
-/

noncomputable section

namespace Arxiv2411_18291

def fractionalBoostConstant (q r : ℕ) : ℝ :=
  q.factorial * ((2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)) *
    (q + r).choose r / (q - r).factorial

theorem fractionalBoostConstant_nonneg (q r : ℕ) : 0 ≤ fractionalBoostConstant q r := by
  unfold fractionalBoostConstant
  positivity

theorem fractionalBoost_error_bound {q r n : ℕ} (hqr : r ≤ q) (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (ε * ((n : ℝ) ^ (q - r) / (q - r).factorial) / 2) /
        ((n : ℝ) ^ q / (2 * q.factorial)) *
      ((2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)) *
        ((q + r).choose r * (n - q).choose r : ℕ) ≤ fractionalBoostConstant q r * ε := by
  let M : ℝ := (2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)
  let A : ℝ := (ε * ((n : ℝ) ^ (q - r) / (q - r).factorial) / 2) /
    ((n : ℝ) ^ q / (2 * q.factorial)) * M
  have hA : 0 ≤ A := by dsimp only [A, M]; positivity
  have hchoose : ((n - q).choose r : ℝ) ≤ (n : ℝ) ^ r := by
    exact_mod_cast (Nat.choose_le_pow (n - q) r).trans
      (Nat.pow_le_pow_left (Nat.sub_le n q) r)
  have hpow : (n : ℝ) ^ (q - r) * (n : ℝ) ^ r = (n : ℝ) ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hqr]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hq : (q.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
  have hs : ((q - r).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  change A * ((q + r).choose r * (n - q).choose r : ℕ) ≤ _
  rw [Nat.cast_mul]
  calc
    _ ≤ A * ((q + r).choose r * (n : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hchoose (Nat.cast_nonneg _)) hA
    _ = (ε * q.factorial * M * (q + r).choose r / (q - r).factorial) *
        ((n : ℝ) ^ (q - r) * (n : ℝ) ^ r / (n : ℝ) ^ q) := by
      dsimp only [A]
      field_simp
    _ = _ := by
      rw [hpow, div_self (pow_ne_zero _ hn'), mul_one]
      dsimp only [fractionalBoostConstant, M]
      ring

end Arxiv2411_18291
