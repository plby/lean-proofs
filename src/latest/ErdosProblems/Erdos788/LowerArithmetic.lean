import ErdosProblems.Erdos788.SparseNeighborhood
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic estimates for the lower bound

These lemmas turn the minimal power-of-two sampling scale into a logarithmic
degree cutoff.  They are kept separate from the finite graph argument.
-/

namespace Erdos788

/-- The average-degree cutoff forced by a minimal sampling exponent grows
at least like the square root of `N / b`. -/
theorem cutoff_growth {N b q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hupper : N * q ^ 2 < 8 * b ^ 3) :
    8 * N < b * (8 * (b + 1) / q + 1) ^ 2 := by
  let D := 8 * (b + 1) / q
  have hdiv : 8 * (b + 1) < q * (D + 1) := by
    exact Nat.lt_mul_div_succ _ hq
  have hsq : (8 * (b + 1)) ^ 2 < (q * (D + 1)) ^ 2 :=
    Nat.pow_lt_pow_left hdiv (by norm_num)
  have hchain : N * (8 * (b + 1)) ^ 2 <
      (8 * b ^ 3) * (D + 1) ^ 2 := by
    calc
      N * (8 * (b + 1)) ^ 2 < N * (q * (D + 1)) ^ 2 :=
        (Nat.mul_lt_mul_left hN).2 hsq
      _ = (N * q ^ 2) * (D + 1) ^ 2 := by ring
      _ < (8 * b ^ 3) * (D + 1) ^ 2 :=
        (Nat.mul_lt_mul_right (by positivity : 0 < (D + 1) ^ 2)).2 hupper
  have hcancel : 8 * N * (b + 1) ^ 2 < b ^ 3 * (D + 1) ^ 2 := by
    nlinarith
  have hb : 0 < b := by
    have hleft : 0 < N * q ^ 2 := Nat.mul_pos hN (pow_pos hq _)
    have hright : 0 < 8 * b ^ 3 := hleft.trans hupper
    by_contra hb
    simp only [Nat.not_lt, Nat.le_zero] at hb
    simp [hb] at hright
  have hbsq : b ^ 2 ≤ (b + 1) ^ 2 := by nlinarith
  have hmul : b ^ 2 * (8 * N) < b ^ 2 * (b * (D + 1) ^ 2) := by
    calc
      b ^ 2 * (8 * N) ≤ 8 * N * (b + 1) ^ 2 := by
        nlinarith
      _ < b ^ 3 * (D + 1) ^ 2 := hcancel
      _ = b ^ 2 * (b * (D + 1) ^ 2) := by ring
  have hb2 : 0 < b ^ 2 := by positivity
  have := (Nat.mul_lt_mul_left hb2).mp hmul
  simpa only [D] using! this

/-- In the small-palette branch, the cutoff furnished by minimal sampling
has logarithm comparable with `log N`. -/
theorem log_le_eight_log_cutoff {N b d : ℕ} (hN : 2 ≤ N)
    (hcut : 8 * N < b * d ^ 2)
    (hb : (b : ℝ) ≤ Real.sqrt ((N : ℝ) * Real.log (N : ℝ))) :
    Real.log (N : ℝ) ≤ 8 * Real.log (d : ℝ) := by
  let n : ℝ := N
  let br : ℝ := b
  let dr : ℝ := d
  let L : ℝ := Real.log n
  let s : ℝ := Real.sqrt n
  have hn : 0 < n := by positivity
  have hnone : (1 : ℝ) ≤ n := by
    simpa [n] using! (show (1 : ℝ) ≤ (N : ℝ) by
      exact_mod_cast (show 1 ≤ N by omega))
  have hL : 0 ≤ L := Real.log_nonneg hnone
  have htarget : 0 ≤ n * L := mul_nonneg hn.le hL
  have htargetSq : (Real.sqrt (n * L)) ^ 2 = n * L := Real.sq_sqrt htarget
  have hb0 : 0 ≤ br := by positivity
  have hbSq : br ^ 2 ≤ n * L := by
    calc
      br ^ 2 ≤ (Real.sqrt (n * L)) ^ 2 :=
        (sq_le_sq₀ hb0 (Real.sqrt_nonneg _)).2 (by simpa [br, n, L] using! hb)
      _ = n * L := htargetSq
  have hcutR : (8 : ℝ) * n < br * dr ^ 2 := by
    simpa [n, br, dr] using!
      (show (8 : ℝ) * (N : ℝ) < (b : ℝ) * (d : ℝ) ^ 2 by
        exact_mod_cast hcut)
  have hcutSq : ((8 : ℝ) * n) ^ 2 < (br * dr ^ 2) ^ 2 := by
    simpa [pow_two] using! mul_self_lt_mul_self (by positivity) hcutR
  have hfirst : ((8 : ℝ) * n) ^ 2 < (n * L) * dr ^ 4 := by
    calc
      ((8 : ℝ) * n) ^ 2 < (br * dr ^ 2) ^ 2 := hcutSq
      _ = br ^ 2 * dr ^ 4 := by ring
      _ ≤ (n * L) * dr ^ 4 :=
        mul_le_mul_of_nonneg_right hbSq (by positivity)
  have hfirst' : n * ((64 : ℝ) * n) < n * (L * dr ^ 4) := by
    nlinarith
  have h64 : (64 : ℝ) * n < L * dr ^ 4 :=
    lt_of_mul_lt_mul_left hfirst' hn.le
  have hlogSqrt : L ≤ 2 * s := by
    simpa [L, n, s, Real.sqrt_eq_rpow, mul_comm] using!
      (Real.log_natCast_le_rpow_div N (by norm_num : (0 : ℝ) < 1 / 2))
  have h64' : (64 : ℝ) * n < (2 * s) * dr ^ 4 :=
    h64.trans_le (mul_le_mul_of_nonneg_right hlogSqrt (by positivity))
  have hspos : 0 < s := Real.sqrt_pos.2 hn
  have hsSq : s ^ 2 = n := Real.sq_sqrt hn.le
  have hcancelForm : (2 * s) * (32 * s) < (2 * s) * dr ^ 4 := by
    nlinarith
  have h32 : (32 : ℝ) * s < dr ^ 4 :=
    lt_of_mul_lt_mul_left hcancelForm (by positivity)
  have hsq2 : ((32 : ℝ) * s) ^ 2 < (dr ^ 4) ^ 2 := by
    simpa [pow_two] using! mul_self_lt_mul_self (by positivity) h32
  have hNd : n < dr ^ 8 := by
    nlinarith
  have hd : 0 < d := by
    by_contra hd
    simp only [Nat.not_lt, Nat.le_zero] at hd
    simp [hd] at hcut
  have hdr : 0 < dr := by
    simpa [dr] using! (show (0 : ℝ) < (d : ℝ) by positivity)
  calc
    Real.log (N : ℝ) = L := by rfl
    _ ≤ Real.log (dr ^ 8) := Real.log_le_log hn hNd.le
    _ = 8 * Real.log (d : ℝ) := by
      rw [Real.log_pow]
      norm_num [dr]

end Erdos788
