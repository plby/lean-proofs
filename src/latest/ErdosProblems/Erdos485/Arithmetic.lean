import Mathlib

/-!
# Elementary numerical bounds for Erdős Problem 485

This file isolates the natural-number arithmetic used by the induction in the
formal proof.  The deliberately generous bound

`B t = 1 + 32 ^ (2 ^ (t - 3) - 1)`

starts with `B 3 = 2`, grows more than quadratically from that point onward,
and absorbs the exceptional all-zero contribution appearing in the
coefficient-counting argument.
-/

namespace Erdos485

/-- The explicit support bound used in the induction. -/
def B (t : ℕ) : ℕ :=
  1 + 32 ^ (2 ^ (t - 3) - 1)

@[simp] theorem B_zero : B 0 = 2 := by
  norm_num [B]

@[simp] theorem B_one : B 1 = 2 := by
  norm_num [B]

@[simp] theorem B_two : B 2 = 2 := by
  norm_num [B]

@[simp] theorem B_three : B 3 = 2 := by
  norm_num [B]

@[simp] theorem B_four : B 4 = 33 := by
  norm_num [B]

/-- The explicit bound is monotone (in fact this holds even below `3`, where
the truncated subtractions make it constant). -/
theorem B_mono : Monotone B := by
  intro s t hst
  unfold B
  apply Nat.add_le_add_left
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.sub_le_sub_right
  apply Nat.pow_le_pow_right (by norm_num)
  exact Nat.sub_le_sub_right hst 3

/-- Pairwise monotonicity in the range used by the main induction. -/
theorem B_mono_of_three_le {s t : ℕ} (_hs : 3 ≤ s) (hst : s ≤ t) :
    B s ≤ B t :=
  B_mono hst

/-- One-step monotonicity, in a convenient form for recursive arguments. -/
theorem B_le_succ (t : ℕ) : B t ≤ B (t + 1) :=
  B_mono (Nat.le_succ t)

private theorem linear_exponent_le (n : ℕ) :
    3 * n + 5 ≤ 5 * (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
      have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega

/-- The term arising when every auxiliary order is zero is absorbed by `B`.
The division is natural-number division, as it is in the finite counting
argument. -/
theorem all_zero_estimate {t : ℕ} (ht : 4 ≤ t) :
    1 + 8 ^ (t - 2) / 2 ≤ B t := by
  let n := t - 4
  have ht_two : t - 2 = n + 2 := by
    dsimp [n]
    omega
  have ht_three : t - 3 = n + 1 := by
    dsimp [n]
    omega
  have hlhs : 8 ^ (n + 2) / 2 = 2 ^ (3 * n + 5) := by
    rw [show 8 = 2 ^ 3 by norm_num, ← pow_mul]
    rw [show 3 * (n + 2) = (3 * n + 5) + 1 by omega, pow_succ]
    simp
  have hrhs : 32 ^ (2 ^ (n + 1) - 1) =
      2 ^ (5 * (2 ^ (n + 1) - 1)) := by
    rw [show 32 = 2 ^ 5 by norm_num, pow_mul]
  rw [B, ht_two, ht_three, hlhs, hrhs]
  exact Nat.add_le_add_left
    (Nat.pow_le_pow_right (by norm_num) (linear_exponent_le n)) 1

/-- From level `4` onward, the next value of `B` is strictly larger than the
square of the preceding value. -/
theorem B_pred_sq_lt {t : ℕ} (ht : 4 ≤ t) :
    B (t - 1) ^ 2 < B t := by
  have hprev : t - 1 - 3 = t - 4 := by omega
  have hcurr : t - 3 = (t - 4) + 1 := by omega
  have hn : 1 ≤ 2 ^ (t - 4) := Nat.one_le_pow _ _ (by norm_num)
  have hexp : 2 ^ (t - 4) * 2 - 1 =
      (2 ^ (t - 4) - 1) * 2 + 1 := by
    omega
  have hexp_full : 2 ^ (t - 3) - 1 =
      (2 ^ (t - 4) - 1) * 2 + 1 := by
    rw [hcurr, pow_succ, hexp]
  have hrhs : 32 ^ (2 ^ (t - 3) - 1) =
      (32 ^ (2 ^ (t - 4) - 1)) ^ 2 * 32 := by
    rw [hexp_full, pow_add, pow_mul]
    norm_num
  rw [B, B, hprev, hrhs]
  have ha : 1 ≤ 32 ^ (2 ^ (t - 4) - 1) :=
    Nat.one_le_pow _ _ (by norm_num)
  nlinarith

/-- Successor-indexed version of `B_pred_sq_lt`. -/
theorem B_sq_lt_succ {t : ℕ} (ht : 3 ≤ t) :
    B t ^ 2 < B (t + 1) := by
  have hfour : 4 ≤ t + 1 := by omega
  simpa only [Nat.add_sub_cancel] using B_pred_sq_lt hfour

/-- A simpler, looser upper bound useful when only a closed expression is
needed. -/
theorem B_le_coarse (t : ℕ) :
    B t ≤ 1 + 32 ^ (2 ^ t) := by
  unfold B
  apply Nat.add_le_add_left
  apply Nat.pow_le_pow_right (by norm_num)
  exact (Nat.sub_le _ _).trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le t 3))

end Erdos485
