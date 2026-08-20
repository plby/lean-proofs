/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteTCover

/-!
# Erdős Problem 446: elementary numerical bounds for the discrete cover

This file collects the small natural-number exponential estimates used when
the dyadic exceptional cover is truncated.  Keeping them separate prevents
the combinatorial proof from being obscured by inductions on powers of two.
-/

namespace Erdos446

/-- Past depth six, the number of possible preceding depths fits strictly
inside the power-of-two window of depth `H - 3`. -/
theorem depth_sub_one_lt_two_pow_sub_three {H : ℕ} (hH : 6 ≤ H) :
    H - 1 < 2 ^ (H - 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hH
  have hsubOne : 6 + n - 1 = n + 5 := by omega
  have hsubThree : 6 + n - 3 = n + 3 := by omega
  rw [hsubOne, hsubThree]
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.succ_add, pow_succ]
      omega

/-- For every exponent at least six, `2^A` dominates the linear term
`2A`, even after losing two powers of two. -/
theorem two_mul_le_two_pow_sub_two {A : ℕ} (hA : 6 ≤ A) :
    2 * A ≤ 2 ^ (A - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hA
  have hsubTwo : 6 + n - 2 = n + 4 := by omega
  rw [hsubTwo]
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.succ_add, pow_succ]
      omega

/-- The slightly shifted linear term used for the far dyadic tail is also
absorbed by the same exponential once the depth is at least eight. -/
theorem add_two_le_two_pow_sub_two {d : ℕ} (hd : 8 ≤ d) :
    d + 2 ≤ 2 ^ (d - 2) := by
  calc
    d + 2 ≤ 2 * d := by omega
    _ ≤ 2 ^ (d - 2) := two_mul_le_two_pow_sub_two (by omega)

/-- Three quarters of a power of two is strictly smaller than the whole
power.  The hypothesis makes the truncated exponent exact. -/
theorem three_mul_two_pow_sub_two_lt_two_pow {A : ℕ} (hA : 2 ≤ A) :
    3 * 2 ^ (A - 2) < 2 ^ A := by
  have hsplit : A - 2 + 2 = A := Nat.sub_add_cancel hA
  calc
    3 * 2 ^ (A - 2) < 4 * 2 ^ (A - 2) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = 2 ^ 2 * 2 ^ (A - 2) := by norm_num
    _ = 2 ^ (2 + (A - 2)) := (pow_add 2 2 (A - 2)).symm
    _ = 2 ^ A := by rw [Nat.add_comm, hsplit]

end Erdos446
