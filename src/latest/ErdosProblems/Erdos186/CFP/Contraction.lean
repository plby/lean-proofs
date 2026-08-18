/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# A logarithmic bound for repeated volume contractions

This file records the elementary numerical estimate used to bound the number
of steps in a density-reduction iteration.  If a positive natural-valued
quantity loses at least a quarter of its value at every step, then the
iteration has length at most three times the binary logarithm of its initial
value (up to an additive constant).

The proof stays in `ℕ`: three contractions by a factor at most `3 / 4`
combine to a contraction by a factor at most `1 / 2`.
-/

namespace Erdos186.CFP

/-! ## A pointwise contraction potential -/

/-- A natural-valued potential which decreases at every `3 / 4` contraction.

Cubing turns the factor `3 / 4` into `27 / 64 < 1 / 2`; the binary logarithm
therefore loses at least one at each contraction. -/
def contractionRank (v : ℕ) : ℕ :=
  Nat.log 2 (v ^ 3)

/-- The contraction potential is monotone in the underlying value. -/
lemma contractionRank_mono {a b : ℕ} (hab : a ≤ b) :
    contractionRank a ≤ contractionRank b := by
  exact Nat.log_mono_right (Nat.pow_le_pow_left hab 3)

/-- A positive `3 / 4` contraction strictly decreases `contractionRank`. -/
lemma contractionRank_lt_of_four_mul_le_three_mul
    {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) (hab : 4 * a ≤ 3 * b) :
    contractionRank a < contractionRank b := by
  have hcubed : (4 * a) ^ 3 ≤ (3 * b) ^ 3 :=
    Nat.pow_le_pow_left hab 3
  have hscaled : 64 * a ^ 3 ≤ 27 * b ^ 3 := by
    simpa [mul_pow] using hcubed
  have hdouble : a ^ 3 * 2 ≤ b ^ 3 := by
    omega
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero 3 (Nat.ne_of_gt ha)
  calc
    contractionRank a = Nat.log 2 (a ^ 3) := rfl
    _ < Nat.log 2 (a ^ 3) + 1 := Nat.lt_succ_self _
    _ = Nat.log 2 (a ^ 3 * 2) :=
      (Nat.log_mul_base Nat.one_lt_two ha3).symm
    _ ≤ Nat.log 2 (b ^ 3) := Nat.log_mono_right hdouble
    _ = contractionRank b := rfl

/-- If `v ≤ n`, its contraction potential is bounded by three times one
plus the binary logarithm of `n`. -/
lemma contractionRank_le_three_mul_log_add_one
    {v n : ℕ} (hvn : v ≤ n) :
    contractionRank v ≤ 3 * (Nat.log 2 n + 1) := by
  have hnle : n ≤ 2 ^ (Nat.log 2 n + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hcubes : n ^ 3 ≤ (2 ^ (Nat.log 2 n + 1)) ^ 3 :=
    Nat.pow_le_pow_left hnle 3
  calc
    contractionRank v ≤ contractionRank n := contractionRank_mono hvn
    _ ≤ Nat.log 2 ((2 ^ (Nat.log 2 n + 1)) ^ 3) :=
      Nat.log_mono_right hcubes
    _ = 3 * (Nat.log 2 n + 1) := by
      rw [← pow_mul, Nat.log_pow Nat.one_lt_two]
      omega

/-! ## A finite sequence estimate -/

/-- Three successive `3 / 4` contractions decrease a natural-valued quantity
by at least a factor of two. -/
lemma two_mul_le_of_three_contractions {a b c d : ℕ}
    (hab : 4 * b ≤ 3 * a) (hbc : 4 * c ≤ 3 * b)
    (hcd : 4 * d ≤ 3 * c) :
    2 * d ≤ a := by
  omega

/-- After `j` blocks of three contraction steps, the sampled value, multiplied
by `2 ^ j`, is no larger than the initial value. -/
lemma pow_two_mul_sample_le
    (v : ℕ → ℕ) (k : ℕ)
    (hcontract : ∀ i < k, 4 * v (i + 1) ≤ 3 * v i) :
    ∀ j, 3 * j ≤ k → 2 ^ j * v (3 * j) ≤ v 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hsj
      have hj0 : 3 * j < k := by omega
      have hj1 : 3 * j + 1 < k := by omega
      have hj2 : 3 * j + 2 < k := by omega
      have hthree' : 2 * v (3 * j + 3) ≤ v (3 * j) := by
        refine two_mul_le_of_three_contractions
          (a := v (3 * j)) (b := v (3 * j + 1))
          (c := v (3 * j + 2)) (d := v (3 * j + 3)) ?_ ?_ ?_
        · exact hcontract (3 * j) hj0
        · simpa [Nat.add_assoc] using hcontract (3 * j + 1) hj1
        · simpa [Nat.add_assoc] using hcontract (3 * j + 2) hj2
      have hthree : 2 * v (3 * (j + 1)) ≤ v (3 * j) := by
        simpa only [Nat.mul_succ] using hthree'
      calc
        2 ^ (j + 1) * v (3 * (j + 1)) =
            2 ^ j * (2 * v (3 * (j + 1))) := by
              rw [pow_succ]
              ring
        _ ≤ 2 ^ j * v (3 * j) := Nat.mul_le_mul_left _ hthree
        _ ≤ v 0 := ih (by omega)

/-- A positive natural-valued sequence can undergo at most
`3 * (Nat.log 2 (v 0) + 1)` successive `3 / 4` contractions.

The assumptions are required only on indices occurring in the finite prefix
from `0` through `k`. -/
theorem contraction_length_le_three_mul_log_add_one
    (v : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ i ≤ k, 0 < v i)
    (hcontract : ∀ i < k, 4 * v (i + 1) ≤ 3 * v i) :
    k ≤ 3 * (Nat.log 2 (v 0) + 1) := by
  let q := k / 3
  have hqk : 3 * q ≤ k := by
    dsimp [q]
    omega
  have hsample : 2 ^ q * v (3 * q) ≤ v 0 :=
    pow_two_mul_sample_le v k hcontract q hqk
  have hpow : 2 ^ q ≤ v 0 := by
    calc
      2 ^ q = 2 ^ q * 1 := by simp
      _ ≤ 2 ^ q * v (3 * q) :=
        Nat.mul_le_mul_left _ (hpos (3 * q) hqk)
      _ ≤ v 0 := hsample
  have hqlog : q ≤ Nat.log 2 (v 0) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  dsimp [q] at hqlog
  omega

end Erdos186.CFP
