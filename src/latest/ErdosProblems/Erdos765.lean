/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the original gist.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 765.
Informal authors: István Reiman, Paul Erdős, Alfréd Rényi, W. G. Brown;
following the exposition of Martin Aigner and Günter M. Ziegler.
Formal authors: Aristotle, Jeremy Tan Jie Rui (Parcly-Taxel).
Source: https://www.erdosproblems.com/765#post-6480
https://gist.githubusercontent.com/Parcly-Taxel/13d3bd0f1390b0832a42994a09cf91c5/raw/e267a3a494e64019a1a442b3b05438745923883b/Erdos765.lean
Original Lean/Mathlib version: 4.28.0 (the linked editor project).
The original prime_between axiom is discharged using this repository's PNT+ library.
-/
import ErdosProblems.Erdos765.Asymptotics

open SimpleGraph Filter Asymptotics Real

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos765

theorem erdos_765 : (fun n ↦ (extremalNumber n C4 : ℝ)) ~[atTop] fun n ↦ n ^ (3 / 2 : ℝ) / 2 := by
  rw [IsEquivalent, isLittleO_iff]
  intro c hc
  set ε : ℝ := min (c / 4) (1 / 2) with hε_def
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := (min_le_right ..).trans_lt (by norm_num)
  have hεc : 1 - c ≤ (1 - ε) ^ 3 := by
    have : ε ≤ c / 4 := min_le_left ..
    nlinarith [sq_nonneg ε]
  filter_upwards [exists_prime_near_sqrt hε, eventually_rpow_pos,
    eventually_n_le_c_rpow hc] with n ⟨q, hq_prime, hq_le, hq_lower⟩ hn_pos hn_ub
  simp only [Pi.sub_apply, norm_eq_abs, abs_of_pos hn_pos]
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le', ← sub_eq_add_neg, ← one_sub_mul]
    calc
      _ ≤ (1 - ε) ^ 3 * (n ^ (3 / 2 : ℝ) / 2) := by nlinarith
      _ ≤ _ := lower_bound_from_prime hε1 hq_lower
      _ ≤ _ := by
        rw [nat_div_two_cast, Nat.cast_le]
        exact extremalNumber_C4_ge_of_isPrimePow_le hq_prime.isPrimePow hq_le
  · rw [sub_le_iff_le_add']
    exact extremalNumber_C4_le_real.trans <| upper_bound_le_rpow_add.trans <|
      add_le_add_right hn_ub _

#print axioms erdos_765
-- 'Erdos765.erdos_765' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos765
