/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ErdosProblems.Erdos230.Angular

/-!
# The final elementary asymptotics for Erdős Problem 230

The analytic construction uses the integer scales
`n = m^18`, `s = m^12`, and `K = m^15`.  All analytic and probabilistic error
terms are absorbed into `2 * m^8`.  This file proves that the resulting explicit
bound implies the one-sided ultraflat statement needed for Problem 230.
-/

namespace Erdos230

noncomputable section

/-- The concrete output expected from the Gaussian--Poisson and finite-sign
construction.  The quantifier `M` makes the examples arbitrarily large. -/
def HasPowerUpperExamples : Prop :=
  ∀ M : ℕ, ∃ m : ℕ, max 2 M ≤ m ∧
    ∃ a : Fin (m ^ 18 + 1) → ℂ, IsUnimodular a ∧
      ∀ theta : ℝ, ‖zerothValue a theta‖ ≤
        (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8

lemma sqrt_nat_pow_eighteen (m : ℕ) :
    Real.sqrt ((m ^ 18 : ℕ) : ℝ) = (m : ℝ) ^ 9 := by
  rw [Nat.cast_pow]
  have h : (m : ℝ) ^ 18 = ((m : ℝ) ^ 9) ^ 2 := by ring
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

/-- A main term `m^9 = sqrt (m^18)` and error `m^8` give relative error
tending to zero.  Removing the constant coefficient contributes one more,
which is absorbed by the same comparison. -/
theorem hasAngularUltraflatUpper_of_power_examples
    (hpower : HasPowerUpperExamples) : HasAngularUltraflatUpper := by
  intro epsilon hepsilon N
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 3 / epsilon < k := exists_nat_gt (3 / epsilon)
  obtain ⟨m, hm, a, ha, hbound⟩ := hpower (max N k)
  have hm2 : 2 ≤ m := (le_max_left 2 (max N k)).trans hm
  have hmN : N ≤ m :=
    le_trans (le_trans (le_max_left N k) (le_max_right 2 (max N k))) hm
  have hmk : k ≤ m :=
    le_trans (le_trans (le_max_right N k) (le_max_right 2 (max N k))) hm
  refine ⟨m ^ 18, ?_, tailCoeffs a, ?_, ?_⟩
  · exact max_le
      (le_trans hm2 (Nat.le_pow (a := m) (b := 18) (by norm_num)))
      (le_trans hmN (Nat.le_pow (a := m) (b := 18) (by norm_num)))
  · intro i
    exact ha i.succ
  · intro theta
    have htail := norm_angularValue_tail_le a (by rw [ha 0]) theta
    have hraw : ‖angularValue (tailCoeffs a) theta‖ ≤
        (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8 + 1 := by
      linarith [hbound theta]
    have hmreal : 3 / epsilon < (m : ℝ) :=
      hk.trans_le (by exact_mod_cast hmk)
    have hepsm : 3 < epsilon * (m : ℝ) := by
      calc
        3 = epsilon * (3 / epsilon) := by field_simp
        _ < epsilon * (m : ℝ) := mul_lt_mul_of_pos_left hmreal hepsilon
    have hmone : 1 ≤ (m : ℝ) ^ 8 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      exact one_le_pow₀ this
    have herr : 2 * (m : ℝ) ^ 8 + 1 ≤ epsilon * (m : ℝ) ^ 9 := by
      calc
        2 * (m : ℝ) ^ 8 + 1 ≤ 3 * (m : ℝ) ^ 8 := by linarith
        _ ≤ (epsilon * (m : ℝ)) * (m : ℝ) ^ 8 := by gcongr
        _ = epsilon * (m : ℝ) ^ 9 := by ring
    rw [sqrt_nat_pow_eighteen]
    calc
      ‖angularValue (tailCoeffs a) theta‖ ≤
          (m : ℝ) ^ 9 + (2 * (m : ℝ) ^ 8 + 1) := by
        simpa [add_assoc] using hraw
      _ ≤ (m : ℝ) ^ 9 + epsilon * (m : ℝ) ^ 9 := by gcongr
      _ = (1 + epsilon) * (m : ℝ) ^ 9 := by ring

end

end Erdos230
