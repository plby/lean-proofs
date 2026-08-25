import ErdosProblems.Erdos1141.BurgessProgressions
import ErdosProblems.Erdos1141.QuadraticReducedCharacter

/-!
# Elementary interval bounds and reduced characters
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem abs_quadratic_interval_le_length {q : ℕ}
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) (M H : ℕ) :
    |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H := by
  calc
    _ ≤ ∑ i ∈ Finset.range H, |χ (M + i : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hχ (M + i : ℕ) with h | h | h <;> rw [h] <;> norm_num
    _ = _ := by simp

theorem sum_zmod_eq_sum_range {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ a : ZMod q, f a) = ∑ i ∈ Finset.range q, f (i : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a _
    exact Finset.mem_range.mpr a.val_lt
  · exact (ZMod.val_injective q).injOn
  · intro i hi
    exact ⟨(i : ZMod q), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.mp hi)⟩
  · intro a _
    rw [ZMod.natCast_zmod_val]

theorem sum_quadratic_period_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) (M : ℕ) :
    (∑ i ∈ Finset.range q, χ (M + i : ℕ)) = 0 := by
  calc
    _ = ∑ a : ZMod q, χ ((M : ZMod q) + a) := by
      rw [sum_zmod_eq_sum_range]
      simp only [Nat.cast_add]
    _ = ∑ a : ZMod q, χ a := Equiv.sum_comp (Equiv.addLeft (M : ZMod q)) χ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

theorem abs_quadratic_interval_le_modulus {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1) (M H : ℕ) :
    |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ q := by
  have hf (n : ℕ) : |χ (n : ZMod q)| ≤ 1 := by
    rcases hχ (n : ZMod q) with h | h | h <;> norm_num [h]
  have hblock (K : ℕ) : |∑ i ∈ Finset.range q, χ (K + i : ℕ)| ≤ (0 : ℝ) := by
    rw [sum_quadratic_period_eq_zero χ hχ1 K, abs_zero]
  simpa only [zero_div, mul_zero, zero_add] using
    abs_sum_range_le_blocks (fun n => χ (n : ZMod q)) hf (NeZero.pos q)
      (le_refl (0 : ℝ)) hblock M H

theorem interval_bound_extend_to_short {q : ℕ}
    (χ : DirichletCharacter ℝ q) (hχ : χ.IsQuadratic) {T b : ℝ}
    (hT0 : 0 ≤ T) (hb : 0 ≤ b)
    (hbound : ∀ M H : ℕ, T ≤ H → |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H * b)
    (M H : ℕ) : |∑ i ∈ Finset.range H, χ (M + i : ℕ)| ≤ H * b + T := by
  by_cases hT : T ≤ H
  · exact (hbound M H hT).trans (le_add_of_nonneg_right hT0)
  · have hlen := abs_quadratic_interval_le_length χ hχ M H
    have hprod : 0 ≤ (H : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
    linarith

end Pollack17.Burgess
