/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An elementary Gauss-sum bound for power exponential sums over a finite field.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PowerCharacters

namespace Erdos477.Counting

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma sum_field_eq_sum_units_add (f : F → ℂ) :
    (∑ x : F, f x) = (∑ u : Fˣ, f u) + f 0 := by
  classical
  have hsum : (∑ u : Fˣ, f u) = ∑ x ∈ Finset.univ.erase 0, f x := by
    apply Finset.sum_bij (fun (u : Fˣ) _ => (u : F))
    · intro u _
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact Units.ne_zero u
    · intro u _ v _ h
      exact Units.ext h
    · intro x hx
      refine ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, ?_⟩
      rfl
    · intro u _
      rfl
  rw [hsum]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ 0)).symm

lemma gaussSum_eq_sum_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ u : Fˣ, χ u * ψ u := by
  rw [gaussSum, sum_field_eq_sum_units_add]
  simp only [MulChar.map_zero, zero_mul, add_zero]

lemma sum_powerCharacters_gaussSum (d : ℕ) (ψ : AddChar F ℂ) :
    (∑ χ : powerCharacters F d, gaussSum (χ.val : MulChar F ℂ) ψ) =
      ∑ u : Fˣ, ψ ((u : F) ^ d) := by
  classical
  simp_rw [gaussSum_eq_sum_units]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_powerCharacters_eq_card_powerFiber]
  have h := Finset.sum_fiberwise' (Finset.univ : Finset Fˣ) (fun u => u ^ d)
    (fun u : Fˣ => ψ (u : F))
  simpa only [Finset.sum_const, nsmul_eq_mul, Units.val_pow_eq_pow_val] using h

omit [DecidableEq F] in
/-- Expansion of a power exponential sum into at most `d` Gauss sums,
plus the contribution from zero. -/
theorem power_sum_eq_gaussSums (d : ℕ) [NeZero d] (ψ : AddChar F ℂ) :
    (∑ x : F, ψ (x ^ d)) =
      1 + ∑ χ : powerCharacters F d, gaussSum (χ.val : MulChar F ℂ) ψ := by
  classical
  rw [sum_field_eq_sum_units_add, sum_powerCharacters_gaussSum]
  simp only [zero_pow (NeZero.ne d), AddChar.map_zero_eq_one, add_comm]

omit [DecidableEq F] in
lemma one_le_sqrt_card_field : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
  rw [Real.one_le_sqrt]
  exact_mod_cast Fintype.card_pos

omit [DecidableEq F] in
lemma norm_gaussSum_le (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ≤ Real.sqrt (Fintype.card F) := by
  by_cases hχ : χ = 1
  · have hne : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ one_ne_zero
    rw [hχ, gaussSum_one_left hne, norm_neg, norm_one]
    exact one_le_sqrt_card_field
  · exact (norm_gaussSum χ ψ hχ hψ).le

omit [DecidableEq F] in
/-- A coefficient-uniform square-root bound for a power exponential sum.
The harmless constant `d+1` avoids needing cancellation of the trivial
character term. -/
theorem norm_power_sum_le (d : ℕ) [NeZero d] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖∑ x : F, ψ (x ^ d)‖ ≤ ((d : ℝ) + 1) * Real.sqrt (Fintype.card F) := by
  rw [power_sum_eq_gaussSums]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖∑ χ : powerCharacters F d, gaussSum (χ.val : MulChar F ℂ) ψ‖ :=
      norm_add_le _ _
    _ ≤ 1 + ∑ χ : powerCharacters F d, ‖gaussSum (χ.val : MulChar F ℂ) ψ‖ := by
      rw [norm_one]
      exact add_le_add le_rfl (norm_sum_le Finset.univ
        (fun χ : powerCharacters F d => gaussSum (χ.val : MulChar F ℂ) ψ))
    _ ≤ 1 + (Fintype.card (powerCharacters F d) : ℝ) * Real.sqrt (Fintype.card F) := by
      gcongr
      calc
        _ ≤ ∑ _χ : powerCharacters F d, Real.sqrt (Fintype.card F) :=
          Finset.sum_le_sum (fun χ _ => norm_gaussSum_le χ.val ψ hψ)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 1 + (d : ℝ) * Real.sqrt (Fintype.card F) := by
      gcongr
      exact_mod_cast card_powerCharacters_le F d
    _ ≤ _ := by
      have h := one_le_sqrt_card_field (F := F)
      nlinarith

#print axioms norm_power_sum_le
-- 'Erdos477.Counting.norm_power_sum_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
