/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Fourier expansion for the number of diagonal sextic points modulo a prime.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.FiniteFieldSurface
import ErdosProblems.Erdos477.Counting.PowerSums

namespace Erdos477.Counting

open scoped BigOperators

/-- The complete sextic exponential sum modulo `p`. -/
noncomputable def sexticSum (p : ℕ) [NeZero p] (t : ZMod p) : ℂ :=
  ∑ x : ZMod p, ZMod.stdAddChar (t * x ^ 6)

@[simp] lemma sexticSum_zero (p : ℕ) [NeZero p] : sexticSum p 0 = p := by
  simp [sexticSum]

lemma norm_sexticSum_le (p : ℕ) [Fact p.Prime] (t : ZMod p) (ht : t ≠ 0) :
    ‖sexticSum p t‖ ≤ 7 * Real.sqrt p := by
  have hψ := AddChar.IsPrimitive.of_ne_one ((ZMod.isPrimitive_stdAddChar p) ht)
  have h := norm_power_sum_le 6 ((ZMod.stdAddChar (N := p)).mulShift t) hψ
  simpa only [sexticSum, AddChar.mulShift_apply, ZMod.card, Nat.cast_ofNat,
    show (6 : ℝ) + 1 = 7 by norm_num] using h

lemma sextic_fourier_product (p : ℕ) [NeZero p] (c t : ZMod p) :
    ZMod.stdAddChar (-t * c) * sexticSum p t ^ 2 * sexticSum p (-t) =
      ∑ z : Fin 3 → ZMod p, ZMod.stdAddChar
        (t * (z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 - c)) := by
  let a : Fin 3 → ZMod p := ![t, t, -t]
  have h := Fintype.prod_sum (fun (k : Fin 3) (x : ZMod p) =>
    ZMod.stdAddChar (a k * x ^ 6))
  have hprod : sexticSum p t ^ 2 * sexticSum p (-t) =
      ∑ z : Fin 3 → ZMod p, ZMod.stdAddChar (t * z 0 ^ 6) *
        ZMod.stdAddChar (t * z 1 ^ 6) * ZMod.stdAddChar (-t * z 2 ^ 6) := by
    simpa only [Fin.prod_univ_three, a, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, ← pow_two, sexticSum] using h
  rw [mul_assoc, hprod, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Additive-character orthogonality counts every affine surface point once. -/
theorem sextic_fourier_count (p : ℕ) [NeZero p] (c : ℤ) :
    (∑ t : ZMod p, ZMod.stdAddChar (-t * (c : ZMod p)) *
      sexticSum p t ^ 2 * sexticSum p (-t)) =
      (p : ℂ) * (sexticResidues p c).card := by
  simp_rw [sextic_fourier_product]
  rw [Finset.sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
  simp only [sub_eq_zero, ZMod.card, apply_ite, Nat.cast_zero, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  change ((sexticResidues p c).card : ℂ) * p = (p : ℂ) * (sexticResidues p c).card
  ring

lemma sextic_fourier_error (p : ℕ) [NeZero p] (c : ℤ) :
    (p : ℂ) * (sexticResidues p c).card - (p : ℂ) ^ 3 =
      ∑ t ∈ Finset.univ.erase (0 : ZMod p),
        ZMod.stdAddChar (-t * (c : ZMod p)) * sexticSum p t ^ 2 * sexticSum p (-t) := by
  have h := Finset.sum_erase_add (s := Finset.univ)
    (fun t : ZMod p => ZMod.stdAddChar (-t * (c : ZMod p)) *
      sexticSum p t ^ 2 * sexticSum p (-t)) (Finset.mem_univ 0)
  rw [sextic_fourier_count] at h
  simp only [neg_zero, zero_mul, AddChar.map_zero_eq_one, sexticSum_zero, one_mul] at h
  linear_combination -h

#print axioms sextic_fourier_count
-- 'Erdos477.Counting.sextic_fourier_count' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
