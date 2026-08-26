/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Selected sextic points in integer coordinates, including the zero middle-coordinate exception.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Diagonal
import ErdosProblems.Erdos477.Decidable
import ErdosProblems.Erdos477.Counting.IntegerBox

namespace Erdos477

def IntegerDiagonalPoint (c : ℤ) (z : Fin 3 → ℤ) : Prop :=
  1 ≤ z 0 ∧ 0 ≤ z 1 ∧ 0 ≤ z 2 ∧ z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c

lemma IntegerDiagonalPoint.nonnegative {c : ℤ} {z : Fin 3 → ℤ}
    (h : IntegerDiagonalPoint c z) (i : Fin 3) : 0 ≤ z i := by
  fin_cases i
  · exact (by decide : (0 : ℤ) ≤ 1).trans h.1
  · exact h.2.1
  · exact h.2.2.1

lemma IntegerDiagonalPoint.cast_toNat {c : ℤ} {z : Fin 3 → ℤ}
    (h : IntegerDiagonalPoint c z) (i : Fin 3) : ((z i).toNat : ℤ) = z i := by
  have hi := h.nonnegative i
  omega

lemma IntegerDiagonalPoint.toNat {c : ℤ} {z : Fin 3 → ℤ}
    (h : IntegerDiagonalPoint c z) :
    DiagonalPoint c (z 0).toNat (z 2).toNat (z 1).toNat := by
  unfold DiagonalPoint
  rw [h.cast_toNat 0, h.cast_toNat 1, h.cast_toNat 2]
  exact sub_eq_zero.mpr h.2.2.2

lemma IntegerDiagonalPoint.first_positive {c : ℤ} {z : Fin 3 → ℤ}
    (h : IntegerDiagonalPoint c z) : 1 ≤ (z 0).toNat := by
  have hi := h.1
  omega

lemma diagonalPoint_swap_positive {c : ℤ} {u x y : ℕ}
    (h : DiagonalPoint c u x y) : DiagonalPoint c y x u := by
  unfold DiagonalPoint at h ⊢
  omega

def swapPositiveCoordinates (z : Fin 3 → ℤ) : Fin 3 → ℤ := ![z 1, z 0, z 2]

lemma swapPositiveCoordinates_involutive : Function.Involutive swapPositiveCoordinates := by
  intro z
  funext i
  fin_cases i <;> rfl

lemma swapPositiveCoordinates_injective : Function.Injective swapPositiveCoordinates :=
  swapPositiveCoordinates_involutive.injective

lemma IntegerDiagonalPoint.swap {c : ℤ} {z : Fin 3 → ℤ}
    (h : IntegerDiagonalPoint c z) (hpositive : 1 ≤ z 1) :
    IntegerDiagonalPoint c (swapPositiveCoordinates z) := by
  change 1 ≤ z 1 ∧ 0 ≤ z 0 ∧ 0 ≤ z 2 ∧ z 1 ^ 6 + z 0 ^ 6 - z 2 ^ 6 = c
  exact ⟨hpositive, h.nonnegative 0, h.2.2.1, by rw [add_comm]; exact h.2.2.2⟩

lemma height_swapPositiveCoordinates (z : Fin 3 → ℤ) (B : ℝ)
    (hz : ∀ i, |(z i : ℝ)| ≤ B) : ∀ i, |(swapPositiveCoordinates z i : ℝ)| ≤ B := by
  intro i
  fin_cases i
  · exact hz 1
  · exact hz 0
  · exact hz 2

lemma IntegerDiagonalPoint.zero_middle_bound {c : ℤ} {z : Fin 3 → ℤ}
    (hc : c ≠ 0) (h : IntegerDiagonalPoint c z) (hz : z 1 = 0) :
    ∀ i, |(z i : ℝ)| ≤ (c.natAbs : ℝ) := by
  have heq : (((z 0).toNat : ℤ) ^ 6 - ((z 2).toNat : ℤ) ^ 6) = c := by
    rw [h.cast_toNat 0, h.cast_toNat 2]
    have hp := h.2.2.2
    simpa only [hz, zero_pow (by decide : 6 ≠ 0), add_zero] using hp
  obtain ⟨hu, hx⟩ := difference_witness_bound hc heq
  have h0 : ((z 0).toNat : ℝ) = (z 0 : ℝ) := by exact_mod_cast h.cast_toNat 0
  have h2 : ((z 2).toNat : ℝ) = (z 2 : ℝ) := by exact_mod_cast h.cast_toNat 2
  intro i
  fin_cases i
  · change |(z 0 : ℝ)| ≤ _
    rw [← h0, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hu
  · change |(z 1 : ℝ)| ≤ _
    rw [hz, Int.cast_zero, abs_zero]
    exact Nat.cast_nonneg _
  · change |(z 2 : ℝ)| ≤ _
    rw [← h2, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hx

theorem card_zero_middle_points_le (c : ℤ) (hc : c ≠ 0) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ z ∈ S, IntegerDiagonalPoint c z ∧ z 1 = 0) :
    S.card ≤ (Counting.sexticBox c (c.natAbs : ℝ)).card := by
  apply Finset.card_le_card
  intro z hz
  exact (Counting.mem_sexticBox c (c.natAbs : ℝ) z).mpr
    ⟨(hS z hz).1.2.2.2, (hS z hz).1.zero_middle_bound hc (hS z hz).2⟩

#print axioms card_zero_middle_points_le
-- 'Erdos477.card_zero_middle_points_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477
