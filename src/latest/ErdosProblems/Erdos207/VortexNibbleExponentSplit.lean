/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexWellSpread

/-!
# Root-exponent alternatives in the KSSS nibble moment bounds

The two-family weight bound gains the needed power unless both exposed
roots are exceptional (singleton or full).  The source treats those
exceptional cases by reversing the exposure order or using equal remainders.
-/

namespace Erdos207

theorem vortexRootExponent_le_order {r a : ℕ} (ha : 1 ≤ a) (har : a ≤ r - 2) :
    vortexRootExponent r a ≤ r := by
  unfold vortexRootExponent
  split_ifs with h
  · rcases h with h | h <;> omega
  · omega

theorem vortexRootExponent_add_ge_or_exceptional (r s a b : ℕ) :
    a + b + 5 ≤ vortexRootExponent r a + vortexRootExponent s b ∨
      ((a = 1 ∨ a = r - 2) ∧ (b = 1 ∨ b = s - 2)) := by
  by_cases ha : a = 1 ∨ a = r - 2
  · by_cases hb : b = 1 ∨ b = s - 2
    · exact Or.inr ⟨ha, hb⟩
    · left
      simp only [vortexRootExponent, if_pos ha, if_neg hb]
      omega
  · left
    have hb := add_two_le_vortexRootExponent s b
    simp only [vortexRootExponent, if_neg ha]
    by_cases hbs : b = 1 ∨ b = s - 2 <;> simp only [hbs, ite_true, ite_false] <;> omega

theorem vortexRootExponent_pair_nibble_split
    {r s a b h q : ℕ} (ha : a < r - 2) (hb : 2 ≤ b)
    (hcount : a + b = h + q + 3) :
    h + q + 8 ≤ vortexRootExponent r a + vortexRootExponent s b ∨
      (a = 1 ∧ b = s - 2) := by
  rcases vortexRootExponent_add_ge_or_exceptional r s a b with h | h
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega⟩

theorem vortexRootExponent_reverse_nibble_split
    {r s a b : ℕ} (ha : 2 ≤ a) (hb : b < s - 2)
    (hcount : a + b + 1 = s) :
    s + 4 ≤ vortexRootExponent r a + vortexRootExponent s b ∨
      (a = r - 2 ∧ b = 1) := by
  rcases vortexRootExponent_add_ge_or_exceptional r s a b with h | h
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega⟩

end Erdos207
