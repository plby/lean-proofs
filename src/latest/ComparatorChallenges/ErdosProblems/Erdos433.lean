/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos433

def S (E : Set ℕ) : AddSubsemigroup ℕ := AddSubsemigroup.closure E
noncomputable def G (E : Set ℕ) : ℕ := sSup {n | n ∉ S E}

noncomputable def g (b a : ℕ) : ℕ :=
  sSup {G E | (E : Finset ℕ)
    (_hE_sub : (E : Set ℕ) ⊆ Set.Icc 1 a)
    (_hE_card : E.card = b)
    (_hE_gcd : Finset.gcd E id = 1)}

theorem erdos_433 (a b : ℕ) (hb_ge_2 : b ≥ 2) (hb_lt_a : b < a) :
  ⌊(a - 2 : ℝ) / (b - 1 : ℝ)⌋ * (a - b + 1) - 1 ≤ g b a ∧
  g b a ≤ (⌈(a - 1 : ℝ) / (b - 1 : ℝ)⌉ - 1) * a - 1 := by
  sorry

end Erdos433
