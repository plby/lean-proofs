/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos407

structure Rep where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def Rep.value (r : Rep) : ℕ :=
  2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d

def solutions (n : ℕ) : Set Rep := {r | r.value = n}

noncomputable def w (n : ℕ) : ℕ := (solutions n).ncard

theorem erdos_407 : ∃ C : ℕ, ∀ n : ℕ, w n ≤ C := by
  sorry

end Erdos407
