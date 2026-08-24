/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

universe u

namespace Erdos63

variable {V : Type u}

def HasCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ x : V, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = n

theorem erdos_63 {V : Type u} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) :
    Set.Infinite {n : ℕ | HasCycleLength G (2 ^ n)} := by
  sorry

end Erdos63
