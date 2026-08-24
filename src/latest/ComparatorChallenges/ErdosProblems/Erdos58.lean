/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped SimpleGraph

namespace Erdos58

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  {n | Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

theorem erdos_58 {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hk : (oddCycleLengths G).encard ≤ (k : ℕ∞)) :
    G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (G.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G) := by
  sorry

end Erdos58
