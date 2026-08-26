import Mathlib

open SimpleGraph
open scoped SimpleGraph

namespace Erdos556

structure ThreeColouring (V : Type*) where
  colour : V → V → Fin 3
  symm : ∀ u v, colour u v = colour v u

def ThreeColouring.graph {V : Type*} (c : ThreeColouring V) (i : Fin 3) :
    SimpleGraph V where
  Adj u v := u ≠ v ∧ c.colour u v = i
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, (c.symm v u).trans h.2⟩⟩
  loopless := ⟨by simp⟩

def IsRamseyOrder (n m : ℕ) : Prop :=
  ∀ c : ThreeColouring (Fin m), ∃ i : Fin 3, cycleGraph n ⊑ c.graph i

noncomputable def ramseyNumber (n : ℕ) : ℕ :=
  sInf {m : ℕ | IsRamseyOrder n m}

theorem erdos_556 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Odd n →
      ramseyNumber n = 4 * n - 3 := by
  sorry

end Erdos556
