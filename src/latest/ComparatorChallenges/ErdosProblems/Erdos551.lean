import Mathlib

open scoped BigOperators Classical SimpleGraph NNReal
open Filter Asymptotics
open Topology

namespace Erdos551

open Fintype SimpleGraph

def CycleCliqueRamseyProperty (k n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), cycleGraph k ⊑ G ∨ ¬ G.IndepSetFree n

theorem cycleCliqueRamseyProperty_exists (k n : ℕ) :
    ∃ N, CycleCliqueRamseyProperty k n N := by
  sorry

noncomputable def cycleCliqueRamseyNumber (k n : ℕ) : ℕ :=
  Nat.find (cycleCliqueRamseyProperty_exists k n)

theorem erdos_551_eventually :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, n ≤ k →
      cycleCliqueRamseyNumber k n = (k - 1) * (n - 1) + 1 := by
  sorry

end Erdos551
