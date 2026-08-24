/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

universe u

namespace Erdos752

def GirthGreaterThan {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → n < p.length

def HasCycleLength {V : Type u} (G : SimpleGraph V) (l : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = l

theorem erdos_752 :
    ∀ (s : ℕ), 1 ≤ s →
      ∃ C : ℕ, 0 < C ∧ ∃ k₀ : ℕ,
        ∀ (k : ℕ), k₀ ≤ k →
          ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
            [DecidableRel G.Adj],
            k ≤ G.minDegree →
            Erdos752.GirthGreaterThan G (2 * s) →
            ∃ L : Finset ℕ,
              k ^ s ≤ C * L.card ∧ ∀ l ∈ L, Erdos752.HasCycleLength G l := by
  sorry

end Erdos752
