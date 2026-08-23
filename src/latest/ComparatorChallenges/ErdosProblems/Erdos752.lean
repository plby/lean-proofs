import Mathlib

open Finset
open SimpleGraph

noncomputable section


universe u

namespace Erdos752

open scoped Classical in
def GirthGreaterThan {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → n < p.length

end Erdos752

namespace Erdos752

open scoped Classical in
def HasCycleLength {V : Type u} (G : SimpleGraph V) (l : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = l

end Erdos752

namespace Erdos752

open scoped Classical in
def MinimumDegreeResolution : Prop :=
  ∀ (s : ℕ), 1 ≤ s →
    ∃ C : ℕ, 0 < C ∧ ∃ k₀ : ℕ,
      ∀ (k : ℕ), k₀ ≤ k →
        ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          k ≤ G.minDegree →
          GirthGreaterThan G (2 * s) →
          ∃ L : Finset ℕ,
            k ^ s ≤ C * L.card ∧ ∀ l ∈ L, HasCycleLength G l

end Erdos752

namespace Erdos752

open scoped Classical in
theorem erdos_752 : MinimumDegreeResolution.{u} := by
  sorry

end Erdos752

end
