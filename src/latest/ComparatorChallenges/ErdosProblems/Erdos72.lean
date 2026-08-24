/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Topology

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos72

noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact (2 * G.edgeFinset.card : ℝ) / Fintype.card V

def HasCycleLength {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = m

theorem erdos_72 :
    ∃ A : Set ℕ, A.HasDensity 0 ∧
      ∃ c : ℝ, 0 < c ∧
        ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ G : SimpleGraph (Fin n),
          c ≤ averageDegree G → ∃ m ∈ A, HasCycleLength G m := by
  sorry

end Erdos72
