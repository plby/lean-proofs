/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos88

universe u

/-- A graph has no clique or independent set of size at least `ε * log n`. -/
def HomogeneousFree {n : ℕ} (ε : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < ε * Real.log n

/-- The number of edges whose endpoints both belong to `S`. -/
noncomputable def inducedEdges {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).edgeSet

/-- Every sufficiently small nonnegative integer occurs as an induced edge count. -/
theorem erdos_88 :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree epsilon G →
            ∀ m : ℕ, (m : ℝ) ≤ delta * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m := by
  sorry

end Erdos88
