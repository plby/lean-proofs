import Mathlib

open Finset Filter SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace SimpleGraph

def IsBalanced {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℝ)
    [DecidableRel G.Adj] : Prop :=
  G.maxDegree ≤ D * G.minDegree

end SimpleGraph

namespace Erdos803

def Erdos803Statement : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ m : ℕ, 1 ≤ m →
      ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          (n : ℝ) * Real.log n ≤ (G.edgeSet.ncard : ℝ) →
            ∃ H : G.Subgraph,
              H.verts.ncard = m ∧
                H.coe.IsBalanced D ∧
                  ε * (m : ℝ) * Real.log m ≤ (H.edgeSet.ncard : ℝ)

end Erdos803

namespace Erdos803

theorem erdos_803 : False ↔ Erdos803Statement := by
  sorry

end Erdos803

end
