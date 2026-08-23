/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Filter SimpleGraph

noncomputable section

namespace SimpleGraph

open scoped Classical in
def IsBalanced {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℝ)
    [DecidableRel G.Adj] : Prop :=
  G.maxDegree ≤ D * G.minDegree

end SimpleGraph

namespace Erdos803

open scoped Classical in
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

open scoped Classical in
theorem erdos_803 : ¬ Erdos803Statement := by
  sorry

end Erdos803

end
