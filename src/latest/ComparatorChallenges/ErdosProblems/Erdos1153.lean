/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1153

structure NodeConfiguration (n : ℕ) where
  nodes : Fin n → ℝ
  injective_nodes : Function.Injective nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

noncomputable def lagrangeBasis {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) (x : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ X.nodes k).eval x

noncomputable def lebesgueFunction {n : ℕ} (X : NodeConfiguration n)
    (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis X k x|

theorem erdos_1153 :
    ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : Erdos1153.NodeConfiguration n,
          ∃ x ∈ Set.Icc a b,
            (2 / Real.pi - ε) * Real.log (n : ℝ) ≤ Erdos1153.lebesgueFunction X x := by
  sorry

end Erdos1153
