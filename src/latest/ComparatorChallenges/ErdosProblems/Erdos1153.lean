/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators Topology
open Finset Set Polynomial Filter MeasureTheory

noncomputable section

namespace Erdos1153

open scoped Classical in
structure NodeConfiguration (n : ℕ) where
  nodes : Fin n → ℝ
  injective_nodes : Function.Injective nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

end Erdos1153

namespace Erdos1153

open scoped Classical in
noncomputable def lagrangeBasis {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) (x : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ X.nodes k).eval x

end Erdos1153

namespace Erdos1153

open scoped Classical in
noncomputable def lebesgueFunction {n : ℕ} (X : NodeConfiguration n)
    (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis X k x|

end Erdos1153

namespace Erdos1153

open scoped Classical in
noncomputable def heightDropKernel (eta t : ℝ) : ℝ :=
  Real.log ((t ^ 2 + (2 * eta) ^ 2) / (t ^ 2 + eta ^ 2)) / 2

end Erdos1153

namespace Erdos1153

open scoped Classical in
def Problem1153 : Prop :=
  ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : NodeConfiguration n,
        ∃ x ∈ Set.Icc a b,
          (2 / Real.pi - ε) * Real.log (n : ℝ) ≤ lebesgueFunction X x

end Erdos1153

namespace Erdos1153

open scoped Classical in
theorem erdos1153 : Problem1153 := by
  sorry

end Erdos1153

end
