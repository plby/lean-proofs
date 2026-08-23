/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset
open scoped BigOperators

noncomputable section


namespace Erdos816

open scoped Classical in
def JoinedByPathThree {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ x y, u ≠ x ∧ u ≠ y ∧ u ≠ v ∧ x ≠ y ∧ x ≠ v ∧ y ≠ v ∧
    G.Adj u x ∧ G.Adj x y ∧ G.Adj y v

end Erdos816

namespace Erdos816

open scoped Classical in
theorem erdos_816
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hedges : G.edgeFinset.card = n ^ 2 + n + 1) :
    ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧ JoinedByPathThree G u v := by
  sorry

end Erdos816

end
