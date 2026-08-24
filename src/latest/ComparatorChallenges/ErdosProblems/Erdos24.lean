/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos24

def _root_.SimpleGraph.IsLabeledC5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 5, G.Adj (f i) (f (i + ⟨1, Nat.one_lt_succ_succ 3⟩))

open scoped Classical in
noncomputable def _root_.SimpleGraph.numC5 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → V)).filter (fun f => G.IsLabeledC5 f)).card / 10

theorem erdos_24 (n : ℕ) (G : SimpleGraph (Fin (5 * n)))
    (hG : G.CliqueFree 3) :
    G.numC5 ≤ n ^ 5 := by
  sorry

end Erdos24
