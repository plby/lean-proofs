/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos24

noncomputable section

open Finset Function SimpleGraph Fintype Nat Matrix


open scoped Classical in
def σ₂FlagIdx (adjDA adjDCenter adjDC : Bool) : Option (Fin 5) :=
  match adjDA, adjDCenter, adjDC with
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | false, false, true => some 3
  | true, false, true => some 4
  | _, _, _ => none

open scoped Classical in
def _root_.SimpleGraph.IsLabeledC5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 5, G.Adj (f i) (f (i + 1))

open scoped Classical in
noncomputable def _root_.SimpleGraph.numC5 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → V)).filter (fun f => G.IsLabeledC5 f)).card / 10

open scoped Classical in
theorem erdos_pentagon_conjecture (n : ℕ) (G : SimpleGraph (Fin (5 * n)))
    (hG : G.CliqueFree 3) :
    G.numC5 ≤ n ^ 5 := by
  sorry

end

end Erdos24
