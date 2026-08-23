/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Order.Interval.Finset.Nat

namespace Erdos794

def V_set : Finset ℕ := Finset.Icc 1 9
def has_subgraph (E : Finset (Finset ℕ)) (v_count e_count : ℕ) : Prop :=
  ∃ s, s ⊆ V_set ∧ s.card = v_count ∧ (E.filter (fun e => e ⊆ s)).card ≥ e_count
def erdos_794 : Prop :=
  ∀ (n : ℕ) (V : Finset ℕ) (E : Finset (Finset ℕ)),
    V.card = 3 * n →
    (∀ e ∈ E, e.card = 3) →
    E.card ≥ n ^ 3 + 1 →
    has_subgraph E 4 3 ∨ has_subgraph E 5 7
end Erdos794

open scoped Classical in
theorem Erdos794.not_erdos_794 :
    Not Erdos794.erdos_794
  := by
  sorry
