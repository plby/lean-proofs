/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Asymptotics Filter

namespace Erdos716

variable {n : ℕ}

/-- `H` contains `3` distinct edges spanning at most `6` vertices. For `n ≥ 6` this is exactly the
statement that `H` contains a member of the family `𝓕` of all `3`-uniform hypergraphs with `6`
vertices and `3` edges. -/
def ThreeEdgesIn6 (H : Finset (Finset (Fin n))) : Prop :=
  ∃ e₁ ∈ H, ∃ e₂ ∈ H, ∃ e₃ ∈ H,
    e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧ (e₁ ∪ e₂ ∪ e₃).card ≤ 6
/-- The extremal number: the maximum number of edges of a `3`-uniform hypergraph on `Fin n` not
containing a member of `𝓕`. -/
noncomputable def ex3 (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
    (fun H => (∀ e ∈ H, e.card = 3) ∧ ¬ ThreeEdgesIn6 H)).sup Finset.card

theorem erdos_716 :
    (fun n => (ex3 n : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) := by
  sorry

end Erdos716
