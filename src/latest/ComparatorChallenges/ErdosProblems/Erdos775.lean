/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos775

set_option linter.style.setOption false
set_option linter.flexible false

open Finset


set_option maxHeartbeats 12800000
open Finset

noncomputable section

open scoped Classical in
structure KUniformHypergraph (α : Type*) (k : ℕ) where
  edges : Set (Finset α)
  uniform : ∀ e ∈ edges, e.card = k
namespace KUniformHypergraph

variable {α : Type*} [DecidableEq α] {k : ℕ}

open scoped Classical in
def IsComplete (H : KUniformHypergraph α k) (S : Finset α) : Prop :=
  ∀ e : Finset α, e ⊆ S → e.card = k → e ∈ H.edges

open scoped Classical in
def IsClique (H : KUniformHypergraph α k) (S : Finset α) : Prop :=
  H.IsComplete S ∧ ∀ T : Finset α, S ⊂ T → ¬H.IsComplete T
end KUniformHypergraph

end

end Erdos775



namespace Erdos775

end Erdos775

open Finset

namespace Erdos775

open scoped Classical in
theorem erdos_problem_775 (C : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ H : KUniformHypergraph (Fin n) 3,
        ∀ sizes : Finset ℕ,
          (∀ s ∈ sizes, ∃ S : Finset (Fin n), H.IsClique S ∧ S.card = s) →
          sizes.card ≤ n - C := by
  sorry

end Erdos775
