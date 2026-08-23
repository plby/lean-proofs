/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos844

set_option linter.style.setOption false
set_option linter.flexible false

open Finset Nat

noncomputable def erdosSarkozySet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun k => 2 ∣ k ∨ ¬ Squarefree k)
end Erdos844


open Finset Nat

namespace Erdos844

open scoped Classical in
theorem erdos_sarkozy (N : ℕ) (A : Finset ℕ)
    (hA_sub : A ⊆ Finset.Icc 1 N)
    (hA_prod : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) :
    A.card ≤ (erdosSarkozySet N).card := by
  sorry

end Erdos844
