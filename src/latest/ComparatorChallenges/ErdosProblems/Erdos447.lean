/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Asymptotics Filter

namespace Erdos447

def UnionFree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → B ≠ C → A ≠ C → A ∪ B ≠ C

open scoped Classical in
noncomputable def MaxUnionFree (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFree).sup Finset.card

theorem erdos_447 :
    (fun n => (MaxUnionFree n : ℝ)) ~[atTop] (fun n => (n.choose (n / 2) : ℝ)) := by
  sorry

end Erdos447
