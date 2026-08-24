/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Asymptotics

namespace Erdos1023

def UnionFreeMany {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ C ∈ F, ∀ G ⊆ F.erase C, G.Nonempty → G.sup id ≠ C
noncomputable def MaxUnionFreeMany (n : ℕ) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFreeMany).sup Finset.card

theorem erdos_1023 :
    ∃ c : ℝ, 0 < c ∧
      (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop]
        (fun n => c * ((2 : ℝ) ^ n) / Real.sqrt (n : ℝ)) := by
  sorry

end Erdos1023
