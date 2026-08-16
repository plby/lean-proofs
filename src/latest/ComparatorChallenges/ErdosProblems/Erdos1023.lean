import Mathlib

namespace Erdos1023

open scoped Nat
open Asymptotics Filter

def UnionFreeMany {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ C ∈ F, ∀ G ⊆ F.erase C, G.Nonempty → G.sup id ≠ C
noncomputable def MaxUnionFreeMany (n : ℕ) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFreeMany).sup Finset.card
end Erdos1023

attribute [local instance] Classical.propDecidable

open scoped Nat
open Asymptotics Filter

namespace Erdos1023

theorem erdos_1023 :
    ∃ c : ℝ, 0 < c ∧
      (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop]
        (fun n => c * ((2 : ℝ) ^ n) / Real.sqrt (n : ℝ)) := by
  sorry

end Erdos1023
