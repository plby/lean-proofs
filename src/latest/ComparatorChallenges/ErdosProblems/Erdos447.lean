import Mathlib

namespace Erdos447

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.cdot false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.whitespace false

open scoped Nat
open Asymptotics Filter


set_option maxHeartbeats 50000000
open scoped Classical in
def UnionFree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → B ≠ C → A ≠ C → A ∪ B ≠ C
noncomputable section AristotleLemmas

end AristotleLemmas

open scoped Classical in
noncomputable def MaxUnionFree (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFree).sup Finset.card
end Erdos447


open scoped Nat
open Asymptotics Filter

namespace Erdos447

open scoped Classical in
theorem erdos_447 :
    (fun n => (MaxUnionFree n : ℝ)) ~[atTop] (fun n => (n.choose (n / 2) : ℝ)) := by
  sorry

end Erdos447
