import Mathlib.Analysis.Asymptotics.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

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

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
def UnionFree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → B ≠ C → A ≠ C → A ∪ B ≠ C
noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable def MaxUnionFree (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFree).sup Finset.card
end Erdos447

attribute [local instance] Classical.propDecidable

theorem Erdos447.erdos_447 :
    @Asymptotics.IsEquivalent.{0, 0} Nat Real
      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (Erdos447.MaxUnionFree n)) fun (n : Nat) ↦
      @Nat.cast.{0} Real Real.instNatCast
        (n.choose
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry
