import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos914

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local instance] Classical.propDecidable

namespace TerminalVertex

variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α]

end TerminalVertex

open Finset

namespace HajnalSzemeredi

open Finset Function SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def HasDisjointCliques (G : SimpleGraph V) (r m : ℕ) : Prop :=
  ∃ f : Fin m → Finset V,
    (∀ i, (f i).card = r) ∧
    (∀ i, ∀ v ∈ f i, ∀ w ∈ f i, v ≠ w → G.Adj v w) ∧
    (∀ i j, i ≠ j → Disjoint (f i) (f j))
end HajnalSzemeredi

end Erdos914

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos914.HajnalSzemeredi.hajnal_szemeredi_clique_cover :
    ∀ {V : Type u_1} [inst : Fintype.{u_1} V] (G : SimpleGraph.{u_1} V)
      [inst_1 : @DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)] (r m : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r →
        @Eq.{1} Nat (@Fintype.card.{u_1} V inst)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r m) →
          @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@SimpleGraph.minDegree.{u_1} V G inst inst_1) →
            @Erdos914.HajnalSzemeredi.HasDisjointCliques.{u_1} V G r m
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
