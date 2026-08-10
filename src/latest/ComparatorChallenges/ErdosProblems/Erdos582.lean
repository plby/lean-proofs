import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Erdos582

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (v0 : V) (H' : SimpleGraph W)

set_option maxHeartbeats 50000000
set_option maxRecDepth 4000

def EdgeRamseyTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (c : G.edgeSet → Bool),
    ∃ (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w),
      c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧
        c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩
variable {V : Type*} [Fintype V] [DecidableEq V]

end Erdos582

attribute [local instance] Classical.propDecidable

universe u_3

theorem Erdos582.erdos_582 :
    @Exists.{2} Type fun (V : Type) ↦
      @Exists.{1} (Fintype.{0} V) fun (x : Fintype.{0} V) ↦
        @Exists.{1} (DecidableEq.{1} V) fun (x : DecidableEq.{1} V) ↦
          @Exists.{1} (SimpleGraph.{0} V) fun (G : SimpleGraph.{0} V) ↦
            And
              (@Eq.{1} Nat (@SimpleGraph.cliqueNum.{0} V G)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Erdos582.EdgeRamseyTriangle.{0} V G)
  := by
  sorry
