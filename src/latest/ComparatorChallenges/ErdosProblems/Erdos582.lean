import Mathlib

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


open SimpleGraph

namespace Erdos582

theorem erdos_582 :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      G.cliqueNum = 3 ∧ EdgeRamseyTriangle G := by
  sorry

end Erdos582
