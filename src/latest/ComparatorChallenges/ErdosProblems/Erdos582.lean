/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos582

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (v0 : V) (H' : SimpleGraph W)

def EdgeRamseyTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (c : G.edgeSet → Bool),
    ∃ (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w),
      c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧
        c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem erdos_582 :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      G.cliqueNum = 3 ∧ EdgeRamseyTriangle G := by
  sorry

end Erdos582
