import ErdosProblems.Erdos1148.GaussParameterBoxes
import ErdosProblems.Erdos1148.LiftForwardClose

/-! # Compact forward boxes of matrix lifts -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def gaussLiftBox (g : SL(2, ℝ)) (a b c wr wx wh : ℝ) : Set SL(2, ℝ) :=
  gaussParameterFrame g '' gaussParameterCell a b c wr wx wh

theorem isCompact_gaussLiftBox (g : SL(2, ℝ)) (a b c wr wx wh : ℝ) :
    IsCompact (gaussLiftBox g a b c wr wx wh) :=
  (isClosed_gaussParameterCell a b c wr wx wh).isCompact.image
    (continuous_gaussParameterFrame g)

theorem gaussLiftBox_forward_close (g : SL(2, ℝ)) (a b c : ℝ) {δ S : ℝ}
    (hδ : 0 ≤ δ) (hS : 0 ≤ S) :
    LiftForwardClose (8 * δ) S (gaussLiftBox g a b c (δ * Real.exp (-S)) δ δ) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  exact gaussFrame_forward_close g p.property.2.1 q.property.2.1
    p.property.2.2.1 q.property.2.2.1 p.property.2.2.2 q.property.2.2.2 hδ hS
    (abs_sub_le_of_mem_same_interval hq.2.2 hp.2.2)
    (abs_sub_le_of_mem_same_interval hq.2.1 hp.2.1)
    (abs_sub_le_of_mem_same_interval hq.1 hp.1)

end Erdos1148.DukeArithmetic
