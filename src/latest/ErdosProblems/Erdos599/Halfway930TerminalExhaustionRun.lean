/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930DiamondTailAdvance
import ErdosProblems.Erdos599.HalfwayCofinalBlueprintRelation

/-!
# Closing an exhausted two-diamond stage

The varying-stage scheduler eventually reaches a stage at which the only
old real terminal not already in the ambient target is the scheduled one.
For that terminal state, the honest two-diamond advance is already a complete
global run.  This file constructs the actual one-stage
`CofinalRealExtensionRun`; fairness and final edge reality are derived.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClosedOldSlice930DiamondTailTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V}

/-- If every old real terminal other than the scheduled vertex is already a
target, the complete two-diamond result has no non-target real terminal. -/
theorem result_realTerminals_subset_target
    (Q : ClosedOldSlice930DiamondTailTransaction C W u)
    (hold : W.realPart.terminals ⊆ {u} ∪ Gamma.target) :
    Q.result.realPart.terminals ⊆ Gamma.target := by
  intro x hx
  rcases Q.result_realTerminals_subset_old_union_target hx with hxOld | hxTarget
  · rcases hold hxOld with hxu | hxTarget
    · have hxeq : x = u := Set.mem_singleton_iff.1 hxu
      subst x
      by_cases huTarget : u ∈ Gamma.target
      · exact huTarget
      · exact False.elim
          (not_mem_realTerminals_of_realLinksTo huTarget Q.result_realLinksTo hx)
    · exact hxTarget
  · exact hxTarget

/-- The terminally exhausted two-diamond transaction, repeated over the
one-point directed order, is an actual fair real-extension run. -/
def terminalExhaustionRun
    (Q : ClosedOldSlice930DiamondTailTransaction C W u)
    (hold : W.realPart.terminals ⊆ {u} ∪ Gamma.target) :
    CofinalRealExtensionRun Gamma C.selectedReference kappa Gamma.target Unit where
  stage := fun _ ↦ Q.result
  scheduled := fun _ ↦ u
  realExtends := by
    intro i j hij
    exact realExtends_refl Q.result Gamma.target
  countably_bounded := by
    intro f
    exact ⟨(), fun n ↦ by simp⟩
  fair := by
    intro x hxCarrier hxSink hxTarget
    exfalso
    apply hxTarget
    apply Q.result_realTerminals_subset_target hold
    refine ⟨?_, ?_⟩
    · change x ∈ Q.result.vertexSet
      simpa only [Set.iUnion_const] using hxCarrier
    · rintro ⟨y, hxy⟩
      apply hxSink
      refine ⟨y, ?_⟩
      simpa only [Set.iUnion_const] using hxy
  resolved := by
    intro i
    exact Q.result_realLinksTo

/-- The compiled honest relation has exactly the real edges of the exhausted
two-diamond result. -/
@[simp] theorem terminalExhaustionRun_finalEdge
    (Q : ClosedOldSlice930DiamondTailTransaction C W u)
    (hold : W.realPart.terminals ⊆ {u} ∪ Gamma.target) :
    (Q.terminalExhaustionRun hold).toBlueprintRelationRun.finalEdge =
      Q.result.realPart.edges := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
    exact hi
  · intro e he
    exact Set.mem_iUnion.2 ⟨(), he⟩

/-- Consequently every edge of the exhausted final relation is an original
ambient-web edge. -/
theorem terminalExhaustionRun_finalEdge_real
    (Q : ClosedOldSlice930DiamondTailTransaction C W u)
    (hold : W.realPart.terminals ⊆ {u} ∪ Gamma.target) :
    (Q.terminalExhaustionRun hold).toBlueprintRelationRun.finalEdge ⊆
      {e | Gamma.graph.Adj e.1 e.2} :=
  (Q.terminalExhaustionRun hold).toBlueprintRelationRun.finalEdge_real

#print axioms result_realTerminals_subset_target
#print axioms terminalExhaustionRun
#print axioms terminalExhaustionRun_finalEdge_real

end ClosedOldSlice930DiamondTailTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
