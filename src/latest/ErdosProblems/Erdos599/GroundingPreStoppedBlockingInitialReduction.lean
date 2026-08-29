/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedFiniteRootBackwardSwitch
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# Eliminating the blocking-initial root failure

A maximal surviving fragment starts either at its limiting-ladder parent's
initial vertex or at the head of a represented cut edge.  Hence its initial
cannot be a pre-stopped root obstruction once parent initials and cut controls
are rooted in the reserved relation.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- The `blockingInitial` constructor is impossible after the two preceding
root classes—limiting-ladder parent initials and represented-cut controls—are
rooted. -/
theorem not_blockingInitial_of_control_and_parent_rooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ GroundingCut.blockableG0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a P.path.initial)
    (hcontrol : ∀ c : GroundingErasedDecode.ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a c.1)
    (hparent : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a P.parent.initial) : False := by
  rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
      (L.popularAuxiliaryInput hL.legal) S.cut P hP.1.1 with
    hfirst | ⟨e, heCut, _heParent, heHead⟩
  · apply hnot
    simpa only [hfirst] using hparent
  · apply hnot
    obtain ⟨a, ha, hareach⟩ :=
      exists_root_reaching_head_of_mem_CE_of_controls_rooted
        hcontrol heCut
    exact ⟨a, ha, by simpa only [heHead] using hareach⟩

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.not_blockingInitial_of_control_and_parent_rooted
