/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion822UnusedRecord
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Genuine finite root prefixes for selected grounding requests

The stationary unused-record argument identifies the limiting-ladder parent
which contains the initial original vertex of every decoded selected request.
This module cuts that parent at the decoded initial vertex.  The result is a
finite path from a genuine source distinct from the unused root, even when the
parent itself is a ray.

The theorem deliberately records only parent-edge membership.  Proving that
those edges survive the simultaneous switch is the separate contact-order
part of Assertion 8.22.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}

namespace UnusedGroundedRecord

/-- A selected request has a finite prefix in its grounded limiting-ladder
parent, starting at an allowed original source and ending at the decoded
request-trace initial vertex. -/
theorem exists_selectedRequest_rootPrefix
    (R : L.UnusedGroundedRecord hL S)
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    ∃ (parent : Gamma.DPath)
        (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        q.start ∈ Gamma.source \ {R.record.initial} ∧
        q.finish =
          (GroundingErasedDecode.selectedRequestTrace
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S) r).initial ∧
        q.support ⊆ parent.support ∧ q.edgeSet ⊆ parent.edgeSet := by
  obtain ⟨a, parent, _haGround, _hchosen, hparent, htrace,
    hsource, _hindex, hroot⟩ := R.exists_selectedRequest_parent_with_root_ne r
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix parent htrace
  refine ⟨parent, q, hparent, ?_, hqFinish, hqSupport, hqEdges⟩
  rw [hqStart]
  exact ⟨hsource, fun heq ↦ hroot (Set.mem_singleton_iff.mp heq).symm⟩

end UnusedGroundedRecord
end DWeb.KappaLadder
end Erdos599
