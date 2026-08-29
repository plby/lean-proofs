/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceBoundary
import ErdosProblems.Erdos599.GroundingOldExitOutgoingObstruction

/-!
# Old cut vertices are sinks of the concrete grounding switch

The old-vertex part `CV` of the popular cut splits into grounded finite
sources and genuine old requests.  The former are sinks by the terminal
geometry of their grounded parent, and the latter are sinks by the explicit
two-sided old-request outgoing cut.  This packages the split into the form
used by the blocking-point argument of Assertion 8.22.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating PopularGroundingBridge GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Every original vertex represented by an old vertex of the popular cut
is a literal sink of the final concrete switched relation. -/
theorem cv_noOutgoing_assertion822SwitchedEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    {b : V}
    (hb : b ∈ GroundingCut.CV
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    ¬ HasOutgoing
      (erasedSelectedSwitchedEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)) b := by
  by_cases hbFinite :
      b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource
  · exact L.finiteSource_noOutgoing_switched_of_mem_cut
      hL S hbFinite (GroundingCut.mem_CV.mp hb)
  · let r : oldRequests (L.popularAuxiliaryInput hL.legal) S.cut :=
      ⟨b, GroundingCut.mem_CV.mp hb, hbFinite⟩
    exact GroundingOldExitOutgoingObstruction.oldRequest_noOutgoing
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) r

end DWeb.KappaLadder
end Erdos599

