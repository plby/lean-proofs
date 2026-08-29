/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Outgoing residual edges at old request exits

The old-exit correction cuts every residual continuation leaving an actual
old request.  The lemmas below record its precise consequence: any switched
edge leaving such an exit must be an inserted forward edge.  Consequently
old-exit sinkhood is reduced to the one remaining decoder statement that no
selected forward edge leaves the old cut point.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingOldExitOutgoingObstruction

open GroundingErasedDecode PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- A residual edge survives the current switch whenever it is not a
selected backward edge and shares neither its tail nor its head with an
inserted forward edge. -/
theorem residualEdge_mem_erasedSelectedSwitchedEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {e : V × V}
    (hresidual : e ∈ residualLadderEdges U S)
    (hnotBackward : e ∉ erasedSelectedDirectionEdges U S K .backward)
    (hnotBoundary : e ∉ boundaryOutgoingCutEdges U S)
    (hnoForwardTail : ∀ f ∈ erasedSelectedDirectionEdges U S K .forward,
      e.1 ≠ f.1)
    (hnoForwardHead : ∀ f ∈ erasedSelectedDirectionEdges U S K .forward,
      e.2 ≠ f.2) :
    e ∈ erasedSelectedSwitchedEdges U S K := by
  apply Or.inl
  refine ⟨hresidual, ?_⟩
  rintro (hbackward | hconflict)
  · exact hnotBackward hbackward
  · rcases hconflict with hconflict | hold
    · obtain ⟨_hresidual, f, hf, htail | hhead⟩ := hconflict
      · exact hnoForwardTail f
          (erasedSelectedRetainedForwardEdges_subset_forward U S K hf) htail
      · exact hnoForwardHead f
          (erasedSelectedRetainedForwardEdges_subset_forward U S K hf) hhead
    · exact hnotBoundary hold

/-- After the old-exit correction, every switched edge leaving the endpoint
of an old request is an inserted forward edge. -/
theorem oldRequest_switchedEdge_mem_forward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : oldRequests L S.cut) {y : V}
    (h : (r.1, y) ∈ erasedSelectedSwitchedEdges U S K) :
    (r.1, y) ∈ erasedSelectedDirectionEdges U S K .forward := by
  rcases h with hresidual | hforward
  · exfalso
    exact hresidual.2 <| Or.inr <| Or.inr <|
      oldRequestOutgoingCutEdges_subset_boundaryOutgoingCutEdges U S <|
        GroundingErasedDecode.oldRequest_residualOutgoing_mem_cut
          U S r hresidual.1
  · exact hforward.1

/-- Every old request is a sink of the corrected switched relation.

The residual half of the relation removes `oldRequestOutgoingCutEdges`, and
the inserted-forward half independently removes
`oldRequestOutgoingForwardCutEdges`.  Thus this conclusion does not depend on
whether the request was selected as active: the endpoint cut is applied after
the simultaneous active-route union has been formed. -/
theorem oldRequest_noOutgoing
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : oldRequests L S.cut) :
    ¬ Alternating.HasOutgoing (erasedSelectedSwitchedEdges U S K) r.1 :=
  GroundingErasedDecode.oldRequest_noOutgoing_switched U S K r

/-- Hence absence of inserted forward departures makes every old request
exit a sink of the corrected switched relation. -/
theorem oldRequest_noOutgoing_of_noForward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : oldRequests L S.cut)
    (hforward : ¬ Alternating.HasOutgoing
      (erasedSelectedDirectionEdges U S K .forward) r.1) :
    ¬ Alternating.HasOutgoing (erasedSelectedSwitchedEdges U S K) r.1 := by
  rintro ⟨y, hy⟩
  exact hforward ⟨y, oldRequest_switchedEdge_mem_forward U S K r hy⟩

/-- Pointwise `CV \ finiteSource` form of the same reduction. -/
theorem cv_noOutgoing_of_not_finiteSource_of_noForward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {b : V} (hbCV : b ∈ GroundingCut.CV L S.cut)
    (hbFinite : b ∉ L.finiteSource)
    (hforward : ¬ Alternating.HasOutgoing
      (erasedSelectedDirectionEdges U S K .forward) b) :
    ¬ Alternating.HasOutgoing (erasedSelectedSwitchedEdges U S K) b := by
  let r : oldRequests L S.cut :=
    ⟨b, GroundingCut.mem_CV.mp hbCV, hbFinite⟩
  exact oldRequest_noOutgoing_of_noForward U S K r hforward

end GroundingOldExitOutgoingObstruction
end Erdos599
