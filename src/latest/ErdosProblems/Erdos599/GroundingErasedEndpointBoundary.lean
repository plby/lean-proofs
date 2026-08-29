/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedForwardConflict
import ErdosProblems.Erdos599.GroundingOldExitOutgoingObstruction

/-!
# Endpoint boundary of a loop-erased grounding route

The projected vertex chain of an erased signed route has no repetition.
Consequently its terminal cannot be the tail of a retained forward step.
This is stronger than the corresponding statement for an arbitrary
alternating trace, whose compatibility rules alone can allow a crossed
endpoint contact.
-/

noncomputable section

open Set

namespace Erdos599
namespace PopularAuxiliary.Input.ErasedSignedRoute

open Alternating

universe u

variable {V : Type u} {x y : V} {raw : List (SignedEdge V)}

/-- No retained forward step of a loop-erased signed route leaves its
terminal vertex.  The tail of such a step occurs at an index strictly
before the last vertex, contradicting injectivity of the erased vertex
chain. -/
theorem noOutgoing_directedSignedEdgeSet_forward_terminal
    (E : ErasedSignedRoute x y raw) :
    ¬ HasOutgoing (directedSignedEdgeSet .forward E.steps) y := by
  rintro ⟨z, s, hs, hforward, hsEdge⟩
  obtain ⟨n, hn, hns⟩ := List.mem_iff_getElem.mp hs
  let i : Fin E.steps.length := ⟨n, hn⟩
  have htail : E.routeVertex i = y := by
    rw [E.routeVertex_eq_entry i]
    have hget : E.steps.get i = s := by
      simpa [i] using hns
    rw [hget]
    exact (SignedEdge.entry_eq_fst_of_direction_forward s hforward).trans
      (congrArg Prod.fst hsEdge)
  have hlast : E.routeVertex E.steps.length = y := E.routeVertex_last
  have hiLen : i.1 = E.steps.length := by
    have hiChain : i.1 < E.vertexChain.length := by
      rw [E.vertexChain_length]
      omega
    have hlastChain : E.steps.length < E.vertexChain.length := by
      rw [E.vertexChain_length]
      omega
    have hget :
        E.vertexChain.get ⟨i.1, hiChain⟩ =
          E.vertexChain.get ⟨E.steps.length, hlastChain⟩ := by
      have hroute : E.routeVertex i.1 =
          E.routeVertex E.steps.length := htail.trans hlast.symm
      unfold routeVertex at hroute
      calc
        E.vertexChain.get ⟨i.1, hiChain⟩ =
            E.vertexChain.getD i.1 y :=
          (List.getD_eq_get E.vertexChain y ⟨i.1, hiChain⟩).symm
        _ = E.vertexChain.getD E.steps.length y := hroute
        _ = E.vertexChain.get ⟨E.steps.length, hlastChain⟩ :=
          List.getD_eq_get E.vertexChain y
            ⟨E.steps.length, hlastChain⟩
    exact congrArg Fin.val (E.vertexChain_nodup.injective_get hget)
  exact (Nat.ne_of_lt i.isLt) hiLen

end PopularAuxiliary.Input.ErasedSignedRoute

namespace GroundingErasedDecode

open Alternating DirectedPath PopularGroundingBridge
open PopularAuxiliary.Input PopularAuxiliary.Input.EndpointTrace
open GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

private theorem edgeSet_endpoints_mem_vertexSet
    (Q : Alternating.AltPath Gamma.graph) {e : V × V}
    (he : e ∈ Q.edgeSet) : e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  cases Q with
  | trivial x => simp at he
  | finite Q =>
      simp only [Alternating.AltPath.edgeSet,
        Alternating.FiniteTrace.edgeSet, Set.mem_iUnion] at he
      obtain ⟨i, he⟩ := he
      have hs := (Q.link i).path.edgeSet_subset_support_prod he
      exact ⟨Set.mem_iUnion.2 ⟨i, hs.1⟩,
        Set.mem_iUnion.2 ⟨i, hs.2⟩⟩
  | infinite Q =>
      simp only [Alternating.AltPath.edgeSet,
        Alternating.InfiniteTrace.edgeSet, Set.mem_iUnion] at he
      obtain ⟨i, he⟩ := he
      have hs := (Q.link i).path.edgeSet_subset_support_prod he
      exact ⟨Set.mem_iUnion.2 ⟨i, hs.1⟩,
        Set.mem_iUnion.2 ⟨i, hs.2⟩⟩

/-- The compressed loop-erased route selected for one request has no
forward departure from its prescribed request exit. -/
theorem selectedErasedCompression_noOutgoing_forward_at_requestExit
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ¬ HasOutgoing
      ((selectedErasedCompression U S K r).path.directionEdges .forward)
      (requestExit r) := by
  intro hout
  obtain ⟨z, hz⟩ := hout
  let T := selectedRequestTrace U S K r
  have hzSteps : (requestExit r, z) ∈
      directedSignedEdgeSet .forward T.erasedRoute.steps :=
    T.erasedRoute.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      (fun {_s} hs ↦ T.valid _ (T.erasedRoute.steps_sublist.subset hs))
      .forward hz
  exact T.erasedRoute.noOutgoing_directedSignedEdgeSet_forward_terminal
    ⟨z, hzSteps⟩

/-- Regard an old request as its untagged control. -/
def oldRequestControl
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (r : oldRequests L C) : ControlRequest L C :=
  ⟨r.1, ⟨Sum.inl r, rfl⟩⟩

@[simp] theorem oldRequestControl_val
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (r : oldRequests L C) : (oldRequestControl r).1 = r.1 := rfl

/-- No retained forward prefix in the active simultaneous union departs from
an old request.  This is the endpoint cut used by the final switched
relation; raw (untrimmed) decoded links are intentionally not asserted to
have this property. -/
theorem activeOldRequest_noOutgoing_forward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (r : oldRequests L S.cut)
    (hrActive : IsActiveControl U S K (oldRequestControl r)) :
    ¬ HasOutgoing (erasedSelectedRetainedForwardEdges U S K) r.1 := by
  exact oldRequest_noOutgoing_erasedSelectedRetainedForwardEdges U S K r

/-- Active old requests are sinks of the corrected switched relation. -/
theorem activeOldRequest_noOutgoing_switched
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (r : oldRequests L S.cut)
    (hrActive : IsActiveControl U S K (oldRequestControl r)) :
    ¬ HasOutgoing (erasedSelectedSwitchedEdges U S K) r.1 :=
  GroundingOldExitOutgoingObstruction.oldRequest_noOutgoing U S K r

end GroundingErasedDecode
end Erdos599
