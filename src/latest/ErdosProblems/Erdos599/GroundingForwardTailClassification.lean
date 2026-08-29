/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedSwitchRelation

/-!
# Classification of a selected forward-edge tail

A forward edge retained by the erased decoder is one of the chosen
connectors of the underlying auxiliary path.  Its tail is therefore
represented in exactly one of three ways: by a literal old gadget, by the
tail of an edge gadget, or by the carrier of the starting proxy.

At an old cut point, normalization excludes the first case.  The remaining
edge-gadget and proxy-carrier cases are the precise extra geometry needed
to prove that old request exits have no inserted forward departure.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingForwardTailClassification

open DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Exact auxiliary-gadget provenance of the tail of one selected erased
forward edge. -/
theorem selectedForwardTail_old_or_edge_or_startingProxy
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) {b y : V}
    (hby : (b, y) ∈
      (selectedErasedCompression U S K r).path.directionEdges .forward) :
    (∃ d : L.LV,
        ((PopularAuxiliary.Input.LambdaVertex.old b : L.LV), d) ∈
          (strongSelectedPath U S K r).edgeSet) ∨
      (∃ v : V, ∃ d : L.LV,
        (PopularAuxiliary.Input.LambdaVertex.edge b v, d) ∈
          (strongSelectedPath U S K r).edgeSet) ∨
      ∃ i : I, ∃ d : L.LV,
        (strongSelectedPath U S K r).start = .proxy i ∧
          ((PopularAuxiliary.Input.LambdaVertex.proxy i : L.LV), d) ∈
            (strongSelectedPath U S K r).edgeSet ∧
          b ∈ (L.proxyPath i).support := by
  let p := strongSelectedPath U S K r
  obtain ⟨s, hs, hsForward, hsEdge⟩ :=
    selectedErasedCompression_directionEdge_provenance U S K r .forward hby
  have hraw : (b, y) ∈
      directedSignedEdgeSet .forward (L.decodeWalkSteps p.walk) := by
    exact ⟨s, hs, hsForward, hsEdge⟩
  rw [L.forwardEdges_decodeWalkSteps p.walk] at hraw
  obtain ⟨a, d, had, hchosen⟩ := hraw
  have hconnector := L.chosenConnector?_eq_some hchosen
  have haSupport : a ∈ p.support :=
    (p.edgeSet_subset_support_prod had).1
  rcases hconnector.1 with hExit | ⟨i, hai, hbProxy⟩
  · cases a with
    | old z =>
        have hzb : z = b := Option.some.inj hExit
        subst z
        exact Or.inl ⟨d, had⟩
    | edge u v =>
        have hub : u = b := Option.some.inj hExit
        subst u
        exact Or.inr (Or.inl ⟨v, d, had⟩)
    | proxy i => simp at hExit
  · subst a
    have hpStart : p.start ∈ L.lambda.source :=
      (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
    have hstart : p.start = .proxy i :=
      L.proxy_mem_support_eq_start p hpStart haSupport
    exact Or.inr (Or.inr ⟨i, d, hstart, had, hbProxy⟩)

/-- At a point of `CV`, cut normalization eliminates the literal-old source
gadget from the preceding classification.  Edge gadgets and the initial
proxy carrier remain as the exact unresolved cases. -/
theorem selectedForwardTail_at_CV_edge_or_startingProxy
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) {b y : V}
    (hbCV : b ∈ GroundingCut.CV L S.cut)
    (hby : (b, y) ∈
      (selectedErasedCompression U S K r).path.directionEdges .forward) :
    (∃ v : V, ∃ d : L.LV,
        (PopularAuxiliary.Input.LambdaVertex.edge b v, d) ∈
          (strongSelectedPath U S K r).edgeSet) ∨
      ∃ i : I, ∃ d : L.LV,
        (strongSelectedPath U S K r).start = .proxy i ∧
          ((PopularAuxiliary.Input.LambdaVertex.proxy i : L.LV), d) ∈
            (strongSelectedPath U S K r).edgeSet ∧
          b ∈ (L.proxyPath i).support := by
  rcases selectedForwardTail_old_or_edge_or_startingProxy U S K r hby with
      ⟨d, holdd⟩ | hedge | hproxy
  · have hpFan :=
      (strongSelectedPath_mem_controlledRequestFan U S K r).1
    have holdSupport :
        (PopularAuxiliary.Input.LambdaVertex.old b : L.LV) ∈
          (strongSelectedPath U S K r).support :=
      ((strongSelectedPath U S K r).edgeSet_subset_support_prod holdd).1
    have holdApex :
        (PopularAuxiliary.Input.LambdaVertex.old b : L.LV) =
          requestAuxVertex r := by
      apply Set.mem_singleton_iff.mp
      exact GroundingAssembly.normalizedRequestFan_cut_normalized
        S K r hpFan ⟨holdSupport, GroundingCut.mem_CV.mp hbCV⟩
    have hfinish :
        (strongSelectedPath U S K r).finish = requestAuxVertex r :=
      strongSelectedPath_finish U S K r
    exact False.elim <|
      (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
        (strongSelectedPath U S K r) holdd)
          (holdApex.trans hfinish.symm)
  · exact Or.inl hedge
  · exact Or.inr hproxy

/-- Union-level form: every inserted forward departure from a `CV` point
comes from an edge gadget with that tail or from the starting proxy carrier
of one active selected request. -/
theorem forwardOutgoing_at_CV_edge_or_startingProxy
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {b : V} (hbCV : b ∈ GroundingCut.CV L S.cut)
    (hout : HasOutgoing (erasedSelectedDirectionEdges U S K .forward) b) :
    (∃ c : ActiveControlRequest U S K, ∃ v : V, ∃ d : L.LV,
        (PopularAuxiliary.Input.LambdaVertex.edge b v, d) ∈
          (strongSelectedPath U S K (chosenRequest c.1)).edgeSet) ∨
      ∃ c : ActiveControlRequest U S K, ∃ i : I, ∃ d : L.LV,
        (strongSelectedPath U S K (chosenRequest c.1)).start = .proxy i ∧
          ((PopularAuxiliary.Input.LambdaVertex.proxy i : L.LV), d) ∈
            (strongSelectedPath U S K (chosenRequest c.1)).edgeSet ∧
          b ∈ (L.proxyPath i).support := by
  obtain ⟨y, hby⟩ := hout
  simp only [erasedSelectedDirectionEdges, Set.mem_iUnion] at hby
  obtain ⟨c, hby⟩ := hby
  rcases selectedForwardTail_at_CV_edge_or_startingProxy
      U S K (chosenRequest c.1) hbCV hby with hedge | hproxy
  · obtain ⟨v, d, hvd⟩ := hedge
    exact Or.inl ⟨c, v, d, hvd⟩
  · obtain ⟨i, d, hstart, hid, hbi⟩ := hproxy
    exact Or.inr ⟨c, i, d, hstart, hid, hbi⟩

end GroundingForwardTailClassification
end Erdos599
