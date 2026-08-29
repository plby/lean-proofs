/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedRootClassification
import ErdosProblems.Erdos599.GroundingForwardTailClassification
import ErdosProblems.Erdos599.GroundingErasedEndpointBoundary

/-!
# Rank of owners meeting an earlier exposed component

The strong simultaneous selector makes every later selected auxiliary path
avoid every limiting-ladder component exposed by an earlier selected path,
away from the later request apex.  A compressed backward edge always gives
an actual edge-gadget contact, and head stopping proves that this contact is
not the request apex.  Consequently a later selected route cannot have a
backward link on an earlier exposed component.

This is the strict rank descent needed by the pre-stopped root repair.  It
does not assert that an equal/self-owned backward link is already rooted.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open Alternating PopularGroundingBridge PopularAuxiliary.Input
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

private noncomputable local instance signedEdgeBEq :
    BEq (SignedEdge V) :=
  ⟨fun s t => @decide (s = t) (Classical.propDecidable _)⟩

private local instance signedEdgeLawfulBEq :
    LawfulBEq (SignedEdge V) :=
  ⟨by intro s t; simp⟩

private noncomputable local instance lambdaVertexBEq :
    BEq (LambdaVertex V I) :=
  ⟨fun x y => @decide (x = y) (Classical.propDecidable _)⟩

private local instance lambdaVertexLawfulBEq :
    LawfulBEq (LambdaVertex V I) :=
  ⟨by intro x y; simp⟩

private theorem count_backward_gadgetSteps
    (L : PopularAuxiliary.Input Gamma I) (a : L.LV) (e : V × V) :
    List.count (SignedEdge.backward e) (L.gadgetSteps a) =
      List.count (.edge e.1 e.2) [a] := by
  rcases e with ⟨u, v⟩
  cases a with
  | old x =>
      rw [List.count_eq_zero.mpr (by simp [PopularAuxiliary.Input.gadgetSteps])]
      rw [List.count_eq_zero.mpr (by simp)]
  | edge x y =>
      by_cases hxy : (x, y) = (u, v)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
        exact (List.count_eq_one_of_mem (List.nodup_singleton _)
          (List.mem_singleton_self _)).trans
            (List.count_eq_one_of_mem (List.nodup_singleton _)
              (List.mem_singleton_self _)).symm
      · have hleft :
            List.count (SignedEdge.backward (u, v))
                (L.gadgetSteps (.edge x y)) = 0 :=
          List.count_eq_zero.mpr (by
            simp only [PopularAuxiliary.Input.gadgetSteps,
              List.mem_singleton]
            intro hs
            exact hxy (congrArg SignedEdge.edge hs).symm)
        have hright : List.count (.edge u v : L.LV) [.edge x y] = 0 :=
          List.count_eq_zero.mpr (by
            simp only [List.mem_singleton]
            intro hv
            have huv : u = x ∧ v = y := by simpa using hv
            exact hxy (Prod.ext huv.1.symm huv.2.symm))
        exact hleft.trans hright.symm
  | proxy i =>
      rw [List.count_eq_zero.mpr (by simp [PopularAuxiliary.Input.gadgetSteps])]
      rw [List.count_eq_zero.mpr (by simp)]

private theorem count_backward_connectorSteps
    (L : PopularAuxiliary.Input Gamma I) (a b : L.LV) (e : V × V) :
    List.count (SignedEdge.backward e) (L.connectorSteps a b) = 0 := by
  unfold PopularAuxiliary.Input.connectorSteps
  split <;> simp [SignedEdge.forward, SignedEdge.backward]

private theorem count_backward_decodeWalkSteps
    (L : PopularAuxiliary.Input Gamma I) {a b : L.LV}
    (q : _root_.Erdos599.DirectedPath.Walk L.lambda.graph a b)
    (e : V × V) :
    List.count (SignedEdge.backward e) (L.decodeWalkSteps q) =
      List.count (.edge e.1 e.2) q.support := by
  classical
  induction q with
  | @nil a =>
      rw [L.decodeWalkSteps_nil, count_backward_gadgetSteps,
        _root_.Erdos599.DirectedPath.Walk.support_nil]
  | @cons a b c hab q ih =>
      rw [L.decodeWalkSteps_cons, List.count_append, List.count_append,
        count_backward_gadgetSteps, count_backward_connectorSteps,
        _root_.Erdos599.DirectedPath.Walk.support_cons, ih]
      simp only [List.count_cons, List.count_nil, Nat.zero_add, Nat.add_zero]
      omega

private theorem selectedRequestTrace_edge_backward_not_mem_ownerRank
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (e : edgeRequests L S.cut) :
    SignedEdge.backward e.1 ∉
      (selectedRequestTrace U S K (.inr e)).steps := by
  classical
  let p := strongSelectedPath U S K (.inr e)
  have hstart : p.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩
  have hfinish : p.finish = .edge e.1.1 e.1.2 :=
    strongSelectedPath_finish U S K (.inr e)
  intro hmem
  have hpositive :
      0 < List.count (SignedEdge.backward e.1)
        (selectedRequestTrace U S K (.inr e)).steps :=
    List.count_pos_iff.mpr hmem
  have hgadgetMem : (.edge e.1.1 e.1.2 : L.LV) ∈ p.walk.support := by
    rw [← hfinish]
    exact p.walk.end_mem_support
  have hgadgetCount :
      List.count (.edge e.1.1 e.1.2 : L.LV) p.walk.support = 1 :=
    List.count_eq_one_of_mem p.isPath hgadgetMem
  have htotal := count_backward_decodeWalkSteps L p.walk e.1
  have happ := congrArg (List.count (SignedEdge.backward e.1))
    (L.decodeFinitePathToEdgeEntry_steps_append p hstart
      e.1.1 e.1.2 hfinish)
  have hlast : List.count (SignedEdge.backward e.1)
      [SignedEdge.backward e.1] = 1 :=
    List.count_eq_one_of_mem (List.nodup_singleton _)
      (List.mem_singleton_self _)
  change List.count (SignedEdge.backward e.1)
      ((selectedRequestTrace U S K (.inr e)).steps ++
        [SignedEdge.backward e.1]) =
    List.count (SignedEdge.backward e.1) (L.decodeWalkSteps p.walk) at happ
  rw [List.count_append, hlast, htotal, hgadgetCount] at happ
  omega

/-- A selected compressed backward edge has a literal edge-gadget contact
on the selected auxiliary path, and that contact is not the terminal request
apex.  The second conclusion is the exact point where the edge-request
head-stopping convention is used. -/
theorem selectedBackwardEdge_auxContact_offApex
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.directionEdges
      .backward) :
    (LambdaVertex.edge e.1 e.2 : L.LV) ∈
        (strongSelectedPath U S K r).support ∧
      (LambdaVertex.edge e.1 e.2 : L.LV) ≠ requestAuxVertex r := by
  let T := selectedRequestTrace U S K r
  obtain ⟨s, hs, hsd, hse⟩ :=
    EndpointTrace.erasedCompression_directionEdges_subset_steps
      L T .backward he
  have hsRaw : s ∈ L.decodeWalkSteps
      (strongSelectedPath U S K r).walk :=
    (selectedRequestTrace_steps_sublist U S K r).subset hs
  have heGadget : (LambdaVertex.edge e.1 e.2 : L.LV) ∈
      (strongSelectedPath U S K r).support := by
    have heSigned : e ∈ directedSignedEdgeSet .backward
        (L.decodeWalkSteps (strongSelectedPath U S K r).walk) :=
      ⟨s, hsRaw, hsd, hse⟩
    rw [L.backwardEdges_decodeWalkSteps
      (strongSelectedPath U S K r).walk] at heSigned
    exact heSigned
  refine ⟨heGadget, ?_⟩
  cases r with
  | inl x =>
      intro heApex
      cases heApex
  | inr f =>
      intro heApex
      have hef : e = f.1 := by
        exact Prod.ext
          (LambdaVertex.edge.inj heApex).1
          (LambdaVertex.edge.inj heApex).2
      have hsEq : s = SignedEdge.backward e := by
        rcases s with ⟨se, sd⟩
        simp only at hsd hse
        subst sd
        subst se
        rfl
      have hnot :=
        selectedRequestTrace_edge_backward_not_mem_ownerRank U S K f
      apply hnot
      rw [← hef]
      exact hsEq ▸ (by simpa only [T] using hs)

/-- A route selected later in the request chronology has no backward link
on any limiting-ladder component exposed by the earlier selected route.
The conclusion is stated as a negation so it can be used directly to orient
the owner of a deleted parent edge. -/
theorem laterSelected_no_backwardLink_on_exposedComponent
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L (strongSelectedPath U S K r))
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression U S K s).path.links)
    (hldir : l.direction = .backward) :
    ¬ l.path.IsSubpathOf Y := by
  intro hsub
  have hnonempty : l.path.edgeSet.Nonempty := by
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    exact ⟨(l.path.start, y), hy⟩
  obtain ⟨e, heLink⟩ := hnonempty
  have heDirection : e ∈
      (selectedErasedCompression U S K s).path.directionEdges .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, heLink⟩
  obtain ⟨hePath, heOffApex⟩ :=
    selectedBackwardEdge_auxContact_offApex U S K s heDirection
  have heTrace : (LambdaVertex.edge e.1 e.2 : L.LV) ∈
      metLadderTrace L (strongSelectedPath U S K r) := by
    apply (mem_metLadderTrace_iff L
      (strongSelectedPath U S K r) (.edge e.1 e.2)).2
    exact ⟨Y, hY, Or.inr ⟨e, hsub.2 heLink, rfl⟩⟩
  exact Set.disjoint_left.1
    (strongSelectedPath_avoids_earlier_components U S K r s hrs)
    hePath ⟨heTrace, by
      simpa only [Set.mem_singleton_iff] using heOffApex⟩

/-- Control-rank form of the preceding exclusion.  A selected backward
link on a component exposed by an active control has an owner control which
is either that control itself or strictly earlier; it can never be later. -/
theorem activeBackwardOwner_eq_or_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (c d : ActiveControlRequestAt U S K T)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest c.1)))
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression U S K
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hsub : l.path.IsSubpathOf Y) :
    d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1 := by
  rcases lt_trichotomy (controlRank U S d.1)
      (controlRank U S c.1) with hdc | heq | hcd
  · exact Or.inr hdc
  · exact Or.inl ((controlRank U S).injective heq)
  · exfalso
    exact laterSelected_no_backwardLink_on_exposedComponent
      U S K (chosenRequest c.1) (chosenRequest d.1) hcd
        Y hY l hl hldir hsub

/-- A forward edge of a later selected route cannot depart from a component
exposed by an earlier selected route.  Ordinary and edge-gadget departures
give a literal off-apex contact with the earlier complete ladder trace.  A
hidden proxy departure gives the corresponding certified proxy collision;
loop-erased terminality excludes the one apparent apex exception. -/
theorem laterSelected_no_forwardEdgeTail_on_exposedComponent
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L (strongSelectedPath U S K r))
    {b y : V}
    (hby : (b, y) ∈
      (selectedErasedCompression U S K s).path.directionEdges .forward)
    (hbY : b ∈ Y.support) : False := by
  let p := strongSelectedPath U S K s
  let q := strongSelectedPath U S K r
  have hpFan : p ∈
      (GroundingControlledAssembly.controlledRequestFan S K s).paths :=
    strongSelectedPath_mem_controlledRequestFan U S K s
  have hpStart : p.start ∈ L.lambda.source :=
    (GroundingControlledAssembly.controlledRequestFan S K s).starts_in_source
      hpFan
  have hYL : Y ∈ L.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      hfaith q hY
  have hnoExit : b ≠ requestExit s := by
    intro hb
    exact selectedErasedCompression_noOutgoing_forward_at_requestExit
      U S K s ⟨y, by simpa only [hb] using hby⟩
  have holdOffApex : (LambdaVertex.old b : L.LV) ≠ requestAuxVertex s := by
    intro hApex
    apply hnoExit
    have hentry := congrArg L.gadgetEntry hApex
    simpa using hentry
  rcases
      GroundingForwardTailClassification.selectedForwardTail_old_or_edge_or_startingProxy
        U S K s hby with hold | hedge | hproxy
  · obtain ⟨d, hbd⟩ := hold
    have hbSupport : (LambdaVertex.old b : L.LV) ∈ p.support :=
      (p.edgeSet_subset_support_prod hbd).1
    have hbTrace : (LambdaVertex.old b : L.LV) ∈
        metLadderTrace L q :=
      (mem_metLadderTrace_iff L q (.old b)).2
        ⟨Y, hY, Or.inl ⟨b, hbY, rfl⟩⟩
    exact Set.disjoint_left.1
      (strongSelectedPath_avoids_earlier_components U S K r s hrs)
        hbSupport ⟨hbTrace, by
          simpa only [Set.mem_singleton_iff] using holdOffApex⟩
  · obtain ⟨v, d, hvd⟩ := hedge
    have hedgeSupport : (LambdaVertex.edge b v : L.LV) ∈ p.support :=
      (p.edgeSet_subset_support_prod hvd).1
    have hbvFamily : (b, v) ∈ L.familyEdges :=
      L.edgeNode_mem_familyEdges_of_start_in_source
        p hpStart hedgeSupport
    obtain ⟨Z, hZL, hbvZ⟩ := hbvFamily
    have hZY : Z = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        hZL hYL (Z.edgeSet_subset_support_prod hbvZ).1 hbY
    have hbvY : (b, v) ∈ Y.edgeSet := hZY ▸ hbvZ
    have hedgeTrace : (LambdaVertex.edge b v : L.LV) ∈
        metLadderTrace L q :=
      (mem_metLadderTrace_iff L q (.edge b v)).2
        ⟨Y, hY, Or.inr ⟨(b, v), hbvY, rfl⟩⟩
    have hedgeOffApex :
        (LambdaVertex.edge b v : L.LV) ≠ requestAuxVertex s := by
      intro hApex
      have hfinish : p.finish = requestAuxVertex s :=
        strongSelectedPath_finish U S K s
      exact (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet p hvd)
        (hApex.trans hfinish.symm)
    exact Set.disjoint_left.1
      (strongSelectedPath_avoids_earlier_components U S K r s hrs)
        hedgeSupport ⟨hedgeTrace, by
          simpa only [Set.mem_singleton_iff] using hedgeOffApex⟩
  · obtain ⟨i, d, hstart, hid, hbi⟩ := hproxy
    have hproxyY : L.proxyPath i = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        (hfaith.1 i) hYL hbi hbY
    have hbTrace : (LambdaVertex.old b : L.LV) ∈
        metLadderTrace L q :=
      (mem_metLadderTrace_iff L q (.old b)).2
        ⟨Y, hY, Or.inl ⟨b, hbY, rfl⟩⟩
    have hbProxyTrace : (LambdaVertex.old b : L.LV) ∈
        startingProxyTrace L p := by
      change (LambdaVertex.old b : L.LV) ∈
        startingProxyTrace L (strongSelectedPath U S K s)
      simp [startingProxyTrace, hstart, hproxyY,
        PopularSwitching.ladderTrace, hbY]
    apply strongSelectedPath_proxy_avoids_earlier_components
      U S K r s hrs
    rw [certifiedProxyComponentCollidingPaths, dif_pos hfaith]
    exact ⟨hpFan, .old b, ⟨hbTrace, by
      simpa only [Set.mem_singleton_iff] using holdOffApex⟩,
      hbProxyTrace⟩

/-- Control-rank form of the forward-tail exclusion.  If a retained edge
of an active route departs from a component exposed by another active
control, then its owner is that control or is strictly earlier. -/
theorem activeForwardTailOwner_eq_or_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (c d : ActiveControlRequestAt U S K T)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest c.1)))
    {f : V × V}
    (hf : f ∈ retainedForwardEdgesAt T
      (selectedErasedCompression U S K (chosenRequest d.1)).path)
    (hftail : f.1 ∈ Y.support) :
    d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1 := by
  rcases lt_trichotomy (controlRank U S d.1)
      (controlRank U S c.1) with hdc | heq | hcd
  · exact Or.inr hdc
  · exact Or.inl ((controlRank U S).injective heq)
  · exfalso
    exact laterSelected_no_forwardEdgeTail_on_exposedComponent
      U S K hfaith (chosenRequest c.1) (chosenRequest d.1) hcd
        Y hY
        (retainedForwardEdgesAt_subset_directionEdges T _ hf) hftail

/-- Owner-refined form for one globally selected backward edge lying on a
component exposed by an active control.  The unique ladder owner of the
backward link is that exposed component, so the owner-rank orientation
applies directly. -/
theorem selectedBackwardEdge_owner_eq_or_rank_lt_of_mem_exposedParent
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (c : ActiveControlRequestAt U S K T)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest c.1)))
    {e : V × V}
    (heSelected : e ∈ erasedSelectedDirectionEdgesAt
      U S K T .backward)
    (heY : e ∈ Y.edgeSet) :
    ∃ (d : ActiveControlRequestAt U S K T)
        (l : Alternating.Link Gamma.graph) (parent : Gamma.DPath),
      l ∈ (selectedErasedCompression U S K
        (chosenRequest d.1)).path.links ∧
      l.direction = .backward ∧ e ∈ l.path.edgeSet ∧
      parent ∈ L.ladder.paths ∧ l.path.IsSubpathOf parent ∧
      parent = Y ∧
      (d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1) := by
  obtain ⟨d, l, parent, hl, hldir, hel, hparent, hsub⟩ :=
    DWeb.KappaLadder.exists_erasedSelectedBackwardEdge_ownerAt
      K T heSelected
  have hYL : Y ∈ L.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      hfaith _ hY
  have heParent : e ∈ parent.edgeSet := hsub.2 hel
  have hparentY : parent = Y :=
    Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
      hparent hYL
        (parent.edgeSet_subset_support_prod heParent).1
        (Y.edgeSet_subset_support_prod heY).1
  have hrank := activeBackwardOwner_eq_or_rank_lt
    U S K T c d Y hY l hl hldir (by simpa only [hparentY] using hsub)
  exact ⟨d, l, parent, hl, hldir, hel, hparent, hsub,
    hparentY, hrank⟩

/-- Rank orientation for the active owner of a retained forward edge which
shares its tail with a parent edge on an exposed component. -/
theorem sameTailForwardOwner_eq_or_rank_lt_of_mem_exposedParent
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (c d : ActiveControlRequestAt U S K T)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest c.1)))
    {e f : V × V}
    (heY : e ∈ Y.edgeSet)
    (hf : f ∈ retainedForwardEdgesAt T
      (selectedErasedCompression U S K (chosenRequest d.1)).path)
    (htail : e.1 = f.1) :
    d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1 := by
  apply activeForwardTailOwner_eq_or_rank_lt
    U S K T hfaith c d Y hY hf
  rw [← htail]
  exact (Y.edgeSet_subset_support_prod heY).1

/-- Complete owner-rank reduction for an unrooted last deleted head on a
finite segment of a component exposed by an active absorber.  Once cut
heads and retained active-route vertices are rooted, the remaining deletion
is owned either by a backward link or by a same-tail forward divergence;
in both cases the owner is the absorber itself or has strictly smaller
control rank. -/
theorem DWeb.KappaLadder.LastDeletedHead.backward_or_sameTail_ownerRank
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (A : Set V)
    (c : ActiveControlRequestAt U S K ∅)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest c.1)))
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hpY : p.edgeSet ⊆ Y.edgeSet)
    (D : DWeb.KappaLadder.LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt U S K ∅))
    (hcontrolRoot : ∀ d : ControlRequest L S.cut,
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
        a d.1)
    (hretainedRoot : ∀ d : ActiveControlRequestAt U S K ∅, ∀ x,
      x ∈ retainedForwardVerticesAt ∅
          (selectedErasedCompression U S K (chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
          a x)
    (hheadNotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
      a D.head) :
    (∃ (u : V) (d : ActiveControlRequestAt U S K ∅)
        (l : Alternating.Link Gamma.graph) (parent : Gamma.DPath),
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ erasedSelectedDirectionEdgesAt
        U S K ∅ .backward ∧
      l ∈ (selectedErasedCompression U S K
        (chosenRequest d.1)).path.links ∧
      l.direction = .backward ∧ (u, D.head) ∈ l.path.edgeSet ∧
      parent ∈ L.ladder.paths ∧ l.path.IsSubpathOf parent ∧
      parent = Y ∧
      (d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1)) ∨
    ∃ (u : V) (d : ActiveControlRequestAt U S K ∅)
        (f : V × V),
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅ ∧
      f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression U S K (chosenRequest d.1)).path ∧
      u = f.1 ∧
      (d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1) := by
  have hYL : Y ∈ L.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      hfaith _ hY
  have hpFamily : p.edgeSet ⊆ L.familyEdges := by
    intro e he
    exact ⟨Y, hYL, hpY he⟩
  rcases D.backward_or_sameTail_of_head_not_rootedPreStopped
      K A hpFamily hcontrolRoot hretainedRoot hheadNotRooted with
      ⟨u, huParent, huBackward⟩ |
      ⟨u, d, f, huParent, huConflict, hf, htail⟩
  · obtain ⟨d, l, parent, hl, hldir, hel, hparent, hsub,
        hparentY, hrank⟩ :=
      selectedBackwardEdge_owner_eq_or_rank_lt_of_mem_exposedParent
        U S K ∅ hfaith c Y hY huBackward (hpY huParent)
    exact Or.inl ⟨u, d, l, parent, huParent, huBackward, hl,
      hldir, hel, hparent, hsub, hparentY, hrank⟩
  · have hrank :=
      sameTailForwardOwner_eq_or_rank_lt_of_mem_exposedParent
        U S K ∅ hfaith c d Y hY (hpY huParent) hf htail
    exact Or.inr ⟨u, d, f, huParent, huConflict, hf, htail, hrank⟩

/-- The owner-oriented normal form of an inactive-control root obstruction.

The data already contains the absorbing active request, the exposed parent,
and the last unrooted deleted head on the ordered contact segment.  Once cut
heads and retained active-route vertices are rooted, the only remaining
deletion is owned by an active route which is either the absorber itself or
has strictly smaller control rank.  Keeping the self alternative explicit is
essential: freshness excludes later owners, but does not by itself repair a
route which switches its own exposed parent. -/
inductive DWeb.KappaLadder.InactivePreStoppedRootObstructionData.OwnerRankOutcome
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    {A : Set V} {c : GroundingErasedDecode.ControlRequest L S.cut}
    (data : DWeb.KappaLadder.InactivePreStoppedRootObstructionData
      S K A c) : Prop
  | backward
      (u : V)
      (d : GroundingErasedDecode.ActiveControlRequestAt U S K ∅)
      (l : Alternating.Link Gamma.graph) (parent : Gamma.DPath)
      (parentEdge : (u, data.deleted.head) ∈ data.segment.edgeSet)
      (selected : (u, data.deleted.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K ∅ .backward)
      (linkMem : l ∈ (GroundingErasedDecode.selectedErasedCompression
        U S K (GroundingErasedDecode.chosenRequest d.1)).path.links)
      (linkBackward : l.direction = .backward)
      (edgeMem : (u, data.deleted.head) ∈ l.path.edgeSet)
      (parentMem : parent ∈ L.ladder.paths)
      (linkSubpath : l.path.IsSubpathOf parent)
      (parentEq : parent = data.parent)
      (ownerRank : d.1 = data.absorber.1 ∨
        GroundingErasedDecode.controlRank U S d.1 <
          GroundingErasedDecode.controlRank U S data.absorber.1)
  | sameTail
      (u : V)
      (d : GroundingErasedDecode.ActiveControlRequestAt U S K ∅)
      (f : V × V)
      (parentEdge : (u, data.deleted.head) ∈ data.segment.edgeSet)
      (conflict : (u, data.deleted.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K ∅)
      (retained : f ∈ GroundingErasedDecode.retainedForwardEdgesAt ∅
        (GroundingErasedDecode.selectedErasedCompression
          U S K (GroundingErasedDecode.chosenRequest d.1)).path)
      (sameTail : u = f.1)
      (ownerRank : d.1 = data.absorber.1 ∨
        GroundingErasedDecode.controlRank U S d.1 <
          GroundingErasedDecode.controlRank U S data.absorber.1)

/-- Package the complete last-deleted-head owner classification directly on
the finite obstruction produced by an inactive control. -/
theorem DWeb.KappaLadder.InactivePreStoppedRootObstructionData.ownerRankOutcome
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    {A : Set V} {c : GroundingErasedDecode.ControlRequest L S.cut}
    (data : DWeb.KappaLadder.InactivePreStoppedRootObstructionData
      S K A c)
    (hcontrolRoot : ∀ d : GroundingErasedDecode.ControlRequest L S.cut,
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
        a d.1)
    (hretainedRoot : ∀
      d : GroundingErasedDecode.ActiveControlRequestAt U S K ∅, ∀ x,
      x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
          (GroundingErasedDecode.selectedErasedCompression
            U S K (GroundingErasedDecode.chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K ∅)
          a x) :
    data.OwnerRankOutcome := by
  rcases data.deleted.backward_or_sameTail_ownerRank
      K hfaith A data.absorber data.parent data.parent_exposed
      data.segment_edges hcontrolRoot hretainedRoot
      data.deleted_head_not_rooted with
      ⟨u, d, l, parent, huSegment, huSelected, hl, hldir, hul,
        hparent, hsub, hparentEq, hrank⟩ |
      ⟨u, d, f, huSegment, huConflict, hf, htail, hrank⟩
  · exact .backward u d l parent huSegment huSelected hl hldir hul
      hparent hsub hparentEq hrank
  · exact .sameTail u d f huSegment huConflict hf htail hrank

end Erdos599

#print axioms Erdos599.selectedBackwardEdge_auxContact_offApex
#print axioms Erdos599.laterSelected_no_backwardLink_on_exposedComponent
#print axioms Erdos599.activeBackwardOwner_eq_or_rank_lt
#print axioms Erdos599.laterSelected_no_forwardEdgeTail_on_exposedComponent
#print axioms Erdos599.activeForwardTailOwner_eq_or_rank_lt
#print axioms Erdos599.selectedBackwardEdge_owner_eq_or_rank_lt_of_mem_exposedParent
#print axioms Erdos599.sameTailForwardOwner_eq_or_rank_lt_of_mem_exposedParent
#print axioms Erdos599.DWeb.KappaLadder.LastDeletedHead.backward_or_sameTail_ownerRank
#print axioms Erdos599.DWeb.KappaLadder.InactivePreStoppedRootObstructionData.ownerRankOutcome
