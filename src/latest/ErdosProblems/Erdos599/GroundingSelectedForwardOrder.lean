/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingDecodedContactOrder
import ErdosProblems.Erdos599.GroundingForwardTailClassification
import ErdosProblems.Erdos599.GroundingSelectedBackwardOrder

/-!
# Order of retained selected forward tails on a fragment

The tail of a decoded forward connector is represented by an old gadget, an
edge gadget, or the selected path's initial proxy.  Assertion 8.21 handles
the first two cases (with a cut-vertex boundary alternative); this file
packages that exact trichotomy for retained forward edges.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingSelectedForwardOrder

open DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Reverse the edge gadgets of a nonempty segment of one proxy path while
starting directly at the proxy source.  Compared with
`GroundingCutDecoder.reverseGadgetCore`, the initial `old b` vertex is
deleted and replaced by the proxy-to-last-edge arc. -/
private def proxyReverseGadgetCore
    (L : PopularAuxiliary.Input Gamma I) (i : I) :
    ∀ {a c b : V} (h : Gamma.graph.Adj a c)
      (q : Walk Gamma.graph c b),
      (Walk.cons h q).edgeSet ⊆ (L.proxyPath i).edgeSet →
      (a, c) ∈ L.familyEdges → q.edgeSet ⊆ L.familyEdges →
        Walk L.lambda.graph (.proxy i) (.edge a c)
  | a, c, _, h, .nil, hproxy, hac, _ => by
      have hacProxy : (a, c) ∈ (L.proxyPath i).edgeSet := by
        apply hproxy
        simp
      have ha : a ∈ (L.proxyPath i).support :=
        ((L.proxyPath i).edgeSet_subset_support_prod hacProxy).1
      exact .cons ((L.lambda_adj_proxy_edge i a c).2
        ⟨hac, a, ha, h⟩) .nil
  | a, c, _, h, @Walk.cons _ _ _ d _ hcd q,
      hproxy, hac, hfamily => by
      have hcdFamily : (c, d) ∈ L.familyEdges := hfamily (by simp)
      have hqFamily : q.edgeSet ⊆ L.familyEdges := by
        intro e he
        exact hfamily (by simp [he])
      have htailProxy : (Walk.cons hcd q).edgeSet ⊆
          (L.proxyPath i).edgeSet := by
        intro e he
        apply hproxy
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at he ⊢
        tauto
      exact (proxyReverseGadgetCore L i hcd q htailProxy
        hcdFamily hqFamily).concat <|
          (L.lambda_adj_edge_edge c d a c).2
            ⟨hcdFamily, hac, Or.inl rfl⟩

/-- Support accounting for the proxy-started reverse gadget core. -/
private theorem mem_proxyReverseGadgetCore_support
    (L : PopularAuxiliary.Input Gamma I) (i : I)
    {a c b : V} (h : Gamma.graph.Adj a c)
    (q : Walk Gamma.graph c b)
    (hproxy : (Walk.cons h q).edgeSet ⊆ (L.proxyPath i).edgeSet)
    (hac : (a, c) ∈ L.familyEdges)
    (hfamily : q.edgeSet ⊆ L.familyEdges) {z : L.LV}
    (hz : z ∈ (proxyReverseGadgetCore L i h q
      hproxy hac hfamily).support) :
    z = .proxy i ∨ ∃ e ∈ (Walk.cons h q).edgeSet,
      z = LambdaVertex.edge e.1 e.2 := by
  induction q generalizing a with
  | nil =>
      simp [proxyReverseGadgetCore] at hz ⊢
      exact hz
  | @cons c d b hcd q ih =>
      have hcdFamily : (c, d) ∈ L.familyEdges := hfamily (by simp)
      have hqFamily : q.edgeSet ⊆ L.familyEdges := by
        intro e he
        exact hfamily (by simp [he])
      have htailProxy : (Walk.cons hcd q).edgeSet ⊆
          (L.proxyPath i).edgeSet := by
        intro e he
        apply hproxy
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at he ⊢
        tauto
      simp only [proxyReverseGadgetCore, Walk.support_concat,
        Walk.support_cons, List.tail_cons, List.nil_append,
        List.mem_append, List.mem_cons, List.not_mem_nil] at hz
      rcases hz with hz | hz
      · rcases ih hcd htailProxy hcdFamily hqFamily hz with
          hzProxy | ⟨e, he, hze⟩
        · exact Or.inl hzProxy
        · refine Or.inr ⟨e, ?_, hze⟩
          simp only [Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff] at he ⊢
          tauto
      · have hza : z = .edge a c := by simpa using hz
        exact Or.inr ⟨(a, c), by simp, by simpa using hza⟩

/-- A strict reverse traversal of a fragment lying on a proxy path can be
started at the proxy source itself.  This is precisely the hidden-source
endpoint case of the Assertion 8.21 decoder. -/
theorem exists_avoiding_proxy_reverse_to_relaxedEscape
    (L : PopularAuxiliary.Input Gamma I) (C : Set L.LV)
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {i : I} (hparent : P.parent = L.proxyPath i)
    (hproxyNotCut : (LambdaVertex.proxy i : L.LV) ∉ C)
    {b x : V} (hbx : GroundingCut.Before P.path b x)
    (E : L.RelaxedEscape C b) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .proxy i ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r C := by
  obtain ⟨p, hpStart, _hpFinish, hpEdges⟩ :=
    GroundingCutDecoder.exists_forward_segment_of_before hbx
  have hpNe : p.start ≠ p.finish := by
    intro h
    exact hbx.2 (hpStart.symm.trans (h.trans _hpFinish))
  obtain ⟨c, hac, tail, hpWalk⟩ :=
    RelationalRoof.exists_cons_of_start_ne_finish
      Gamma.graph.Adj p.walk hpNe
  have hacEdge : (p.start, c) ∈ p.edgeSet := by
    change (p.start, c) ∈ p.walk.edgeSet
    rw [hpWalk]
    simp
  have hacFragment : (p.start, c) ∈ P.path.edgeSet := hpEdges hacEdge
  have hacFamily : (p.start, c) ∈ L.familyEdges :=
    ⟨P.parent, P.parent_mem, P.edges_subset hacFragment⟩
  have htailFamily : tail.edgeSet ⊆ L.familyEdges := by
    intro e he
    have hep : e ∈ p.edgeSet := by
      change e ∈ p.walk.edgeSet
      rw [hpWalk]
      exact Set.mem_union_right _ he
    exact ⟨P.parent, P.parent_mem, P.edges_subset (hpEdges hep)⟩
  have hwholeFragment :
      (Walk.cons hac tail).edgeSet ⊆ P.path.edgeSet := by
    intro e he
    apply hpEdges
    change e ∈ p.walk.edgeSet
    simpa only [hpWalk] using he
  have hwholeProxy : (Walk.cons hac tail).edgeSet ⊆
      (L.proxyPath i).edgeSet := by
    intro e he
    rw [← hparent]
    exact P.edges_subset (hwholeFragment he)
  let core : Walk L.lambda.graph (.proxy i) (.edge p.start c) :=
    proxyReverseGadgetCore L i hac tail hwholeProxy
      hacFamily htailFamily
  have hcoreAvoid : Disjoint
      ({z | z ∈ core.support} : Set L.LV) C := by
    rw [Set.disjoint_left]
    intro z hz hzC
    rcases mem_proxyReverseGadgetCore_support L i hac tail
        hwholeProxy hacFamily htailFamily hz with rfl | ⟨e, he, rfl⟩
    · exact hproxyNotCut hzC
    · exact GroundingCutDecoder.edge_not_mem_cut_of_not_mem_CE
        L C ⟨P.parent, P.parent_mem,
          P.edges_subset (hwholeFragment he)⟩
        (fun heC ↦ Set.disjoint_left.1 hP.1
          (hwholeFragment he) heC) hzC
  have hjoin : L.lambda.graph.Adj (.edge p.start c) E.route.start := by
    rcases E.start_eq with hordinary | hrelaxed
    · have hstart : E.route.start = .old p.start := by
        simpa only [hpStart] using hordinary
      rw [hstart]
      exact (L.lambda_adj_edge_old p.start c p.start).2
        ⟨hacFamily, Or.inl rfl⟩
    · apply GroundingCutDecoder.lambda_adj_edge_of_relaxedForwardStep
        L hacFamily
      simpa only [hpStart] using hrelaxed
  let suffix : Walk L.lambda.graph (.edge p.start c) E.route.finish :=
    .cons hjoin E.route.walk
  let raw : Walk L.lambda.graph (.proxy i) E.route.finish :=
    core.append suffix
  obtain ⟨q, hqSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) raw
  let r : FinitePath L.lambda.graph :=
    { start := .proxy i
      finish := E.route.finish
      walk := q.1
      isPath := q.2 }
  refine ⟨r, rfl, E.target, ?_⟩
  change Disjoint r.support C
  rw [Set.disjoint_left]
  intro z hzr hzC
  have hzRaw : z ∈ raw.support := hqSupport hzr
  have hzAppend : z ∈ core.support ++ suffix.support.tail := by
    simpa only [raw, Walk.support_append] using hzRaw
  rcases List.mem_append.mp hzAppend with hzCore | hzSuffix
  · exact Set.disjoint_left.1 hcoreAvoid hzCore hzC
  · have hzRoute : z ∈ E.route.support := by
      change z ∈ E.route.walk.support
      simpa only [suffix, Walk.support_cons, List.tail_cons] using hzSuffix
    exact Set.disjoint_left.1 E.avoids hzRoute hzC

/-- A starting-proxy attachment to a blockable retained fragment is no
later than its blocking point, unless the attachment itself is an old cut
vertex.  The proxy case is the endpoint omitted by the ordinary old/edge
forms of Assertion 8.21.

If the attachment `b` were strictly after `bl(P)`, reverse the surviving
fragment segment from `b` to the relaxed escape at `bl(P)`.  The predecessor
edge of `b` lies on the same proxy path.  It therefore lets us replace the
resulting `old b` start by either the proxy-to-old arc (when `old b` is a
target) or the proxy-to-edge arc followed by the standard edge-start
replacement.  In both cases this gives a cut-avoiding auxiliary
source--target path, contradicting separation. -/
theorem startingProxyTail_beforeEq_or_mem_CV
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (hfaith : ProxyPathsFaithful L)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {b : V} (hbP : b ∈ P.path.support)
    {i : I}
    (hstart : (strongSelectedPath U S K r).start = .proxy i)
    (hbProxy : b ∈ (L.proxyPath i).support) :
    GroundingCut.BeforeEq P.path b
        (GroundingCut.blockingPoint L S.cut P) ∨
      b ∈ GroundingCut.CV L S.cut := by
  by_cases hbCV : b ∈ GroundingCut.CV L S.cut
  · exact Or.inr hbCV
  · left
    have hblP : GroundingCut.blockingPoint L S.cut P ∈ P.path.support :=
      GroundingCut.blockingPoint_mem_support L S.cut P hblockable
    rcases GroundingCut.beforeEq_total hbP hblP with hbBefore | hblBefore
    · exact hbBefore
    · by_contra hbNotBefore
      have hblNe : GroundingCut.blockingPoint L S.cut P ≠ b := by
        intro hEq
        apply hbNotBefore
        simpa only [hEq] using GroundingCut.beforeEq_refl hbP
      have hstrict : GroundingCut.Before P.path
          (GroundingCut.blockingPoint L S.cut P) b :=
        ⟨hblBefore, hblNe⟩
      have hescape :
          PopularAuxiliary.Input.Fragment.MeetsEscape L S.cut P := by
        by_contra hnoEscape
        have hfinite : P.path.IsFinite :=
          hblockable.resolve_left hnoEscape
        obtain ⟨t, ht⟩ := hfinite
        have hbt : GroundingCut.BeforeEq P.path b t :=
          GroundingCut.beforeEq_terminal ht hbP
        have hblEq : GroundingCut.blockingPoint L S.cut P = t :=
          GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
            L S.cut P hnoEscape ht
        apply hbNotBefore
        simpa only [hblEq] using hbt
      have hparent : P.parent = L.proxyPath i :=
        Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
          P.parent_mem (hfaith.1 i) (P.support_subset hbP) hbProxy
      have hproxySupport : (LambdaVertex.proxy i : L.LV) ∈
          (strongSelectedPath U S K r).support := by
        rw [← hstart]
        exact (strongSelectedPath U S K r).start_mem_support
      have hproxyNotCut : (LambdaVertex.proxy i : L.LV) ∉ S.cut := by
        intro hiCut
        have hiApex := strongSelectedPath_cut_contact_eq_requestAuxVertex
          U S K r hproxySupport hiCut
        cases r <;> cases hiApex
      have hproxySource :
          (LambdaVertex.proxy i : L.LV) ∈ L.lambda.source :=
        L.mem_lambda_source_proxy i
      obtain ⟨E⟩ :=
        GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
          L S.cut P hescape
      obtain ⟨t, htStart, htTarget, htAvoid⟩ :=
        exists_avoiding_proxy_reverse_to_relaxedEscape
          L S.cut P hP.1 hparent hproxyNotCut hstrict E
      exact PopularAuxiliary.Input.no_avoiding_source_target_path
        L.lambda S.cut S.separates t (htStart ▸ hproxySource)
          htTarget htAvoid

/-- Owner-level forward-tail trichotomy.  The only case not directly
bounded by Assertion 8.21 is the hidden attachment point of a starting
proxy, retained explicitly for the grounded-source argument. -/
theorem selectedRetainedForwardTail_beforeEq_or_mem_CV_or_startingProxy
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {b y : V}
    (hby : (b, y) ∈ retainedForwardEdges (L := L) S.cut
      (selectedErasedCompression U S K r).path)
    (hbP : b ∈ P.path.support) :
    GroundingCut.BeforeEq P.path b
        (GroundingCut.blockingPoint L S.cut P) ∨
      b ∈ GroundingCut.CV L S.cut ∨
      ∃ i : I, ∃ d : L.LV,
        (strongSelectedPath U S K r).start = .proxy i ∧
          ((LambdaVertex.proxy i : L.LV), d) ∈
            (strongSelectedPath U S K r).edgeSet ∧
          b ∈ (L.proxyPath i).support := by
  have hbyForward : (b, y) ∈
      (selectedErasedCompression U S K r).path.directionEdges .forward :=
    retainedForwardEdges_subset_directionEdges S.cut _ hby
  rcases GroundingForwardTailClassification.selectedForwardTail_old_or_edge_or_startingProxy
      U S K r hbyForward with hold | hedge | hproxy
  · obtain ⟨d, hbd⟩ := hold
    have hbSupport : (LambdaVertex.old b : L.LV) ∈
        (strongSelectedPath U S K r).support :=
      ((strongSelectedPath U S K r).edgeSet_subset_support_prod hbd).1
    by_cases hbApex :
        (LambdaVertex.old b : L.LV) = requestAuxVertex r
    · exact Or.inr <| Or.inl <| GroundingCut.mem_CV.mpr <|
        hbApex ▸ requestAuxVertex_mem_cut r
    · exact Or.inl <|
        GroundingDecodedContactOrder.strongSelectedPath_fragmentContact_beforeEq_blockingPoint
          S K r P hP hblockable ⟨⟨hbSupport, hbApex⟩, hbP⟩
  · obtain ⟨v, d, hvd⟩ := hedge
    have hedgeSupport : (LambdaVertex.edge b v : L.LV) ∈
        (strongSelectedPath U S K r).support :=
      ((strongSelectedPath U S K r).edgeSet_subset_support_prod hvd).1
    have hedgeNotApex :
        (LambdaVertex.edge b v : L.LV) ≠ requestAuxVertex r := by
      intro hedgeApex
      have hfinish := strongSelectedPath_finish U S K r
      exact (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
        (strongSelectedPath U S K r) hvd)
          (hedgeApex.trans hfinish.symm)
    exact (GroundingSelectedBackwardOrder.strongSelectedPath_edgeGadgetTail_beforeEq_or_mem_CV
        U S K r P hP hblockable hedgeSupport hedgeNotApex hbP).imp_right
          Or.inl
  · exact Or.inr (Or.inr hproxy)

/-- Under faithful proxy encoding the owner-level trichotomy has no
exceptional proxy branch. -/
theorem selectedRetainedForwardTail_beforeEq_or_mem_CV
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (hfaith : ProxyPathsFaithful L)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {b y : V}
    (hby : (b, y) ∈ retainedForwardEdges (L := L) S.cut
      (selectedErasedCompression U S K r).path)
    (hbP : b ∈ P.path.support) :
    GroundingCut.BeforeEq P.path b
        (GroundingCut.blockingPoint L S.cut P) ∨
      b ∈ GroundingCut.CV L S.cut := by
  rcases selectedRetainedForwardTail_beforeEq_or_mem_CV_or_startingProxy
      U S K r P hP hblockable hby hbP with
      horder | hbCV | ⟨i, _d, hstart, _hid, hbi⟩
  · exact Or.inl horder
  · exact Or.inr hbCV
  · exact startingProxyTail_beforeEq_or_mem_CV
      U S K r hfaith P hP hblockable hbP hstart hbi

/-- Union-level form for a retained forward edge of any active owner. -/
theorem erasedSelectedRetainedForwardTail_beforeEq_or_mem_CV_or_startingProxy
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {b y : V}
    (hby : (b, y) ∈ erasedSelectedRetainedForwardEdges U S K)
    (hbP : b ∈ P.path.support) :
    GroundingCut.BeforeEq P.path b
        (GroundingCut.blockingPoint L S.cut P) ∨
      b ∈ GroundingCut.CV L S.cut ∨
      ∃ c : ActiveControlRequest U S K, ∃ i : I, ∃ d : L.LV,
        (strongSelectedPath U S K (chosenRequest c.1)).start = .proxy i ∧
          ((LambdaVertex.proxy i : L.LV), d) ∈
            (strongSelectedPath U S K (chosenRequest c.1)).edgeSet ∧
          b ∈ (L.proxyPath i).support := by
  simp only [erasedSelectedRetainedForwardEdges, Set.mem_iUnion] at hby
  obtain ⟨c, hby⟩ := hby
  rcases selectedRetainedForwardTail_beforeEq_or_mem_CV_or_startingProxy
      U S K (chosenRequest c.1) P hP hblockable hby hbP with
      horder | hbCV | ⟨i, d, hstart, hid, hbi⟩
  · exact Or.inl horder
  · exact Or.inr (Or.inl hbCV)
  · exact Or.inr (Or.inr ⟨c, i, d, hstart, hid, hbi⟩)

/-- Faithful union-level form: every retained forward departure from a
blockable fragment occurs weakly before its blocking point or at an old cut
vertex. -/
theorem erasedSelectedRetainedForwardTail_beforeEq_or_mem_CV
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {b y : V}
    (hby : (b, y) ∈ erasedSelectedRetainedForwardEdges U S K)
    (hbP : b ∈ P.path.support) :
    GroundingCut.BeforeEq P.path b
        (GroundingCut.blockingPoint L S.cut P) ∨
      b ∈ GroundingCut.CV L S.cut := by
  simp only [erasedSelectedRetainedForwardEdges, Set.mem_iUnion] at hby
  obtain ⟨c, hby⟩ := hby
  exact selectedRetainedForwardTail_beforeEq_or_mem_CV
    U S K (chosenRequest c.1) hfaith P hP hblockable hby hbP

end GroundingSelectedForwardOrder
end Erdos599
