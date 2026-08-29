/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedSwitchRelation
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Rank separation for decoded Section 8 carriers

The auxiliary recursion makes a later selected path avoid the supports and
the exposed limiting-ladder components of every earlier selected path.  A
collision at the later request gadget itself is deliberately allowed, since
every member of the local request fan ends there.  Consequently decoded
carriers are not literally pairwise disjoint.  This file records the exact
ranked statement: their intersection is contained in the carrier of the
later request gadget.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingErasedCarrierRank

open DirectedPath PopularGroundingBridge PopularAuxiliary.Input
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Every component exposed by an auxiliary path is a genuine member of the
limiting ladder when proxy paths faithfully name limiting-ladder members. -/
theorem exposedLadderPaths_subset_ladder
    {L : PopularAuxiliary.Input Gamma I}
    (hfaith : ProxyPathsFaithful L)
    (p : FinitePath L.lambda.graph) :
    exposedLadderPaths L p ⊆ L.ladder.paths := by
  intro Y hY
  rcases hY with hY | hY
  · exact hY.1
  · cases hstart : p.start with
    | old x => simp [hstart] at hY
    | edge x y => simp [hstart] at hY
    | proxy i =>
        have hYi : Y = L.proxyPath i := by
          simpa [exposedLadderPaths, hstart] using hY
        exact hYi.symm ▸ hfaith.1 i

/-- If a non-proxy gadget of `p` represents an original vertex represented
by `q`, then either that same old gadget already belongs to `q`, or the
gadget lies on a limiting-ladder component exposed by `q`. -/
theorem nonproxy_mem_support_or_metLadderTrace_of_carrier_overlap
    {L : PopularAuxiliary.Input Gamma I}
    (hfaith : ProxyPathsFaithful L)
    (q p : FinitePath L.lambda.graph)
    (hqstart : q.start ∈ L.lambda.source)
    (hpstart : p.start ∈ L.lambda.source)
    {a : L.LV} (ha : a ∈ p.support)
    (ha_nonproxy : ∀ i, a ≠ .proxy i)
    {x : V} (hxa : x ∈ L.gadgetCarrier a)
    (hxq : x ∈ L.decodedVertexCarrier q) :
    a ∈ q.support ∨ a ∈ metLadderTrace L q := by
  cases a with
  | old y =>
      have hxy : x = y := by simpa [gadgetCarrier] using hxa
      rcases L.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
          q hqstart hxq with hxold | ⟨Y, hYexposed, hxY⟩
      · exact Or.inl (hxy ▸ hxold)
      · exact Or.inr ((mem_metLadderTrace_iff L q (.old y)).2
          ⟨Y, hYexposed, Or.inl ⟨y, hxy ▸ hxY, rfl⟩⟩)
  | edge y z =>
      have hyz : (y, z) ∈ L.familyEdges :=
        L.edgeNode_mem_familyEdges_of_start_in_source p hpstart ha
      change ∃ Y ∈ L.ladder.paths, (y, z) ∈ Y.edgeSet at hyz
      obtain ⟨Z, hZL, hyzZ⟩ := hyz
      have hxEnds : x = y ∨ x = z := by
        simpa [gadgetCarrier, eq_comm] using hxa
      have hxZ : x ∈ Z.support := hxEnds.elim
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hyzZ).1)
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hyzZ).2)
      have hZexposed : Z ∈ exposedLadderPaths L q := by
        rcases L.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
            q hqstart hxq with hxold | ⟨Y, hYexposed, hxY⟩
        · left
          exact ⟨hZL, .old x, hxold, Or.inl ⟨x, hxZ, rfl⟩⟩
        · have hYL : Y ∈ L.ladder.paths :=
            exposedLadderPaths_subset_ladder hfaith q hYexposed
          have hZY : Z = Y :=
            Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
              hZL hYL hxZ hxY
          exact hZY ▸ hYexposed
      exact Or.inr ((mem_metLadderTrace_iff L q (.edge y z)).2
        ⟨Z, hZexposed, Or.inr ⟨(y, z), hyzZ, rfl⟩⟩)
  | proxy i => exact False.elim (ha_nonproxy i rfl)

/-- A proxy gadget whose represented carrier meets the decoded carrier of
`q` supplies a literal old-gadget witness common to its starting proxy trace
and the complete ladder trace exposed by `q`. -/
theorem exists_old_mem_metLadderTrace_and_startingProxyTrace
    {L : PopularAuxiliary.Input Gamma I}
    (hfaith : ProxyPathsFaithful L)
    (q p : FinitePath L.lambda.graph)
    (hqstart : q.start ∈ L.lambda.source)
    (hpstart : p.start ∈ L.lambda.source)
    (i : I) (hi : LambdaVertex.proxy i ∈ p.support)
    {x : V} (hxi : x ∈ L.gadgetCarrier (.proxy i))
    (hxq : x ∈ L.decodedVertexCarrier q) :
    LambdaVertex.old x ∈ metLadderTrace L q ∧
      LambdaVertex.old x ∈ startingProxyTrace L p := by
  have hpstarti : p.start = LambdaVertex.proxy i :=
    L.proxy_mem_support_eq_start p hpstart hi
  have hxi' : x ∈ (L.proxyPath i).support := by
    simpa [gadgetCarrier] using hxi
  have hproxyExposed : L.proxyPath i ∈ exposedLadderPaths L q := by
    rcases L.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
        q hqstart hxq with hxold | ⟨Y, hYexposed, hxY⟩
    · left
      exact ⟨hfaith.1 i, .old x, hxold, Or.inl ⟨x, hxi', rfl⟩⟩
    · have hYL : Y ∈ L.ladder.paths :=
          exposedLadderPaths_subset_ladder hfaith q hYexposed
      have hEq : L.proxyPath i = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
          (hfaith.1 i) hYL hxi' hxY
      exact hEq ▸ hYexposed
  constructor
  · exact (mem_metLadderTrace_iff L q (.old x)).2
      ⟨L.proxyPath i, hproxyExposed, Or.inl ⟨x, hxi', rfl⟩⟩
  · simp [startingProxyTrace, hpstarti, PopularSwitching.ladderTrace, hxi']

/-- Rank-ordered decoded carriers can overlap only in the gadget at which
the later request terminates. -/
theorem strongSelectedPath_decodedVertexCarrier_inter_subset_apex
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s) :
    L.decodedVertexCarrier (strongSelectedPath U S K s) ∩
        L.decodedVertexCarrier (strongSelectedPath U S K r) ⊆
      L.gadgetCarrier (requestAuxVertex s) := by
  let p := strongSelectedPath U S K s
  let q := strongSelectedPath U S K r
  have hpFan : p ∈
      (GroundingControlledAssembly.controlledRequestFan S K s).paths :=
    strongSelectedPath_mem_controlledRequestFan U S K s
  have hpstart : p.start ∈ L.lambda.source :=
    (GroundingControlledAssembly.controlledRequestFan S K s).starts_in_source hpFan
  have hqstart : q.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
  have hfresh := (strongSelectedPath_spec U S K s).2.2
    (GroundingAssembly.requestRank U S r) hrs q
      (strongSelectedPath_spec U S K r).1
  intro x hx
  by_contra hxapex
  rcases hx with ⟨hxp, hxq⟩
  simp only [PopularAuxiliary.Input.decodedVertexCarrier,
    Set.mem_iUnion] at hxp
  obtain ⟨a, ha, hxa⟩ := hxp
  have ha_ne : a ≠ requestAuxVertex s := by
    intro has
    exact hxapex (has ▸ hxa)
  cases a with
  | old y =>
      have hnonproxy : ∀ i : I,
          (LambdaVertex.old y : L.LV) ≠ LambdaVertex.proxy i :=
        fun _ h ↦ by cases h
      rcases nonproxy_mem_support_or_metLadderTrace_of_carrier_overlap
          hfaith q p hqstart hpstart ha hnonproxy hxa hxq with hsupport | htrace
      · exact Set.disjoint_left.1 hfresh.1 ha hsupport
      · apply hfresh.2.1
        exact ⟨hpFan, .old y, ⟨htrace, by simpa using ha_ne⟩, ha⟩
  | edge y z =>
      have hnonproxy : ∀ i : I,
          (LambdaVertex.edge y z : L.LV) ≠ LambdaVertex.proxy i :=
        fun _ h ↦ by cases h
      rcases nonproxy_mem_support_or_metLadderTrace_of_carrier_overlap
          hfaith q p hqstart hpstart ha hnonproxy hxa hxq with hsupport | htrace
      · exact Set.disjoint_left.1 hfresh.1 ha hsupport
      · apply hfresh.2.1
        exact ⟨hpFan, .edge y z, ⟨htrace, by simpa using ha_ne⟩, ha⟩
  | proxy i =>
      have hcommon := exists_old_mem_metLadderTrace_and_startingProxyTrace
        hfaith q p hqstart hpstart i ha hxa hxq
      have hold_ne : LambdaVertex.old x ≠ requestAuxVertex s := by
        intro heq
        apply hxapex
        rw [← heq]
        simp [gadgetCarrier]
      apply hfresh.2.2
      rw [certifiedProxyComponentCollidingPaths, dif_pos hfaith]
      exact ⟨hpFan, .old x, ⟨hcommon.1, by simpa using hold_ne⟩, hcommon.2⟩

/-- The concrete endpoint of a selected request belongs to the decoded
carrier of its auxiliary path. -/
theorem requestExit_mem_strongSelectedPath_decodedVertexCarrier
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    requestExit r ∈
      L.decodedVertexCarrier (strongSelectedPath U S K r) := by
  have hapex : requestAuxVertex r ∈
      (strongSelectedPath U S K r).support := by
    rw [← strongSelectedPath_finish U S K r]
    exact (strongSelectedPath U S K r).finish_mem_support
  apply L.gadgetCarrier_subset_decodedVertexCarrier
    (strongSelectedPath U S K r) hapex
  exact L.mem_gadgetCarrier_of_gadgetEntry
    (gadgetEntry_requestAuxVertex r)

/-- The selected request exit belongs to the exact decoded-route carrier:
it is the entry vertex of the terminal request gadget.  This remains true
when the compressed route is trivial. -/
theorem requestExit_mem_strongSelectedPath_decodedRouteIncidentCarrier
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    requestExit r ∈
      L.decodedRouteIncidentCarrier (strongSelectedPath U S K r) := by
  right
  refine ⟨requestAuxVertex r, ?_, gadgetEntry_requestAuxVertex r⟩
  rw [← strongSelectedPath_finish U S K r]
  exact (strongSelectedPath U S K r).finish_mem_support

/-- Every vertex used by the compressed erased route belongs to the
decoded carrier of the auxiliary path from which that route was decoded. -/
theorem selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (selectedErasedCompression U S K r).path.vertexSet ⊆
      L.decodedVertexCarrier (strongSelectedPath U S K r) := by
  let E := selectedErasedCompression U S K r
  intro x hx
  change x ∈ E.path.vertexSet at hx
  cases hpath : E.path with
  | trivial v =>
      have hxv : x = v := by simpa [hpath] using hx
      have hvexit : v = requestExit r := by
        have hterminal := E.terminal_eq
        rw [hpath] at hterminal
        exact Option.some.inj hterminal
      rw [hxv, hvexit]
      exact requestExit_mem_strongSelectedPath_decodedVertexCarrier U S K r
  | finite Q =>
      rw [hpath] at hx
      change x ∈ Q.vertexSet at hx
      have hxQ : x ∈ Q.vertexSet := hx
      simp only [Alternating.FiniteTrace.vertexSet, Set.mem_iUnion] at hxQ
      obtain ⟨i, hxi⟩ := hxQ
      by_cases hxfinish : x = (Q.link i).path.finish
      · have hxstart : x ≠ (Q.link i).path.start := by
          rw [hxfinish]
          exact (Q.link i).nontrivial.symm
        obtain ⟨y, hyx⟩ :=
          Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            (Q.link i).path hxi hxstart
        have hyxE : (y, x) ∈ E.path.edgeSet := by
          rw [hpath]
          exact Set.mem_iUnion.2 ⟨i, hyx⟩
        exact (selectedErasedRouteEdge_endpoints_mem U S K r
          (by simpa [E] using hyxE)).2
      · obtain ⟨y, hxy⟩ :=
          Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            (Q.link i).path hxi hxfinish
        have hxyE : (x, y) ∈ E.path.edgeSet := by
          rw [hpath]
          exact Set.mem_iUnion.2 ⟨i, hxy⟩
        exact (selectedErasedRouteEdge_endpoints_mem U S K r
          (by simpa [E] using hxyE)).1
  | infinite Q =>
      have hterminal := E.terminal_eq
      rw [hpath] at hterminal
      simp at hterminal

/-- Rank-ordered compressed erased routes can meet only inside the later
request's terminal gadget carrier. -/
theorem selectedErasedCompression_vertexSet_inter_subset_apex
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s) :
    (selectedErasedCompression U S K s).path.vertexSet ∩
        (selectedErasedCompression U S K r).path.vertexSet ⊆
      L.gadgetCarrier (requestAuxVertex s) := by
  intro x hx
  apply strongSelectedPath_decodedVertexCarrier_inter_subset_apex
    U S K hfaith r s hrs
  exact ⟨selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K s hx.1,
    selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K r hx.2⟩

/-- Deleting each request's own terminal gadget carrier makes the actual
compressed erased-route vertex sets pairwise disjoint. -/
theorem selectedErasedCompression_trimmedVertexSets_pairwiseDisjoint
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L) :
    Set.PairwiseDisjoint Set.univ (fun r : Request L S.cut ↦
      (selectedErasedCompression U S K r).path.vertexSet \
        L.gadgetCarrier (requestAuxVertex r)) := by
  intro r _hr s _hs hrs
  change Disjoint
    ((selectedErasedCompression U S K r).path.vertexSet \
      L.gadgetCarrier (requestAuxVertex r))
    ((selectedErasedCompression U S K s).path.vertexSet \
      L.gadgetCarrier (requestAuxVertex s))
  rw [Set.disjoint_left]
  intro x hxr hxs
  rcases lt_trichotomy (GroundingAssembly.requestRank U S r)
      (GroundingAssembly.requestRank U S s) with hrslt | hrseq | hsrlt
  · exact hxs.2
      (selectedErasedCompression_vertexSet_inter_subset_apex
        U S K hfaith r s hrslt ⟨hxs.1, hxr.1⟩)
  · exact False.elim
      (hrs ((GroundingAssembly.requestRank U S).injective hrseq))
  · exact hxr.2
      (selectedErasedCompression_vertexSet_inter_subset_apex
        U S K hfaith s r hsrlt ⟨hxr.1, hxs.1⟩)

/-- After deleting each request's own terminal gadget carrier, the decoded
carriers of distinct selected paths are genuinely disjoint. -/
theorem strongSelectedPath_trimmedDecodedCarriers_pairwiseDisjoint
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L) :
    Set.PairwiseDisjoint Set.univ (fun r : Request L S.cut ↦
      L.decodedVertexCarrier (strongSelectedPath U S K r) \
        L.gadgetCarrier (requestAuxVertex r)) := by
  intro r _hr s _hs hrs
  change Disjoint
    (L.decodedVertexCarrier (strongSelectedPath U S K r) \
      L.gadgetCarrier (requestAuxVertex r))
    (L.decodedVertexCarrier (strongSelectedPath U S K s) \
      L.gadgetCarrier (requestAuxVertex s))
  rw [Set.disjoint_left]
  intro x hxr hxs
  rcases lt_trichotomy (GroundingAssembly.requestRank U S r)
      (GroundingAssembly.requestRank U S s) with hrslt | hrseq | hsrlt
  · exact hxs.2
      (strongSelectedPath_decodedVertexCarrier_inter_subset_apex
        U S K hfaith r s hrslt ⟨hxs.1, hxr.1⟩)
  · exact False.elim
      (hrs ((GroundingAssembly.requestRank U S).injective hrseq))
  · exact hxr.2
      (strongSelectedPath_decodedVertexCarrier_inter_subset_apex
        U S K hfaith s r hsrlt ⟨hxr.1, hxs.1⟩)

end GroundingErasedCarrierRank
end Erdos599
