/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualSelection

/-!
# Terminal-cut incidence for the split equal switch

The proof is uniform over the enlarged split auxiliary.  Every finite source
and every proxy still represents a recorded inessential limiting-ladder
component, so no such source carrier can meet the essential terminal cut.
Consequently neither a retained ladder edge nor a canonical inserted forward
edge leaves that cut.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingEqualActiveSelection
open GroundingRootedReachabilityWarp
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev SplitTerminalInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- The endpoints of an edge of a directed simple path or ray are distinct. -/
private theorem pathEdge_endpoints_ne
    {P : Gamma.DPath} {x y : V} (hxy : (x, y) ∈ P.edgeSet) : x ≠ y := by
  cases P with
  | inl p =>
      obtain ⟨n, hn, hnx, hny⟩ :=
        _root_.Erdos599.DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet
          p.walk hxy
      intro hxyEq
      have hn0 : n < p.walk.support.length := by omega
      have hget :
          p.walk.support[n]'hn0 = p.walk.support[n + 1]'hn := by
        exact hnx.trans (hxyEq.trans hny.symm)
      have hindex : (⟨n, hn0⟩ : Fin p.walk.support.length) =
          ⟨n + 1, hn⟩ := p.isPath.get_inj_iff.mp hget
      have hval := congrArg Fin.val hindex
      exact Nat.ne_of_lt (Nat.lt_succ_self n) hval
  | inr r =>
      obtain ⟨n, hn⟩ := hxy
      intro hxyEq
      have hvalue : r n = r (n + 1) :=
        (congrArg Prod.fst hn).symm.trans
          (hxyEq.trans (congrArg Prod.snd hn))
      have hindex := r.injective hvalue
      omega

/-- A recorded path belongs to the inessential part of the limiting warp. -/
private theorem recorded_mem_limitWarp_inessential
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hp : L.chosen a = some p) :
    p ∈ Gamma.inessentialPaths L.limitWarp := by
  apply L.recorded_mem_inessential hlegal.recordedPathsPersist hp
  change a.1 + 1 ≤ kappa.ord
  exact (Order.add_one_le_iff).2 a.2

/-- A finite terminal of a concrete warp has no outgoing edge in the union
of its member edge sets. -/
private theorem noOutgoing_familyEdges_of_mem_terminalFrontier
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {x : V} (hx : x ∈ Gamma.terminalFrontier W) :
    ¬ ∃ y, (x, y) ∈ Alternating.familyEdges W := by
  rintro ⟨y, hxy⟩
  obtain ⟨p, hpW, hpterm⟩ := hx
  simp only [Alternating.familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨q, hqW, hxyq⟩ := hxy
  have hxp : x ∈ p.support := Gamma.terminal_mem_support hpterm
  have hpq : p = q :=
    _root_.Erdos599.Alternating.DWeb.IsWarp.eq_of_mem_support
      hW hpW hqW hxp
      (q.edgeSet_subset_support_prod hxyq).1
  subst q
  rcases p with p | r
  · have hpfinish : p.finish = x := by
      simpa [DWeb.terminal?, DirectedPath.Path.terminal?] using hpterm
    exact _root_.Erdos599.Alternating.FinitePath.no_outgoing_edge_at_finish
      p y (hpfinish ▸ hxyq)
  · simp [DWeb.terminal?, DirectedPath.Path.terminal?] at hpterm

/-- The essential terminal cut is disjoint from every grounded finite
auxiliary source. -/
theorem splitTerminalCut_not_mem_finiteSource
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    {b : V} (hb : b ∈ (SplitTerminalInput L hL).terminalCut) :
    b ∉ (SplitTerminalInput L hL).finiteSource := by
  rintro ⟨a, ha, p, hchosen, hpterm⟩
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp :=
    recorded_mem_limitWarp_inessential L hL.legal hchosen
  exact splitTerminalCut_not_mem_support_of_inessential L hL hb hpInessential
    (Gamma.terminal_mem_support hpterm)

/-- The essential terminal cut is disjoint from the carrier of every
grounded proxy path. -/
theorem splitTerminalCut_not_mem_proxyPath
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    {b : V} (hb : b ∈ (SplitTerminalInput L hL).terminalCut)
    (i : L.splitInfiniteRecords) :
    b ∉ ((SplitTerminalInput L hL).proxyPath i).support := by
  obtain ⟨a, ha, hchosen⟩ := i.2
  have hiInessential : i.1 ∈ Gamma.inessentialPaths L.limitWarp :=
    recorded_mem_limitWarp_inessential L hL.legal hchosen
  exact splitTerminalCut_not_mem_support_of_inessential L hL hb hiInessential

/-- No limiting-ladder edge leaves the essential terminal cut. -/
theorem splitTerminalCut_noOutgoing_familyEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    {b : V} (hb : b ∈ (SplitTerminalInput L hL).terminalCut) :
    ¬ Alternating.HasOutgoing (SplitTerminalInput L hL).familyEdges b := by
  rintro ⟨y, hby⟩
  change b ∈ Gamma.terminalFrontier
    (Gamma.essentialWarpPart L.limitWarp) at hb
  obtain ⟨p, hpEssential, hpterm⟩ := hb
  have hbFull : b ∈ Gamma.terminalFrontier L.limitWarp :=
    ⟨p, hpEssential.1, hpterm⟩
  have hlimitWarp : Gamma.IsWarp L.limitWarp := by
    simpa [KappaLadder.limitWarp] using
      hL.legal.warpStages (Ladder.finalStage kappa)
  apply noOutgoing_familyEdges_of_mem_terminalFrontier hlimitWarp hbFull
  refine ⟨y, ?_⟩
  simpa [SplitTerminalInput, KappaLadder.splitPopularAuxiliaryInput,
    PopularAuxiliary.Input.familyEdges, Alternating.familyEdges] using hby

/-- Exact source-gadget provenance of the tail of a canonical erased
forward edge. -/
theorem splitCanonicalErasedForwardTail_old_or_edge_or_startingProxy
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitTerminalInput L hL).lambda (SplitTerminalInput L hL).lambda.target)
    (p : WarpPath Q) {b y : V}
    (hby : (b, y) ∈
      (canonicalErasedRoute (SplitTerminalInput L hL) Q p).directionEdges .forward) :
    (∃ d : (SplitTerminalInput L hL).LV,
        ((PopularAuxiliary.Input.LambdaVertex.old b :
          (SplitTerminalInput L hL).LV), d) ∈ p.1.edgeSet ∧
        (SplitTerminalInput L hL).chosenConnector?
          (.old b) d = some (b, y)) ∨
      (∃ v : V, ∃ d : (SplitTerminalInput L hL).LV,
        (PopularAuxiliary.Input.LambdaVertex.edge b v, d) ∈ p.1.edgeSet) ∨
      ∃ i : L.splitInfiniteRecords, ∃ d : (SplitTerminalInput L hL).LV,
        p.1.start = .proxy i ∧
          ((PopularAuxiliary.Input.LambdaVertex.proxy i :
            (SplitTerminalInput L hL).LV), d) ∈ p.1.edgeSet ∧
          b ∈ ((SplitTerminalInput L hL).proxyPath i).support := by
  let I := SplitTerminalInput L hL
  let T := I.decodeFinitePath p.1 (Q.starts_in_source p.2)
    (Q.ends_in_target p.2)
  let E := T.runs.erasedSignedRoute
  have hby' : (b, y) ∈
      (E.compressionOfValid
        (fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs))).path.directionEdges
          .forward := by
    simpa [canonicalErasedRoute, I, T, E,
      PopularAuxiliary.Input.MicroTrace.erasedCompression] using hby
  have hsigned :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      (fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs)) .forward hby'
  obtain ⟨s, hsE, hsForward, hsEdge⟩ := hsigned
  have hraw : (b, y) ∈
      PopularAuxiliary.Input.directedSignedEdgeSet .forward
        (I.decodeWalkSteps p.1.walk) := by
    refine ⟨s, ?_, hsForward, hsEdge⟩
    simpa [I, T] using E.steps_sublist.subset hsE
  rw [I.forwardEdges_decodeWalkSteps p.1.walk] at hraw
  obtain ⟨a, d, had, hchosen⟩ := hraw
  have hconnector := I.chosenConnector?_eq_some hchosen
  have haSupport : a ∈ p.1.support :=
    (p.1.edgeSet_subset_support_prod had).1
  rcases hconnector.1 with hExit | ⟨i, hai, hbProxy⟩
  · cases a with
    | old z =>
        have hzb : z = b := Option.some.inj hExit
        subst z
        exact Or.inl ⟨d, had, hchosen⟩
    | edge u v =>
        have hub : u = b := Option.some.inj hExit
        subst u
        exact Or.inr (Or.inl ⟨v, d, had⟩)
    | proxy i => simp at hExit
  · subst a
    have hstart : p.1.start = .proxy i :=
      I.proxy_mem_support_eq_start p.1 (Q.starts_in_source p.2) haSupport
    exact Or.inr (Or.inr ⟨i, d, hstart, had, hbProxy⟩)

/-- No canonical erased forward edge leaves the essential terminal cut. -/
theorem splitTerminalCut_noOutgoing_canonicalErasedForwardEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitTerminalInput L hL).lambda (SplitTerminalInput L hL).lambda.target)
    {b : V} (hb : b ∈ (SplitTerminalInput L hL).terminalCut) :
    ¬ Alternating.HasOutgoing
      (canonicalErasedForwardEdges (SplitTerminalInput L hL) Q) b := by
  rintro ⟨y, hby⟩
  simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hby
  obtain ⟨p, hby⟩ := hby
  have hbyNe : b ≠ y := by
    have hby' := hby
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at hby'
    obtain ⟨l, _hl, _hd, hbyl⟩ := hby'
    exact pathEdge_endpoints_ne
      (P := (Sum.inl l.path : Gamma.DPath)) hbyl
  rcases splitCanonicalErasedForwardTail_old_or_edge_or_startingProxy
      L hL Q p hby with hold | hedge | hproxy
  · obtain ⟨d, hbd, hchosen⟩ := hold
    have hadj := p.1.edgeSet_subset_adj hbd
    cases d with
    | old z =>
        have hbClass := ((SplitTerminalInput L hL).lambda_adj_old_old b z).1 hadj
        rcases hbClass.1 with hbOff | hbFinite
        · exact hbOff.2 (by
            change b ∈ Gamma.vertexSet L.limitWarp
            change b ∈ Gamma.terminalFrontier
              (Gamma.essentialWarpPart L.limitWarp) at hb
            obtain ⟨q, hq, hqb⟩ := hb
            exact ⟨q, hq.1, Gamma.terminal_mem_support hqb⟩)
        · exact splitTerminalCut_not_mem_finiteSource L hL hb hbFinite
    | edge u v =>
        have hbClass := ((SplitTerminalInput L hL).lambda_adj_old_edge b u v).1 hadj
        rcases hbClass.2 with hbeq | hbClass
        · have hconnector :=
            (SplitTerminalInput L hL).chosenConnector?_eq_some hchosen
          have hyv : y = v := by
            have hvy : v = y := by
              simpa only [PopularAuxiliary.Input.gadgetEntry_edge,
                Option.some.injEq] using hconnector.2.1
            exact hvy.symm
          exact hbyNe (hbeq.trans hyv.symm)
        · rcases hbClass.1 with hbOff | hbFinite
          · exact hbOff.2 (by
              change b ∈ Gamma.vertexSet L.limitWarp
              change b ∈ Gamma.terminalFrontier
                (Gamma.essentialWarpPart L.limitWarp) at hb
              obtain ⟨q, hq, hqb⟩ := hb
              exact ⟨q, hq.1, Gamma.terminal_mem_support hqb⟩)
          · exact splitTerminalCut_not_mem_finiteSource L hL hb hbFinite
    | proxy i => simp at hadj
  · obtain ⟨v, d, hbvd⟩ := hedge
    have hadj := p.1.edgeSet_subset_adj hbvd
    cases d with
    | old z =>
        exact splitTerminalCut_noOutgoing_familyEdges L hL hb
          ⟨v, (((SplitTerminalInput L hL).lambda_adj_edge_old b v z).1 hadj).1⟩
    | edge w z =>
        exact splitTerminalCut_noOutgoing_familyEdges L hL hb
          ⟨v, (((SplitTerminalInput L hL).lambda_adj_edge_edge b v w z).1 hadj).1⟩
    | proxy i => simp at hadj
  · obtain ⟨i, d, _hstart, _hid, hbi⟩ := hproxy
    exact splitTerminalCut_not_mem_proxyPath L hL hb i hbi

/-- The complete collision-repaired equal-family relation has no edge
leaving the essential terminal cut. -/
theorem splitTerminalCut_noOutgoing_canonicalErasedRepairedEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitTerminalInput L hL).lambda (SplitTerminalInput L hL).lambda.target)
    {b : V} (hb : b ∈ (SplitTerminalInput L hL).terminalCut) :
    ¬ Alternating.HasOutgoing
      (canonicalErasedRepairedEdges (SplitTerminalInput L hL) Q) b := by
  rintro ⟨y, hby⟩
  rcases hby with hbase | hforward
  · exact splitTerminalCut_noOutgoing_familyEdges L hL hb ⟨y, hbase.1.1⟩
  · exact splitTerminalCut_noOutgoing_canonicalErasedForwardEdges
      L hL Q hb ⟨y, hforward⟩

/-- Therefore the essential terminal cut is automatically a reachability
antichain for the collision-repaired equal-family relation. -/
theorem splitTerminalCut_isReachabilityAntichain_canonicalErasedRepairedEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitTerminalInput L hL).lambda (SplitTerminalInput L hL).lambda.target) :
    IsReachabilityAntichain
      (canonicalErasedRepairedEdges (SplitTerminalInput L hL) Q)
      (SplitTerminalInput L hL).terminalCut := by
  intro b hb c _hc hbc
  rcases hbc.cases_head with hcb | ⟨x, hbx, _hxc⟩
  · exact hcb
  · exact False.elim
      (splitTerminalCut_noOutgoing_canonicalErasedRepairedEdges
        L hL Q hb ⟨x, hbx⟩)


end KappaLadder
end DWeb
end Erdos599

