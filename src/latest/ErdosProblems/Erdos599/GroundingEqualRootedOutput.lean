/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualActiveSelection
import ErdosProblems.Erdos599.GroundingRootedReachabilityHindrance

/-!
# Rooted output of the collision-repaired equal-stage relation

Carrier-disjoint thinning makes the union of the canonical decoded routes
locally sound.  The relation in `GroundingEqualActiveSelection` toggles every
selected backward edge, deletes residual head/tail conflicts, and inserts the
selected forward edges.  This file connects that concrete relation to the
finite rooted-output compiler.

The structure below names the genuinely ambient part of the construction:
the essential terminal cut must be an antichain and must be reachable from a
set of permitted original roots which omits one original source.  Once those
facts are available, no global relation decomposition, reverse-ray exclusion,
or finite-character assumption is needed.
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

private abbrev EqualInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :=
  L.popularAuxiliaryInput hL.legal

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
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
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

/-- A vertex of the essential terminal cut cannot lie on an inessential
component of the limiting ladder warp. -/
theorem terminalCut_not_mem_support_of_inessential
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut)
    {p : Gamma.DPath} (hp : p ∈ Gamma.inessentialPaths L.limitWarp) :
    b ∉ p.support := by
  intro hbp
  change b ∈ Gamma.terminalFrontier
    (Gamma.essentialWarpPart L.limitWarp) at hb
  obtain ⟨q, hqEssential, hqb⟩ := hb
  have hqbSupport : b ∈ q.support := Gamma.terminal_mem_support hqb
  by_cases hpq : p = q
  · subst q
    exact hp.2 hqEssential
  · exact Set.disjoint_left.1
      (hL.legal.warpStages (Ladder.finalStage kappa)
        hp.1 hqEssential.1 hpq) hbp hqbSupport

/-- The essential terminal cut is disjoint from every grounded finite
auxiliary source. -/
theorem terminalCut_not_mem_finiteSource
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut) :
    b ∉ (EqualInput L hL).finiteSource := by
  rintro ⟨a, ha, p, hchosen, hpterm⟩
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp :=
    recorded_mem_limitWarp_inessential L hL.legal hchosen
  exact terminalCut_not_mem_support_of_inessential L hL hb hpInessential
    (Gamma.terminal_mem_support hpterm)

/-- The essential terminal cut is disjoint from the carrier of every
grounded proxy path. -/
theorem terminalCut_not_mem_proxyPath
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut)
    (i : L.groundedInfiniteRecords) :
    b ∉ ((EqualInput L hL).proxyPath i).support := by
  obtain ⟨a, ha, hchosen⟩ := i.2
  have hiInessential : i.1 ∈ Gamma.inessentialPaths L.limitWarp :=
    recorded_mem_limitWarp_inessential L hL.legal hchosen
  exact terminalCut_not_mem_support_of_inessential L hL hb hiInessential

/-- No limiting-ladder edge leaves the essential terminal cut. -/
theorem terminalCut_noOutgoing_familyEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut) :
    ¬ Alternating.HasOutgoing (EqualInput L hL).familyEdges b := by
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
  simpa [EqualInput, KappaLadder.popularAuxiliaryInput,
    PopularAuxiliary.Input.familyEdges, Alternating.familyEdges] using hby

/-- Exact source-gadget provenance of the tail of a canonical erased
forward edge. -/
theorem canonicalErasedForwardTail_old_or_edge_or_startingProxy
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (p : WarpPath Q) {b y : V}
    (hby : (b, y) ∈
      (canonicalErasedRoute (EqualInput L hL) Q p).directionEdges .forward) :
    (∃ d : (EqualInput L hL).LV,
        ((PopularAuxiliary.Input.LambdaVertex.old b :
          (EqualInput L hL).LV), d) ∈ p.1.edgeSet ∧
        (EqualInput L hL).chosenConnector?
          (.old b) d = some (b, y)) ∨
      (∃ v : V, ∃ d : (EqualInput L hL).LV,
        (PopularAuxiliary.Input.LambdaVertex.edge b v, d) ∈ p.1.edgeSet) ∨
      ∃ i : L.groundedInfiniteRecords, ∃ d : (EqualInput L hL).LV,
        p.1.start = .proxy i ∧
          ((PopularAuxiliary.Input.LambdaVertex.proxy i :
            (EqualInput L hL).LV), d) ∈ p.1.edgeSet ∧
          b ∈ ((EqualInput L hL).proxyPath i).support := by
  let I := EqualInput L hL
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
theorem terminalCut_noOutgoing_canonicalErasedForwardEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut) :
    ¬ Alternating.HasOutgoing
      (canonicalErasedForwardEdges (EqualInput L hL) Q) b := by
  rintro ⟨y, hby⟩
  simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hby
  obtain ⟨p, hby⟩ := hby
  have hbyNe : b ≠ y := by
    have hby' := hby
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at hby'
    obtain ⟨l, _hl, _hd, hbyl⟩ := hby'
    exact pathEdge_endpoints_ne
      (P := (Sum.inl l.path : Gamma.DPath)) hbyl
  rcases canonicalErasedForwardTail_old_or_edge_or_startingProxy
      L hL Q p hby with hold | hedge | hproxy
  · obtain ⟨d, hbd, hchosen⟩ := hold
    have hadj := p.1.edgeSet_subset_adj hbd
    cases d with
    | old z =>
        have hbClass := ((EqualInput L hL).lambda_adj_old_old b z).1 hadj
        rcases hbClass.1 with hbOff | hbFinite
        · exact hbOff.2 (by
            change b ∈ Gamma.vertexSet L.limitWarp
            change b ∈ Gamma.terminalFrontier
              (Gamma.essentialWarpPart L.limitWarp) at hb
            obtain ⟨q, hq, hqb⟩ := hb
            exact ⟨q, hq.1, Gamma.terminal_mem_support hqb⟩)
        · exact terminalCut_not_mem_finiteSource L hL hb hbFinite
    | edge u v =>
        have hbClass := ((EqualInput L hL).lambda_adj_old_edge b u v).1 hadj
        rcases hbClass.2 with hbeq | hbClass
        · have hconnector :=
            (EqualInput L hL).chosenConnector?_eq_some hchosen
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
          · exact terminalCut_not_mem_finiteSource L hL hb hbFinite
    | proxy i => simp at hadj
  · obtain ⟨v, d, hbvd⟩ := hedge
    have hadj := p.1.edgeSet_subset_adj hbvd
    cases d with
    | old z =>
        exact terminalCut_noOutgoing_familyEdges L hL hb
          ⟨v, (((EqualInput L hL).lambda_adj_edge_old b v z).1 hadj).1⟩
    | edge w z =>
        exact terminalCut_noOutgoing_familyEdges L hL hb
          ⟨v, (((EqualInput L hL).lambda_adj_edge_edge b v w z).1 hadj).1⟩
    | proxy i => simp at hadj
  · obtain ⟨i, d, _hstart, _hid, hbi⟩ := hproxy
    exact terminalCut_not_mem_proxyPath L hL hb i hbi

/-- The complete collision-repaired equal-family relation has no edge
leaving the essential terminal cut. -/
theorem terminalCut_noOutgoing_canonicalErasedRepairedEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut) :
    ¬ Alternating.HasOutgoing
      (canonicalErasedRepairedEdges (EqualInput L hL) Q) b := by
  rintro ⟨y, hby⟩
  rcases hby with hbase | hforward
  · exact terminalCut_noOutgoing_familyEdges L hL hb ⟨y, hbase.1.1⟩
  · exact terminalCut_noOutgoing_canonicalErasedForwardEdges
      L hL Q hb ⟨y, hforward⟩

/-- Therefore the essential terminal cut is automatically a reachability
antichain for the collision-repaired equal-family relation. -/
theorem terminalCut_isReachabilityAntichain_canonicalErasedRepairedEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target) :
    IsReachabilityAntichain
      (canonicalErasedRepairedEdges (EqualInput L hL) Q)
      (EqualInput L hL).terminalCut := by
  intro b hb c _hc hbc
  rcases hbc.cases_head with hcb | ⟨x, hbx, _hxc⟩
  · exact hcb
  · exact False.elim
      (terminalCut_noOutgoing_canonicalErasedRepairedEdges
        L hL Q hb ⟨x, hbx⟩)

/-! ## Reserving one grounded inessential parent -/

/-- The grounded limiting-ladder parent represented by one auxiliary
source path, together with the fact that its full ladder trace is exposed
by that path. -/
structure ReservedGroundedParent
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source) where
  parent : Gamma.DPath
  parent_inessential : parent ∈ Gamma.inessentialPaths L.limitWarp
  parent_groundedRecord : parent ∈ (EqualInput L hL).groundedRecords
  parent_initial_source : parent.initial ∈ Gamma.source
  source_represents :
    (∃ p : FinitePath Gamma.graph,
      parent = .inl p ∧ q.start = .old p.finish) ∨
    (∃ i : L.groundedInfiniteRecords,
      parent = (EqualInput L hL).proxyPath i ∧ q.start = .proxy i)
  parent_exposed : parent ∈
    GroundingSimultaneousDecode.exposedLadderPaths (EqualInput L hL) q

/-- Every auxiliary source in the equal family has a canonical grounded
inessential parent, and the complete trace of that parent lies in the
reserved collision carrier. -/
theorem reservedGroundedParent_nonempty
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source) :
    Nonempty (L.ReservedGroundedParent hL q hqsource) := by
  let I := EqualInput L hL
  rcases I.start_of_mem_lambda_source q hqsource with
      ⟨b, hbFinite, hstart⟩ | ⟨i, hstart⟩
  · let x : L.groundedFiniteTerminalSet := ⟨b, hbFinite⟩
    let x' : L.finiteTerminalSet :=
      ⟨b, L.groundedFiniteTerminalSet_subset_finiteTerminalSet hbFinite⟩
    obtain ⟨_haFinite, parent, hchosen, hterminal⟩ :=
      L.finiteTerminalStage_spec x'
    have hindex : L.finiteTerminalIndex x = L.finiteTerminalStage x' := rfl
    have hground : L.finiteTerminalIndex x ∈ L.phiGround :=
      L.finiteTerminalStage_mem_phiGround hL.legal x
    have hgroundRecord : parent ∈ (EqualInput L hL).groundedRecords := by
      change ∃ a : Ladder.Stage kappa,
        a ∈ L.phiGround ∧ L.chosen a = some parent
      exact ⟨L.finiteTerminalIndex x, hground, by
        simpa only [hindex] using hchosen⟩
    obtain ⟨groundedParent, hparentChosen, hparentSource⟩ := hground
    rw [hindex] at hparentChosen
    rcases parent with p | r
    · have hfinish : p.finish = b := Option.some.inj hterminal
      have hparent : groundedParent = (.inl p : Gamma.DPath) :=
        Option.some.inj (hparentChosen.symm.trans hchosen)
      subst groundedParent
      have hinessential : (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp :=
        recorded_mem_limitWarp_inessential L hL.legal hchosen
      refine ⟨{
        parent := .inl p
        parent_inessential := hinessential
        parent_groundedRecord := hgroundRecord
        parent_initial_source := hparentSource
        source_represents := Or.inl ⟨p, rfl, by
          simpa only [hfinish] using hstart⟩
        parent_exposed := Or.inl ⟨hinessential.1, ?_⟩ }⟩
      refine ⟨.old b, ?_, Or.inl ⟨b, ?_, rfl⟩⟩
      · simpa only [hstart] using q.start_mem_support
      · change b ∈ p.support
        simpa only [hfinish] using p.finish_mem_support
    · change (none : Option V) = some b at hterminal
      cases hterminal
  · have hispec := L.groundedInfiniteStage_spec i
    obtain ⟨parent, hparentChosen, hparentSource⟩ := hispec.1.1
    have hchosen : L.chosen (L.groundedInfiniteStage i) = some i.1 :=
      hispec.2
    have hiparent : i.1 = parent :=
      Option.some.inj (hchosen.symm.trans hparentChosen)
    have hiSource : i.1.initial ∈ Gamma.source := hiparent ▸ hparentSource
    have hiInessential : i.1 ∈ Gamma.inessentialPaths L.limitWarp :=
      L.recorded_mem_limitWarp_inessential hL.legal hchosen
    have hiGroundedRecord : i.1 ∈ (EqualInput L hL).groundedRecords := by
      change ∃ a : Ladder.Stage kappa,
        a ∈ L.phiGround ∧ L.chosen a = some i.1
      exact ⟨L.groundedInfiniteStage i, hispec.1.1, hchosen⟩
    refine ⟨{
      parent := i.1
      parent_inessential := hiInessential
      parent_groundedRecord := hiGroundedRecord
      parent_initial_source := hiSource
      source_represents := Or.inr ⟨i, by
        simp only [EqualInput, KappaLadder.popularAuxiliaryInput,
          KappaLadder.groundedInfinitePath], hstart⟩
      parent_exposed := ?_ }⟩
    right
    simpa [GroundingSimultaneousDecode.exposedLadderPaths, hstart,
      EqualInput, KappaLadder.popularAuxiliaryInput,
      KappaLadder.groundedInfinitePath]

namespace ReservedGroundedParent

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}

/-- Any selected family avoiding the reserved collision carrier has decoded
carriers disjoint from the reserved grounded parent. -/
theorem decodedCarriers_disjoint
    (R : L.ReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q)) :
    ∀ p ∈ Q.paths,
      Disjoint ((EqualInput L hL).decodedVertexCarrier p)
        R.parent.support := by
  intro p hp
  exact decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
    (EqualInput L hL) (L.popularAuxiliary_proxyPathsFaithful hL)
    p q (Q.starts_in_source hp) R.parent_exposed (havoid p hp)

/-- No inserted forward edge is incident with the reserved parent. -/
theorem forwardEdges_endpoints_not_mem
    (R : L.ReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q))
    {e : V × V} (he : e ∈
      canonicalErasedForwardEdges (EqualInput L hL) Q) :
    e.1 ∉ R.parent.support ∧ e.2 ∉ R.parent.support := by
  apply canonicalErasedForwardEdges_endpoints_not_mem
    (EqualInput L hL) Q (R.decodedCarriers_disjoint Q havoid) he

/-- A limiting-ladder edge whose tail lies on the reserved parent remains
on that same parent. -/
theorem familyEdge_head_mem
    (R : L.ReservedGroundedParent hL q hqsource)
    {x y : V} (hx : x ∈ R.parent.support)
    (hxy : (x, y) ∈ (EqualInput L hL).familyEdges) :
    y ∈ R.parent.support := by
  obtain ⟨p, hpLimit, hxyP⟩ := hxy
  have hxP : x ∈ p.support := (p.edgeSet_subset_support_prod hxyP).1
  have hparentP : R.parent = p :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa))
      R.parent_inessential.1 hpLimit hx hxP
  rw [hparentP]
  exact (p.edgeSet_subset_support_prod hxyP).2

/-- The reserved parent is forward closed under the complete repaired
relation.  Inserted edges cannot touch it, while every retained ladder edge
stays on its unique limiting-warp component. -/
theorem repairedEdge_head_mem
    (R : L.ReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q))
    {x y : V} (hx : x ∈ R.parent.support)
    (hxy : (x, y) ∈
      canonicalErasedRepairedEdges (EqualInput L hL) Q) :
    y ∈ R.parent.support := by
  rcases hxy with hbase | hforward
  · exact R.familyEdge_head_mem hx hbase.1.1
  · exact False.elim ((R.forwardEdges_endpoints_not_mem Q havoid hforward).1 hx)

/-- Every vertex reachable from the reserved original source in the
repaired relation remains on its grounded inessential parent. -/
theorem reachable_mem_support
    (R : L.ReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q))
    {x : V}
    (hx : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        canonicalErasedRepairedEdges (EqualInput L hL) Q)
      R.parent.initial x) :
    x ∈ R.parent.support := by
  induction hx with
  | refl => exact R.parent.initial_mem_support
  | tail hxy hyz ih => exact R.repairedEdge_head_mem Q havoid ih hyz

/-- The reserved source cannot reach the essential terminal cut. -/
theorem not_reaches_terminalCut
    (R : L.ReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q))
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut) :
    ¬ Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        canonicalErasedRepairedEdges (EqualInput L hL) Q)
      R.parent.initial b := by
  intro hreach
  exact terminalCut_not_mem_support_of_inessential L hL hb
    R.parent_inessential (R.reachable_mem_support Q havoid hreach)

end ReservedGroundedParent

/-- Ambient rooted geometry for the concrete collision-repaired relation of
a decoded-carrier-disjoint equal subwarp. -/
structure CanonicalEqualRootedOutput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) where
  allowedRoots : Set V
  allowedRoots_subset_source : allowedRoots ⊆ Gamma.source
  terminalCut_rooted : ∀ b ∈
      (L.popularAuxiliaryInput hL.legal).terminalCut,
    ∃ a ∈ allowedRoots, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
        (L.popularAuxiliaryInput hL.legal) Q) a b
  unusedSource : V
  unusedSource_mem : unusedSource ∈ Gamma.source
  unusedSource_not_allowed : unusedSource ∉ allowedRoots

/-- Once every essential terminal is reachable from some original source,
the reserved-parent construction removes one source without losing any of
those witnesses.  Indeed the reserved source cannot reach the cut at all,
so no terminal-rooting witness could have used it. -/
theorem canonicalEqualRootedOutput_of_sourceRooted
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source)
    (R : L.ReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q))
    (hroot : ∀ b ∈ (EqualInput L hL).terminalCut,
      ∃ a ∈ Gamma.source, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          canonicalErasedRepairedEdges (EqualInput L hL) Q) a b) :
    Nonempty (L.CanonicalEqualRootedOutput hL Q) := by
  refine ⟨{
    allowedRoots := Gamma.source \ {R.parent.initial}
    allowedRoots_subset_source := fun _ ha ↦ ha.1
    terminalCut_rooted := ?_
    unusedSource := R.parent.initial
    unusedSource_mem := R.parent_initial_source
    unusedSource_not_allowed := by simp }⟩
  intro b hb
  obtain ⟨a, haSource, hab⟩ := hroot b hb
  have hane : a ≠ R.parent.initial := by
    intro hae
    subst a
    exact R.not_reaches_terminalCut Q havoid hb hab
  exact ⟨a, ⟨haSource, by simpa using hane⟩, hab⟩

namespace CanonicalEqualRootedOutput

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {Q : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- Direct compilation of the equal-stage rooted output into an ordinary
hindrance.  Local adjacency and bi-uniqueness are discharged by the concrete
repaired-relation theorems; the terminal-cut separator is discharged by
ladder legality. -/
theorem exists_hindrance
    (O : L.CanonicalEqualRootedOutput hL Q)
    (hQdisjoint : Q.paths.PairwiseDisjoint
      (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  exact L.exists_hindrance_of_rootedTerminalCut hL
    (canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal) Q)
    O.allowedRoots
    (canonicalErasedRepairedEdges_subset_adj
      (L.popularAuxiliaryInput hL.legal) Q)
    (canonicalErasedRepairedEdges_biUnique
      (L.popularAuxiliaryInput hL.legal) Q hQdisjoint)
    O.allowedRoots_subset_source
    (terminalCut_isReachabilityAntichain_canonicalErasedRepairedEdges
      L hL Q)
    O.terminalCut_rooted O.unusedSource O.unusedSource_mem
    O.unusedSource_not_allowed

end CanonicalEqualRootedOutput

/-- Exact equal-branch compiler with the unused-source issue completely
discharged.  Its only ambient premise is source reachability of the
essential terminal cut in the concrete repaired relation. -/
theorem ReservedGroundedParent.exists_hindrance_of_sourceRooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hQdisjoint : Q.paths.PairwiseDisjoint
      (EqualInput L hL).decodedVertexCarrier)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q))
    (hroot : ∀ b ∈ (EqualInput L hL).terminalCut,
      ∃ a ∈ Gamma.source, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          canonicalErasedRepairedEdges (EqualInput L hL) Q) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  exact (canonicalEqualRootedOutput_of_sourceRooted
    L hL q hqsource R Q havoid hroot).some.exists_hindrance hQdisjoint

/-- Collision-safe reduction of the stationary target-pure equal branch to
the exact remaining rooted terminal-cut geometry.

The callback receives the thinned subwarp together with all four facts
proved by the stationary selection theorem.  Its output mentions only the
concrete repaired relation, not an arbitrary realizing family. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_rootedOutput
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (rootedOutput : ∀
      (Q : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths →
      (∀ p ∈ Q.paths,
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) →
      Q.paths.PairwiseDisjoint
        (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier →
      Nonempty (L.CanonicalEqualRootedOutput hL Q)) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  obtain ⟨Q, hQP, hQpure, hQstat, hQdisjoint⟩ :=
    L.exists_targetPure_stationary_decodedCarrierDisjoint_equalSubwarp
      hL P hpure hstat
  exact (rootedOutput Q hQP hQpure hQstat hQdisjoint).some.exists_hindrance
    hQdisjoint

/-- Reserved-source form of the equal-branch reduction.  The callback is
the precise remaining whole-family obligation: all essential terminals
must be rooted in the concrete relation.  Stationarity, target purity,
collision freedom, antichain geometry, and omission of an original source
are discharged here. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_sourceRooted
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (sourceRooted : ∀
      (q : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph),
      q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths →
      ∀ (Q : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths →
      (∀ p ∈ Q.paths,
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) →
      Q.paths.PairwiseDisjoint
        (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier →
      (∀ p ∈ Q.paths,
        Disjoint p.support
          (collisionCarrier (L.popularAuxiliaryInput hL.legal) q)) →
      ∀ b ∈ (L.popularAuxiliaryInput hL.legal).terminalCut,
        ∃ a ∈ Gamma.source, Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (L.popularAuxiliaryInput hL.legal) Q) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  obtain ⟨q, hq, Q, hQP, hQpure, hQstat, hQdisjoint, hQavoid⟩ :=
    L.exists_reserved_targetPure_stationary_equalSubwarp hL P hpure hstat
  have hqsource : q.start ∈
      (L.popularAuxiliaryInput hL.legal).lambda.source :=
    ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq
  obtain ⟨R⟩ := L.reservedGroundedParent_nonempty hL q hqsource
  exact R.exists_hindrance_of_sourceRooted Q hQdisjoint hQavoid
    (sourceRooted q hq Q hQP hQpure hQstat hQdisjoint hQavoid)

end KappaLadder
end DWeb
end Erdos599
