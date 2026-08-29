/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualActiveTransaction
import ErdosProblems.Erdos599.SplitGroundingTargetPureChronology

/-!
# Split-legal chronology for hanging backward owners

The successor-normalized ladder still gives every hanging limiting
component a unique marker stage.  This file defines that stage without
legacy strict provenance and proves the weak owner-stage bound for every
compressed backward link of a target-pure split auxiliary route.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev SplitHangingInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- Every hanging limiting component has a marker as its initial vertex
under split legality. -/
theorem IsSplitLegal.exists_splitMarkerStage_of_mem_limitWarp_of_hanging
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    ∃ b : Ladder.Stage kappa, L.marker b = some p.initial := by
  rcases hlegal.hasAccumulatedInitialProvenance
      (Ladder.finalStage kappa) p hp with
      hpSource | ⟨b, _hb, hmarker⟩
  · exact False.elim (hhang hpSource)
  · exact ⟨b, hmarker⟩

/-- Unique owner stage of a hanging limiting component under split
legality. -/
noncomputable def splitHangingComponentStage
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (p : Gamma.DPath) (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    Ladder.Stage kappa :=
  Classical.choose
    (hlegal.exists_splitMarkerStage_of_mem_limitWarp_of_hanging hp hhang)

@[simp]
theorem marker_splitHangingComponentStage
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (p : Gamma.DPath) (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    L.marker (L.splitHangingComponentStage hlegal p hp hhang) =
      some p.initial :=
  Classical.choose_spec
    (hlegal.exists_splitMarkerStage_of_mem_limitWarp_of_hanging hp hhang)

/-- Two hanging limiting components with the same split owner stage are the
same warp component. -/
theorem IsSplitLegal.hangingComponent_eq_of_splitStage_eq
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    {p q : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hpHang : PopularAuxiliary.IsHangingPath Gamma p)
    (hq : q ∈ L.limitWarp)
    (hqHang : PopularAuxiliary.IsHangingPath Gamma q)
    (hstage :
      L.splitHangingComponentStage hlegal p hp hpHang =
        L.splitHangingComponentStage hlegal q hq hqHang) :
    p = q := by
  have hpMarker :=
    L.marker_splitHangingComponentStage hlegal p hp hpHang
  have hqMarker :=
    L.marker_splitHangingComponentStage hlegal q hq hqHang
  rw [hstage] at hpMarker
  have hinitial : p.initial = q.initial :=
    Option.some.inj (hpMarker.symm.trans hqMarker)
  exact DWeb.IsWarp.eq_of_initial_eq Gamma
    (hlegal.warpStages (Ladder.finalStage kappa)) hp hq hinitial

/-- Roof membership of a support point propagates backwards along a limiting
component to its initial vertex. -/
theorem IsSplitLegal.limitComponent_initial_mem_roof_of_support_mem
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (c : Ladder.Stage kappa) {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    {v : V} (hvp : v ∈ p.support)
    (hvRoof : v ∈ Gamma.roof (L.frontier c)) :
    p.initial ∈ Gamma.roof (L.frontier c) := by
  have hback : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∈ Gamma.roof (L.frontier c) →
      x ∈ Gamma.roof (L.frontier c) := by
    intro x y hxy hyRoof
    have hxyFamily :
        (x, y) ∈ (L.splitPopularAuxiliaryInput hlegal).familyEdges :=
      ⟨p, hp, hxy⟩
    exact
      (hlegal.familyEdge_tail_mem_strictRoof_frontier
        c hxyFamily hyRoof).1
  rcases p with p | r
  · apply Walk.start_mem_of_meets_of_backwardClosed
      (w := p.walk) (R := Gamma.roof (L.frontier c))
    · intro x y hxy hy
      exact hback hxy hy
    · exact ⟨v, hvp, hvRoof⟩
  · obtain ⟨n, hn⟩ := hvp
    subst v
    change r 0 ∈ Gamma.roof (L.frontier c)
    induction n with
    | zero => exact hvRoof
    | succ n ih =>
        apply ih
        apply hback
        · exact ⟨n, rfl⟩
        · exact hvRoof

/-- If a support point of a hanging component is roofed at the successor of
stage a, its split owner stage is at most a. -/
theorem IsSplitLegal.splitHangingComponentStage_le_of_support_mem_roof_successor
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (a : Ladder.Stage kappa) {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p)
    {v : V} (hvp : v ∈ p.support)
    (hvRoof : v ∈ Gamma.roof
      (L.frontier (L.splitSuccessorStage hlegal a))) :
    L.splitHangingComponentStage hlegal p hp hhang ≤ a := by
  let b := L.splitHangingComponentStage hlegal p hp hhang
  have hbMarker : L.marker b = some p.initial :=
    L.marker_splitHangingComponentStage hlegal p hp hhang
  have hInitialRoof : p.initial ∈ Gamma.roof
      (L.frontier (L.splitSuccessorStage hlegal a)) :=
    hlegal.limitComponent_initial_mem_roof_of_support_mem
      (L.splitSuccessorStage hlegal a) hp hvp hvRoof
  by_contra hnot
  have hab : a < b := lt_of_not_ge hnot
  have hsuccle : L.splitSuccessorStage hlegal a ≤ b :=
    (L.splitSuccessorStage_le_iff_lt hlegal).2 hab
  have hInitialRoofB : p.initial ∈ Gamma.roof (L.frontier b) := by
    rcases hsuccle.lt_or_eq with hlt | heq
    · exact Gamma.roof_cut (hlegal.frontierChronology hlt) hInitialRoof
    · rwa [heq] at hInitialRoof
  exact L.splitMarker_not_mem_roof_frontier hlegal hbMarker hInitialRoofB

/-- Split finite-source gadget-exit successor-roof transport. -/
theorem IsSplitLegal.splitTargetPure_finite_gadgetExit_successorRoofTransport
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (q : FinitePath (L.splitPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitPopularAuxiliaryInput hlegal).IsTargetPure q)
    (x : L.finiteTerminalSet)
    (z : (L.splitPopularAuxiliaryInput hlegal).LV) (y : V)
    (hqx : q.start = .old x.1) (hqz : q.finish = z)
    (hzexit : (L.splitPopularAuxiliaryInput hlegal).gadgetExit z = some y) :
    y ∈ Gamma.roof
      (L.frontier (L.splitSuccessorStage hlegal
        (L.finiteTerminalStage x))) := by
  let I := L.splitPopularAuxiliaryInput hlegal
  have hrun : PopularAuxiliary.Input.RunsFromTo x.1 y
      (I.decodeWalkSteps q.walk) :=
    I.decodeWalkSteps_runs_from_entry q.walk (by rw [hqx]; rfl)
      (by rw [hqz]; exact hzexit)
  exact hlegal.splitTargetPure_run_terminal_mem_roof
    (L.splitSuccessorStage hlegal (L.finiteTerminalStage x))
      q hs hpure hrun
    (L.splitFiniteTerminal_mem_strictRoof_successorFrontier hlegal x)

/-- Split proxy gadget-exit successor-roof transport. -/
theorem IsSplitLegal.splitTargetPure_proxy_gadgetExit_successorRoofTransport
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (q : FinitePath (L.splitPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitPopularAuxiliaryInput hlegal).IsTargetPure q)
    (i : L.splitInfiniteRecords)
    (z : (L.splitPopularAuxiliaryInput hlegal).LV) (y : V)
    (hqi : q.start = .proxy i) (hqz : q.finish = z)
    (hzexit : (L.splitPopularAuxiliaryInput hlegal).gadgetExit z = some y) :
    y ∈ Gamma.roof
      (L.frontier (L.splitSuccessorStage hlegal
        (L.splitInfiniteStage i))) := by
  let I := L.splitPopularAuxiliaryInput hlegal
  obtain ⟨w, hwProxy, hrun⟩ :=
    I.decodeWalkSteps_runs_from_eq_proxy q.walk hqi (by
      rw [hqz]
      exact hzexit)
  exact hlegal.splitTargetPure_run_terminal_mem_roof
    (L.splitSuccessorStage hlegal (L.splitInfiniteStage i))
      q hs hpure hrun
    (L.splitPopularAuxiliary_proxyPath_support_subset_strictRoof
      hlegal i hwProxy)

/-- A target-pure split route can meet a hanging limiting component only at
an owner stage weakly below the route source stage. -/
theorem splitTargetPure_hangingComponentStage_le_of_gadgetExit_contact
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (p : FinitePath (SplitHangingInput L hL).lambda.graph)
    (hs : p.start ∈ (SplitHangingInput L hL).lambda.source)
    (hpure : (SplitHangingInput L hL).IsTargetPure p)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (z : (SplitHangingInput L hL).LV)
    (hzp : z ∈ p.support)
    (v : V) (hvY : v ∈ Y.support)
    (hzexit : (SplitHangingInput L hL).gadgetExit z = some v) :
    L.splitHangingComponentStage hL.legal Y hY hhang ≤
      (L.splitPopularAuxiliaryIndexed hL).f ⟨p.start, hs⟩ := by
  let I := SplitHangingInput L hL
  let U := L.splitPopularAuxiliaryIndexed hL
  have hmeet : p.walk.Meets ({z} : Set I.LV) :=
    ⟨z, hzp, Set.mem_singleton z⟩
  let q : FinitePath I.lambda.graph :=
    p.firstHit ({z} : Set I.LV) hmeet
  have hqStart : q.start = p.start := rfl
  have hqFinish : q.finish = z :=
    Set.mem_singleton_iff.1
      (p.firstHit_finish_mem ({z} : Set I.LV) hmeet)
  have hqSource : q.start ∈ I.lambda.source := hqStart ▸ hs
  have hqPure : I.IsTargetPure q :=
    PopularAuxiliary.Input.IsTargetPure.firstHit I hpure
      ({z} : Set I.LV) hmeet
  rcases I.start_of_mem_lambda_source p hs with
      ⟨x, hxSource, hpx⟩ | ⟨i, hpi⟩
  · let xs : L.finiteTerminalSet := ⟨x, hxSource⟩
    have hvRoof : v ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal
          (L.finiteTerminalStage xs))) :=
      hL.legal.splitTargetPure_finite_gadgetExit_successorRoofTransport
        q hqSource hqPure xs z v (hqStart.trans hpx) hqFinish hzexit
    have hle :=
      hL.legal.splitHangingComponentStage_le_of_support_mem_roof_successor
        (L.finiteTerminalStage xs) hY hhang hvY hvRoof
    have hsEq :
        (⟨p.start, hs⟩ : I.lambda.source) =
          ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
      Subtype.ext hpx
    rw [hsEq]
    exact hle
  · have hvRoof : v ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal
          (L.splitInfiniteStage i))) :=
      hL.legal.splitTargetPure_proxy_gadgetExit_successorRoofTransport
        q hqSource hqPure i z v (hqStart.trans hpi) hqFinish hzexit
    have hle :=
      hL.legal.splitHangingComponentStage_le_of_support_mem_roof_successor
        (L.splitInfiniteStage i) hY hhang hvY hvRoof
    have hsEq :
        (⟨p.start, hs⟩ : I.lambda.source) =
          ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
      Subtype.ext hpi
    rw [hsEq]
    exact hle

/-- Every compressed backward edge still names an edge gadget visited by
the auxiliary path. -/
theorem splitCanonicalErasedRoute_backwardEdge_gadget_mem_support
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitHangingInput L hL).lambda
      (SplitHangingInput L hL).lambda.target)
    (p : WarpPath Q) {e : V × V}
    (he : e ∈ (canonicalErasedRoute
      (SplitHangingInput L hL) Q p).directionEdges .backward) :
    (PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 :
      (SplitHangingInput L hL).LV) ∈ p.1.support := by
  let J := SplitHangingInput L hL
  let T := J.decodeFinitePath p.1
    (Q.starts_in_source p.2) (Q.ends_in_target p.2)
  let E := T.runs.erasedSignedRoute
  have he' : e ∈
      (E.compressionOfValid
        (fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs))).path.directionEdges
          .backward := by
    simpa [canonicalErasedRoute, T, E,
      PopularAuxiliary.Input.MicroTrace.erasedCompression] using he
  have hsigned :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      (fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs))
      .backward he'
  obtain ⟨s, hsE, hsback, hse⟩ := hsigned
  have hsT : s ∈ T.steps := E.steps_sublist.subset hsE
  have hsRaw : s ∈ J.decodeWalkSteps p.1.walk := by
    simpa only [T, PopularAuxiliary.Input.decodeFinitePath_steps] using hsT
  have heRaw : e ∈ PopularAuxiliary.Input.directedSignedEdgeSet
      .backward (J.decodeWalkSteps p.1.walk) :=
    ⟨s, hsRaw, hsback, hse⟩
  rw [J.backwardEdges_decodeWalkSteps p.1.walk] at heRaw
  exact heRaw

/-- Compressed-link form of the weak split owner-stage chronology. -/
theorem splitCanonicalErasedRoute_backwardLink_ownerStage_le_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (Q : Popular.XSWarp
      (SplitHangingInput L hL).lambda
      (SplitHangingInput L hL).lambda.target)
    (p : WarpPath Q)
    (hpure : (SplitHangingInput L hL).IsTargetPure p.1)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (SplitHangingInput L hL) Q p).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma parent)
    (hsub : l.path.IsSubpathOf parent) :
    L.splitHangingComponentStage hL.legal parent hparent hhang ≤
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.1.start, Q.starts_in_source p.2⟩ := by
  obtain ⟨y, hy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      l.path l.path.start_mem_support l.nontrivial
  have hyRoute : (l.path.start, y) ∈
      (canonicalErasedRoute
        (SplitHangingInput L hL) Q p).directionEdges .backward := by
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hy⟩
  have hzSupport :
      (PopularAuxiliary.Input.LambdaVertex.edge l.path.start y :
        (SplitHangingInput L hL).LV) ∈ p.1.support :=
    L.splitCanonicalErasedRoute_backwardEdge_gadget_mem_support
      hL Q p hyRoute
  apply L.splitTargetPure_hangingComponentStage_le_of_gadgetExit_contact hL
    p.1 (Q.starts_in_source p.2) hpure hparent hhang
      (.edge l.path.start y) hzSupport l.path.start
  · exact hsub.1 l.path.start_mem_support
  · rfl

end DWeb.KappaLadder
end Erdos599
