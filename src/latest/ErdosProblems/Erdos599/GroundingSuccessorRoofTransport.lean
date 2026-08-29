/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingHangingLadderRank
import ErdosProblems.Erdos599.GroundingSuccessorTransport
import ErdosProblems.Erdos599.CyclowarpDecomposition
import ErdosProblems.Erdos599.LadderSuccessorBridge
import ErdosProblems.Erdos599.ControlledSlices

/-!
# The graph-theoretic successor-roof transport

This file proves the missing geometric part of the successor-corrected
version of source Lemma 7.17.  The central invariant is that a directed
edge of a limiting ladder component cannot enter the roof of an earlier
frontier for the first time: if its head is in that roof, the edge already
occurred at the earlier accumulated stage.  Traversing such an edge
backwards therefore lands in the strict roof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- A marker inserted at an earlier stage is roofed by every later
frontier.  The marker singleton is present at the immediate successor
stage, and frontier chronology transports its roof membership onward. -/
theorem marker_mem_roof_frontier_of_lt
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    {a b : Stage kappa} {y : V} (hba : b < a)
    (hy : L.marker b = some y) :
    y ∈ Gamma.roof (L.frontier a) := by
  let c : Stage kappa :=
    ⟨b.1 + 1, by
      exact lt_of_le_of_lt
        ((Order.add_one_le_iff).2 (show b.1 < a.1 from hba)) a.2⟩
  have hc_le : c ≤ a := by
    change b.1 + 1 ≤ a.1
    exact (Order.add_one_le_iff).2 hba
  have hySucc : Gamma.trivialPath y ∈ L.successorWarp b :=
    (hlegal.freshMarkers.2 b y hy).2
  have hyWarp : Gamma.trivialPath y ∈ L.warpAt c := by
    change Gamma.trivialPath y ∈
      L.accumulated (Ladder.Stage.toExtended c)
    change Gamma.trivialPath y ∈
      L.accumulated (Ladder.Stage.succExtended b) at hySucc
    simpa [c, Ladder.Stage.toExtended, Ladder.Stage.succExtended] using hySucc
  have hyTerminal : y ∈ Gamma.terminalFrontier (L.warpAt c) :=
    ⟨Gamma.trivialPath y, hyWarp, Gamma.terminal?_trivialPath y⟩
  have hyRoofC : y ∈ Gamma.roof (L.frontier c) := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      Gamma.roof_essential]
    exact Gamma.subset_roof _ hyTerminal
  rcases hc_le.lt_or_eq with hca | hca
  · exact Gamma.roof_cut (hlegal.frontierChronology hca) hyRoofC
  · rw [← hca]
    exact hyRoofC

/-- Every accumulated family of a legal ladder is self-roofing.  This is
not a separate legality assumption: initial provenance puts the initial point
of each component either in the original source or at an already inserted
marker, and warp disjointness then lets `pathSupportRoof` propagate that
roof membership along the component. -/
theorem IsLegal.vertexSet_warpAt_subset_roof_terminalFrontier
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (a : Stage kappa) :
    Gamma.vertexSet (L.warpAt a) ⊆
      Gamma.roof (Gamma.terminalFrontier (L.warpAt a)) := by
  rintro x ⟨p, hp, hxp⟩
  let T := Gamma.terminalFrontier (L.warpAt a)
  have hpInitialRoofFrontier : p.initial ∈ Gamma.roof (L.frontier a) := by
    rcases hlegal.hasAccumulatedInitialProvenance
        (Stage.toExtended a) p hp with hpSource | ⟨b, hba, hbMarker⟩
    · rw [L.frontier_eq_essential_terminalFrontier
          hlegal.roofsSourceAtStages,
        Gamma.roof_essential]
      exact hlegal.roofsSourceAtStages (Stage.toExtended a) hpSource
    · have hba' : b < a := by
        change b.1 + 1 ≤ a.1 at hba
        change b.1 < a.1
        exact (Order.add_one_le_iff).1 hba
      exact L.marker_mem_roof_frontier_of_lt hlegal hba' hbMarker
  have hpInitialRoof : p.initial ∈ Gamma.roof T := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      Gamma.roof_essential] at hpInitialRoofFrontier
    exact hpInitialRoofFrontier
  have hpInterTerminal : p.support ∩ T ⊆
      (match Gamma.terminal? p with
      | some t => ({t} : Set V)
      | none => ∅) := by
    exact Gamma.waveRoofSystem.support_inter_terminalSet_subset
      (show Gamma.IsWarp (L.warpAt a) from
        hlegal.warpStages (Stage.toExtended a)) hp
  have hpSupportRoof : p.support ⊆ Gamma.roof T := by
    apply Gamma.pathSupportRoof p T hpInitialRoof
    · intro t ht
      exact ⟨p, hp, ht⟩
    · exact hpInterTerminal
  exact hpSupportRoof hxp

/-- At a self-roofing warp stage, the tail of every directed family edge
lies in the strict roof of that stage's terminal frontier. -/
theorem IsLegal.edge_tail_mem_strictRoof_of_mem_warpAt
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (a : Stage kappa) {u v : V}
    (he : (u, v) ∈ Gamma.pathFamilyEdgeSet (L.warpAt a)) :
    u ∈ Gamma.strictRoof (Gamma.terminalFrontier (L.warpAt a)) := by
  rcases he with ⟨p, hp, hep⟩
  have huSupport : u ∈ p.support :=
    (p.edgeSet_subset_support_prod hep).1
  refine ⟨hlegal.vertexSet_warpAt_subset_roof_terminalFrontier a
    ⟨p, hp, huSupport⟩, ?_⟩
  intro huEssential
  obtain ⟨q, hq, hqTerminal⟩ := huEssential.1
  have hpq : p = q := by
    by_contra hpq
    exact Set.disjoint_left.1
      (hlegal.warpStages (Stage.toExtended a) hp hq hpq)
      huSupport (Gamma.terminal_mem_support hqTerminal)
  subst q
  rcases p with p | r
  · exact _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
      p hep (Option.some.inj hqTerminal).symm
  · simp at hqTerminal

/-- The head of a directed edge of a path is never the path's initial
vertex. -/
theorem path_edge_head_ne_initial {p : Gamma.DPath} {u v : V}
    (he : (u, v) ∈ p.edgeSet) : v ≠ p.initial := by
  rcases p with p | r
  · exact
      _root_.Erdos599.Alternating.FinitePath.target_ne_start_of_mem_edgeSet
        p he
  · rintro rfl
    rcases he with ⟨n, hn⟩
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

/-- Every noninitial point of a lifted rung path avoids the complete roof
of the old accumulated terminal frontier.  The quotient construction gives
avoidance of the strict roof and of the raw terminal frontier separately;
the essential part of that terminal frontier accounts for the boundary of
the roof. -/
theorem liftStagePath_not_mem_roof_of_ne_initial
    (L : Gamma.KappaLadder kappa) (a : Stage kappa)
    (r : (L.stageWeb a).DPath) {x : V}
    (hxr : x ∈ (L.liftStagePath a r).support)
    (hxne : x ≠ r.initial) :
    x ∉ Gamma.roof (Gamma.terminalFrontier (L.warpAt a)) := by
  let T := Gamma.terminalFrontier (L.warpAt a)
  let Q := Gamma.quotient T
  let r' : Q.essentialPart.DPath := r
  let q : Q.DPath := Q.liftEssentialPartPath r'
  have hxq : x ∈ q.support := by
    dsimp only [q]
    rw [Q.support_liftEssentialPartPath]
    rwa [L.support_liftStagePath a r] at hxr
  have hxqne : x ≠ q.initial := by
    dsimp only [q]
    rw [Q.initial_liftEssentialPartPath]
    exact hxne
  have hav := Gamma.quotientPath_avoids_after_initial T q hxq hxqne
  intro hxRoof
  by_cases hxEssential : x ∈ Gamma.essential T
  · exact hav.2 (Gamma.essential_subset _ hxEssential)
  · exact hav.1 ⟨hxRoof, hxEssential⟩

/-- In particular, the head of every newly contributed rung edge avoids
the old roof. -/
theorem liftStagePath_edge_head_not_mem_roof
    (L : Gamma.KappaLadder kappa) (a : Stage kappa)
    (r : (L.stageWeb a).DPath) {u v : V}
    (he : (u, v) ∈ (L.liftStagePath a r).edgeSet) :
    v ∉ Gamma.roof (Gamma.terminalFrontier (L.warpAt a)) := by
  apply L.liftStagePath_not_mem_roof_of_ne_initial a r
  · exact ((L.liftStagePath a r).edgeSet_subset_support_prod he).2
  · simpa only [L.initial_liftStagePath a r] using
      (path_edge_head_ne_initial (Gamma := Gamma) he)

/-- No directed family edge can enter an earlier ladder roof for the first
time at a later stage.  New successor edges lie on lifted quotient paths,
whose noninitial vertices avoid the old roof; genuine limits add no new
directed edge, because the edge set of a threadwise limit is the union of
the earlier edge sets. -/
theorem IsLegal.pathFamilyEdgeSet_of_head_mem_roof_frontier
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (c : Stage kappa) :
    ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord), c.1 ≤ o →
      ∀ {u v : V},
        (u, v) ∈ Gamma.pathFamilyEdgeSet
            (L.accumulated (⟨o, ho⟩ : ExtendedStage kappa)) →
        v ∈ Gamma.roof (L.frontier c) →
        (u, v) ∈ Gamma.pathFamilyEdgeSet (L.warpAt c) := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
      intro ho hc u v he _hv
      have hc0 : c.1 = 0 := le_antisymm hc bot_le
      have hstage : (⟨0, ho⟩ : ExtendedStage kappa) =
          Stage.toExtended c := Subtype.ext hc0.symm
      rwa [hstage] at he
  | add_one o ih =>
      intro ho hc u v he hv
      rcases hc.lt_or_eq with hc | hc
      · have hoKappa : o < kappa.ord :=
          (show o < o + 1 by
            rw [← Order.succ_eq_add_one]
            exact Order.lt_succ o).trans_le ho
        let a : Stage kappa := ⟨o, hoKappa⟩
        have hca : c ≤ a := by
          change c.1 ≤ o
          exact (Order.lt_add_one_iff).1 hc
        have hsucc : (⟨o + 1, ho⟩ : ExtendedStage kappa) =
            Stage.succExtended a := Subtype.ext rfl
        have heSuccessor : (u, v) ∈
            Gamma.pathFamilyEdgeSet (L.successorWarp a) := by
          change (u, v) ∈ Gamma.pathFamilyEdgeSet
            (L.accumulated (Stage.succExtended a))
          rwa [← hsucc]
        rcases heSuccessor with ⟨q, hq, heq⟩
        rcases hlegal.successorComponentProvenance a q hq with
            hArrow | hMarker
        · rcases hArrow with ⟨p, hp, hpq⟩
          rcases hpq with ⟨_hpRay, rfl⟩ |
              ⟨x, _hpTerminal, hcontinue | hfixed⟩
          · exact ih hoKappa.le hca ⟨q, hp, heq⟩ hv
          · rcases hcontinue with ⟨r, _hrInitial,
                _hrMem, _hrTerminal, _hextends, _hsupport,
                hedge, _hqTerminal⟩
            change (u, v) ∈ pathEdgeSet q at heq
            rw [hedge] at heq
            rcases heq with heOld | heNew
            · exact ih hoKappa.le hca ⟨p, hp, heOld⟩ hv
            · have hvRoofA : v ∈ Gamma.roof (L.frontier a) := by
                rcases hca.lt_or_eq with hca | rfl
                · exact Gamma.roof_cut
                    (hlegal.frontierChronology hca) hv
                · exact hv
              have hvRaw : v ∈ Gamma.roof
                  (Gamma.terminalFrontier (L.warpAt a)) := by
                rw [L.frontier_eq_essential_terminalFrontier
                    hlegal.roofsSourceAtStages,
                  Gamma.roof_essential] at hvRoofA
                exact hvRoofA
              exact (L.liftStagePath_edge_head_not_mem_roof a r heNew
                hvRaw).elim
          · rcases hfixed with ⟨_hno, rfl⟩
            exact ih hoKappa.le hca ⟨q, hp, heq⟩ hv
        · rcases hMarker with ⟨y, _hy, rfl⟩
          change (u, v) ∈ (∅ : Set (V × V)) at heq
          exact heq.elim
      · have hcEq : (⟨o + 1, ho⟩ : ExtendedStage kappa) =
            Stage.toExtended c := Subtype.ext hc.symm
        rwa [hcEq] at he
  | limit o hoLimit ih =>
      intro ho hc u v he hv
      rcases hc.lt_or_eq with hc | hc
      · let oe : ExtendedStage kappa := ⟨o, ho⟩
        obtain ⟨C, hstage, hlimit⟩ := hlegal.limitStages oe hoLimit
        have heLimit : (u, v) ∈
            Gamma.pathFamilyEdgeSet (C.limitPaths Gamma) := by
          rw [← hlimit]
          exact he
        rw [C.pathFamilyEdgeSet_limitPaths Gamma] at heLimit
        obtain ⟨b, heb⟩ := Set.mem_iUnion.1 heLimit
        let ci : Set.Iio o := ⟨c.1, hc⟩
        obtain ⟨d, hbd, hcd⟩ := exists_ge_ge b ci
        have hed : (u, v) ∈ Gamma.pathFamilyEdgeSet (C.stage d) :=
          C.pathFamilyEdgeSet_mono Gamma hbd heb
        have hedAccumulated : (u, v) ∈ Gamma.pathFamilyEdgeSet
            (L.accumulated
              (⟨d.1, d.2.le.trans ho⟩ : ExtendedStage kappa)) := by
          rwa [← hstage d]
        exact ih d.1 d.2 (d.2.le.trans ho) hcd hedAccumulated hv
      · have hcEq : (⟨o, ho⟩ : ExtendedStage kappa) =
            Stage.toExtended c := Subtype.ext hc.symm
        rwa [hcEq] at he

/-- Backwards traversal of any limiting-ladder edge whose head is in a
ladder roof lands in the corresponding strict roof. -/
theorem IsLegal.familyEdge_tail_mem_strictRoof_frontier
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (c : Stage kappa) {u v : V}
    (he : (u, v) ∈
      (L.popularAuxiliaryInput hlegal).familyEdges)
    (hv : v ∈ Gamma.roof (L.frontier c)) :
    u ∈ Gamma.strictRoof (L.frontier c) := by
  have heLimit : (u, v) ∈ Gamma.pathFamilyEdgeSet L.limitWarp := by
    change ∃ p ∈ L.limitWarp, (u, v) ∈ p.edgeSet at he
    exact he
  have heStage : (u, v) ∈ Gamma.pathFamilyEdgeSet (L.warpAt c) :=
    hlegal.pathFamilyEdgeSet_of_head_mem_roof_frontier c
      kappa.ord le_rfl c.2.le heLimit hv
  have huRaw := hlegal.edge_tail_mem_strictRoof_of_mem_warpAt c heStage
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    Gamma.strictRoof_essential]
  exact huRaw

/-- Forward traversal of an original edge preserves a ladder roof when
its tail is in the strict roof.  Strictness ensures that the tail is not on
the (essential) frontier itself, so adjoining the edge to a target path
cannot create a spurious meeting with the frontier. -/
theorem IsLegal.edge_head_mem_roof_frontier_of_tail_mem_strictRoof
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (c : Stage kappa) {u v : V} (huv : Gamma.graph.Adj u v)
    (hu : u ∈ Gamma.strictRoof (L.frontier c)) :
    v ∈ Gamma.roof (L.frontier c) := by
  by_contra hv
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (Gamma.not_mem_roof_iff (L.frontier c) v).1 hv
  have huNotFrontier : u ∉ L.frontier c := by
    intro huFrontier
    apply hu.2
    rw [hlegal.frontiersEssential c]
    exact huFrontier
  let tail : Walk Gamma.graph v p.finish :=
    RelationalRoof.castStart Gamma.graph.Adj hpTarget.1 p.walk
  let joined : Walk Gamma.graph u p.finish := .cons huv tail
  obtain ⟨q, hqsub⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := Gamma.graph.Adj) joined
  let r : FinitePath Gamma.graph :=
    { start := u
      finish := p.finish
      walk := q.1
      isPath := q.2 }
  obtain ⟨z, hzr, hzFrontier⟩ := hu.1 r ⟨rfl, hpTarget.2⟩
  have hzjoined : z ∈ joined.support := hqsub hzr
  simp only [joined, Walk.support_cons, List.mem_cons] at hzjoined
  rcases hzjoined with rfl | hztail
  · exact huNotFrontier hzFrontier
  · have hzp : z ∈ p.support := by
      change z ∈ p.walk.support
      simpa only [tail, RelationalRoof.support_castStart] using hztail
    exact Set.disjoint_left.1 hpAvoid hzp hzFrontier

/-- An old auxiliary vertex outside the limiting ladder is strict as soon
as it is roofed by a ladder frontier. -/
theorem IsLegal.mem_strictRoof_frontier_of_mem_roof_of_mem_offLadder
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (c : Stage kappa) {x : V}
    (hxRoof : x ∈ Gamma.roof (L.frontier c))
    (hxOff : x ∈ (L.popularAuxiliaryInput hlegal).offLadder) :
    x ∈ Gamma.strictRoof (L.frontier c) := by
  refine ⟨hxRoof, ?_⟩
  intro hxEssential
  have hxFrontier : x ∈ L.frontier c := by
    rw [← hlegal.frontiersEssential c]
    exact hxEssential
  exact hxOff.2
    (_root_.Erdos599.CardinalInduction.ControlledSlices.frontier_subset_vertexSet_limitWarp_of_legal
        Gamma L hlegal c hxFrontier)

end KappaLadder
end DWeb
end Erdos599
