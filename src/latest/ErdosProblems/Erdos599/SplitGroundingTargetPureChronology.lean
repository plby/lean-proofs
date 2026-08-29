/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitSameStageRecord
import ErdosProblems.Erdos599.SplitGroundingAuxiliary
import ErdosProblems.Erdos599.SplitGroundingChronology
import ErdosProblems.Erdos599.GroundingTargetPureDichotomy
import ErdosProblems.Erdos599.ControlledSlices

/-!
# First-target chronology for the split grounding auxiliary

The successor-normalized split ladder has the same accumulated-warp geometry
as a legacy legal ladder.  Its only different field concerns the provenance
of a recorded hanging component.  The proofs below use the sound
earlier-or-current provenance alternative, and establish the pathwise weak
chronology needed after first-target normalization.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Split legality implies initial provenance for every accumulated
component. -/
theorem IsSplitLegal.hasAccumulatedInitialProvenance
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal) :
    L.HasAccumulatedInitialProvenance := by
  have hprovenance : ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord)
      (p : Gamma.DPath), p ∈ L.accumulated ⟨o, ho⟩ →
        p.initial ∈ Gamma.source ∨
          ∃ b : Ladder.Stage kappa,
            Ladder.Stage.succExtended b ≤ ⟨o, ho⟩ ∧
              L.marker b = some p.initial := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho p hp
        have hzero : (⟨0, ho⟩ : Ladder.ExtendedStage kappa) =
            Ladder.zeroStage kappa := Subtype.ext rfl
        have hpTrivial : p ∈ Gamma.trivialWave := by
          rw [hzero, hlegal.initialStage] at hp
          exact hp
        exact Or.inl
          (Gamma.initialSet_trivialWave ▸ ⟨p, hpTrivial, rfl⟩)
    | add_one o ih =>
        intro ho p hp
        have hoStage : o < kappa.ord := (Order.add_one_le_iff).1 ho
        let a : Ladder.Stage kappa := ⟨o, hoStage⟩
        have hsucc : (⟨o + 1, ho⟩ : Ladder.ExtendedStage kappa) =
            Ladder.Stage.succExtended a := Subtype.ext rfl
        have hpSuccessor : p ∈ L.successorWarp a := by
          change p ∈ L.accumulated (Ladder.Stage.succExtended a)
          rw [← hsucc]
          exact hp
        rcases hlegal.successorComponentProvenance a p hpSuccessor with
            ⟨q, hq, hqp⟩ | ⟨y, hy, rfl⟩
        · have hoo : o ≤ o + 1 := by
            rw [← Order.succ_eq_add_one]
            exact le_succ o
          have hcurrent : Ladder.Stage.toExtended a =
              (⟨o, le_trans hoo ho⟩ : Ladder.ExtendedStage kappa) :=
            Subtype.ext rfl
          have hqAt : q ∈ L.accumulated
              (⟨o, le_trans hoo ho⟩ : Ladder.ExtendedStage kappa) := by
            rw [← hcurrent]
            exact hq
          rcases ih (le_trans hoo ho) q hqAt with
              hqSource | ⟨b, hbStage, hbMarker⟩
          · exact Or.inl (Gamma.extends_initial hqp.extends ▸ hqSource)
          · refine Or.inr ⟨b, hbStage.trans ?_, ?_⟩
            · change o ≤ o + 1
              exact hoo
            · simpa only [Gamma.extends_initial hqp.extends] using hbMarker
        · exact Or.inr ⟨a, le_rfl, by simpa using hy⟩
    | limit o hoLimit ih =>
        intro ho p hp
        let a : Ladder.ExtendedStage kappa := ⟨o, ho⟩
        obtain ⟨C, hstage, hlimit⟩ := hlegal.limitStages a hoLimit
        have hpInitial : p.initial ∈ C.initialUnion := by
          rw [← C.initialSet_limitPaths Gamma, ← hlimit]
          exact ⟨p, hp, rfl⟩
        obtain ⟨b, q, hq, hqp⟩ := Set.mem_iUnion.1 hpInitial
        have hbo : b.1 ≤ kappa.ord := b.2.le.trans ho
        have hqAccumulated : q ∈ L.accumulated ⟨b.1, hbo⟩ := by
          rw [← hstage b]
          exact hq
        rcases ih b.1 b.2 hbo q hqAccumulated with
            hqSource | ⟨c, hcStage, hcMarker⟩
        · exact Or.inl (hqp ▸ hqSource)
        · exact Or.inr ⟨c, hcStage.trans b.2.le, by
            simpa only [hqp] using hcMarker⟩
  intro a p hp
  exact hprovenance a.1 a.2 p hp

/-- A marker inserted at an earlier stage is roofed by every later split
frontier. -/
theorem splitMarker_mem_roof_frontier_of_lt
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
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

/-- Every accumulated split-ladder family is self-roofing. -/
theorem IsSplitLegal.vertexSet_warpAt_subset_roof_terminalFrontier
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
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
      exact splitMarker_mem_roof_frontier_of_lt hlegal hba' hbMarker
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

/-- At a self-roofing split stage, the tail of every family edge is in the
strict roof of its terminal frontier. -/
theorem IsSplitLegal.edge_tail_mem_strictRoof_of_mem_warpAt
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
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

/-- No directed family edge can enter an earlier ladder roof for the first
time at a later stage.  New successor edges lie on lifted quotient paths,
whose noninitial vertices avoid the old roof; genuine limits add no new
directed edge, because the edge set of a threadwise limit is the union of
the earlier edge sets. -/
theorem IsSplitLegal.pathFamilyEdgeSet_of_head_mem_roof_frontier
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
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
theorem IsSplitLegal.familyEdge_tail_mem_strictRoof_frontier
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (c : Stage kappa) {u v : V}
    (he : (u, v) ∈
      (L.splitPopularAuxiliaryInput hlegal).familyEdges)
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
theorem IsSplitLegal.edge_head_mem_roof_frontier_of_tail_mem_strictRoof
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
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

/-- Every split-ladder frontier is carried by the limiting warp. -/
theorem IsSplitLegal.frontier_subset_vertexSet_limitWarp
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (a : Stage kappa) :
    L.frontier a ⊆ Gamma.vertexSet L.limitWarp := by
  intro x hx
  obtain ⟨q, hq, hqx⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (hlegal.roofsSourceAtStages (Stage.toExtended a)) hx
  obtain ⟨r, hr, hqr⟩ :=
    CardinalInduction.ControlledSlices.stagesEmbedInLimit_of_limitStages
      Gamma L hlegal.regular hlegal.limitStages a q hq.1
  exact ⟨r, hr, hqr.1 (Gamma.terminal_mem_support hqx)⟩

/-- An old auxiliary vertex outside the limiting ladder is strict as soon
as it is roofed by a ladder frontier. -/
theorem IsSplitLegal.mem_strictRoof_frontier_of_mem_roof_of_mem_offLadder
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (c : Stage kappa) {x : V}
    (hxRoof : x ∈ Gamma.roof (L.frontier c))
    (hxOff : x ∈ (L.splitPopularAuxiliaryInput hlegal).offLadder) :
    x ∈ Gamma.strictRoof (L.frontier c) := by
  refine ⟨hxRoof, ?_⟩
  intro hxEssential
  have hxFrontier : x ∈ L.frontier c := by
    rw [← hlegal.frontiersEssential c]
    exact hxEssential
  exact hxOff.2
    (hlegal.frontier_subset_vertexSet_limitWarp c hxFrontier)



/-- The split successor stage is definitionally the accumulated successor. -/
@[simp]
theorem warpAt_splitSuccessorStage
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : Stage kappa) :
    L.warpAt (L.splitSuccessorStage hlegal a) = L.successorWarp a := by
  rfl

/-- A finite obstruction-record terminal is strictly roofed by its successor
frontier. -/
theorem splitFiniteTerminal_mem_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (x : L.finiteTerminalSet) :
    x.1 ∈ Gamma.strictRoof
      (L.frontier
        (L.splitSuccessorStage hlegal (L.finiteTerminalStage x))) := by
  obtain ⟨_, p, hp, hpx⟩ := L.finiteTerminalStage_spec x
  have hpAvailable : p ∈ L.bookkeeping.available
      (L.finiteTerminalStage x) :=
    L.bookkeeping.chosen_mem_available hlegal.validBookkeeping hp
  have hxRaw : x.1 ∈ Gamma.strictRoof
      (Gamma.terminalFrontier
        (L.successorWarp (L.finiteTerminalStage x))) :=
    Gamma.terminal_mem_strictRoof_of_mem_inessentialPaths
      hpAvailable.1 hpx
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    Gamma.strictRoof_essential,
    L.warpAt_splitSuccessorStage hlegal]
  exact hxRaw

/-- A selected ray whose initial vertex is roofed by the successor warp has
its whole support in the strict successor roof. -/
theorem splitChosenRay_support_subset_strictRoof_successorFrontier_of_initial
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Stage kappa} {r : Ray Gamma.graph}
    (hchosen : L.chosen a = some (.inr r : Gamma.DPath))
    (hinitial : r.initial ∈ Gamma.roof
      (Gamma.terminalFrontier (L.successorWarp a))) :
    r.support ⊆ Gamma.strictRoof
      (L.frontier (L.splitSuccessorStage hlegal a)) := by
  have hpAvailable :
      (.inr r : Gamma.DPath) ∈ L.bookkeeping.available a :=
    L.bookkeeping.chosen_mem_available hlegal.validBookkeeping hchosen
  let T := Gamma.terminalFrontier (L.successorWarp a)
  have hsupportDisjoint : Disjoint r.support T := by
    apply Set.disjoint_left.2
    intro z hzr hzT
    obtain ⟨q, hqWarp, hqTerminal⟩ := hzT
    have hrq : (.inr r : Gamma.DPath) ≠ q := by
      intro hrq
      have hterminal := congrArg Gamma.terminal? hrq
      rw [Gamma.terminal?_ray, hqTerminal] at hterminal
      cases hterminal
    exact Set.disjoint_left.1
      (hlegal.warpStages (Stage.succExtended a)
        hpAvailable.1.1 hqWarp hrq)
      hzr (Gamma.terminal_mem_support hqTerminal)
  have hsupportRoof : r.support ⊆ Gamma.roof T := by
    apply Gamma.pathSupportRoof (.inr r : Gamma.DPath) T
    · exact hinitial
    · intro t ht
      rw [Gamma.terminal?_ray] at ht
      cases ht
    · intro z hz
      exact False.elim
        (Set.disjoint_left.1 hsupportDisjoint hz.1 hz.2)
  intro z hzr
  have hzRoof : z ∈ Gamma.roof
      (L.frontier (L.splitSuccessorStage hlegal a)) := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      Gamma.roof_essential,
      L.warpAt_splitSuccessorStage hlegal]
    exact hsupportRoof hzr
  refine ⟨hzRoof, ?_⟩
  intro hzEssential
  have hzFrontier :
      z ∈ L.frontier (L.splitSuccessorStage hlegal a) := by
    rw [← hlegal.frontiersEssential
      (L.splitSuccessorStage hlegal a)]
    exact hzEssential
  have hzT : z ∈ T := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      L.warpAt_splitSuccessorStage hlegal] at hzFrontier
    exact hzFrontier.1
  exact Set.disjoint_left.1 hsupportDisjoint hzr hzT

/-- A marker is roofed by the frontier immediately after its insertion. -/
theorem splitMarker_mem_roof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Stage kappa} {y : V} (hy : L.marker a = some y) :
    y ∈ Gamma.roof (L.frontier (L.splitSuccessorStage hlegal a)) := by
  have hyWarp : Gamma.trivialPath y ∈ L.successorWarp a :=
    (hlegal.freshMarkers.2 a y hy).2
  have hyTerminal : y ∈ Gamma.terminalFrontier (L.successorWarp a) :=
    ⟨Gamma.trivialPath y, hyWarp, Gamma.terminal?_trivialPath y⟩
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    Gamma.roof_essential,
    L.warpAt_splitSuccessorStage hlegal]
  exact Gamma.subset_roof _ hyTerminal

/-- Every split proxy path, including a genuine same-stage hanging ray, is
strictly roofed by the successor frontier of its record stage. -/
theorem splitInfinitePath_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (i : L.splitInfiniteRecords) :
    (L.splitInfinitePath hlegal i).support ⊆
      Gamma.strictRoof
        (L.frontier
          (L.splitSuccessorStage hlegal (L.splitInfiniteStage i))) := by
  obtain ⟨r, hr⟩ := L.splitInfinitePath_isRay hlegal i
  let a := L.splitInfiniteStage i
  have hchosen : L.chosen a = some (.inr r : Gamma.DPath) := by
    rw [← hr]
    exact (L.splitInfiniteStage_spec i).2
  have hpInitialRoof : r.initial ∈ Gamma.roof
      (Gamma.terminalFrontier (L.successorWarp a)) := by
    by_cases hground : r.initial ∈ Gamma.source
    · exact hlegal.roofsSourceAtStages (Stage.succExtended a) hground
    · have haHanging : a ∈ L.phiHanging := by
        refine ⟨(L.splitInfiniteStage_spec i).1.1, ?_⟩
        rintro ⟨p, hp, hpGround⟩
        have hpr : p = (.inr r : Gamma.DPath) :=
          Option.some.inj (hp.symm.trans hchosen)
        rw [hpr] at hpGround
        exact hground hpGround
      rcases hlegal.splitHangingProvenance.resolve a haHanging
          (.inr r : Gamma.DPath) hchosen with
          ⟨b, hba, hbMarker⟩ | ⟨_hnew, haMarker⟩
      · have hbRoof : r.initial ∈ Gamma.roof
            (L.frontier (L.splitSuccessorStage hlegal b)) :=
          L.splitMarker_mem_roof_successorFrontier hlegal hbMarker
        have hsucc : L.splitSuccessorStage hlegal b <
            L.splitSuccessorStage hlegal a := by
          change b.1 + 1 < a.1 + 1
          rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
          exact Order.succ_lt_succ hba
        have haRoof : r.initial ∈ Gamma.roof
            (L.frontier (L.splitSuccessorStage hlegal a)) :=
          Gamma.roof_cut (hlegal.frontierChronology hsucc) hbRoof
        rw [L.frontier_eq_essential_terminalFrontier
            hlegal.roofsSourceAtStages,
          Gamma.roof_essential,
          L.warpAt_splitSuccessorStage hlegal] at haRoof
        exact haRoof
      · have haRoof : r.initial ∈ Gamma.roof
            (L.frontier (L.splitSuccessorStage hlegal a)) :=
          L.splitMarker_mem_roof_successorFrontier hlegal haMarker
        rw [L.frontier_eq_essential_terminalFrontier
            hlegal.roofsSourceAtStages,
          Gamma.roof_essential,
          L.warpAt_splitSuccessorStage hlegal] at haRoof
        exact haRoof
  rw [hr]
  exact L.splitChosenRay_support_subset_strictRoof_successorFrontier_of_initial
    hlegal hchosen hpInitialRoof

/-- Input-level form of the split proxy support theorem. -/
theorem splitPopularAuxiliary_proxyPath_support_subset_strictRoof
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (i : L.splitInfiniteRecords) :
    ((L.splitPopularAuxiliaryInput hlegal).proxyPath i).support ⊆
      Gamma.strictRoof
        (L.frontier
          (L.splitSuccessorStage hlegal (L.splitInfiniteStage i))) :=
  L.splitInfinitePath_support_subset_strictRoof_successorFrontier hlegal i



/-- The decoded run of a target-pure split-auxiliary path preserves the
selected ladder roof. -/
theorem IsSplitLegal.splitTargetPure_run_terminal_mem_roof
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (c : Stage kappa)
    (p : FinitePath (L.splitPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : p.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitPopularAuxiliaryInput hlegal).IsTargetPure p)
    {x y : V}
    (hrun : PopularAuxiliary.Input.RunsFromTo x y
      ((L.splitPopularAuxiliaryInput hlegal).decodeWalkSteps p.walk))
    (hx : x ∈ Gamma.strictRoof (L.frontier c)) :
    y ∈ Gamma.roof (L.frontier c) := by
  let I := L.splitPopularAuxiliaryInput hlegal
  apply PopularAuxiliary.Input.RunsFromTo.terminal_mem_roof_of_forwardPairsRecoverStrict
      (L := I) hrun
      (R := Gamma.roof (L.frontier c))
      (Rs := Gamma.strictRoof (L.frontier c))
  · exact fun _ hz ↦ hz.1
  · exact hx.1
  · intro _ _ _
    exact hx
  · intro s hsmem hback hsEntry
    have hedge : s.edge ∈ I.familyEdges :=
      I.decodeWalkSteps_backward_on_ladder p hs hsmem hback
    have htail := hlegal.familyEdge_tail_mem_strictRoof_frontier
      c hedge (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hback]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hback] using htail
  · intro s hsmem hforward hsEntry
    have hadj : Gamma.graph.Adj s.edge.1 s.edge.2 :=
      I.decodeWalkSteps_valid p hs hsmem
    have hhead := hlegal.edge_head_mem_roof_frontier_of_tail_mem_strictRoof
      c hadj (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hforward]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hforward] using hhead
  · intro z hzRoof hzOff
    exact hlegal.mem_strictRoof_frontier_of_mem_roof_of_mem_offLadder
      c hzRoof hzOff
  · exact I.decodeWalkSteps_forwardPairsRecoverStrict p hpure

/-- Target-pure paths beginning at a finite split record transport their old
endpoint into the record's successor roof. -/
theorem IsSplitLegal.splitTargetPure_finite_successorRoofTransport
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (q : FinitePath (L.splitPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitPopularAuxiliaryInput hlegal).IsTargetPure q)
    (x : L.finiteTerminalSet) (y : V)
    (hqx : q.start = .old x.1) (hqy : q.finish = .old y) :
    y ∈ Gamma.roof
      (L.frontier
        (L.splitSuccessorStage hlegal (L.finiteTerminalStage x))) := by
  let I := L.splitPopularAuxiliaryInput hlegal
  have hrun : PopularAuxiliary.Input.RunsFromTo x.1 y
      (I.decodeWalkSteps q.walk) :=
    I.decodeWalkSteps_runs_from_entry q.walk (by rw [hqx]; rfl)
      (by rw [hqy]; rfl)
  exact hlegal.splitTargetPure_run_terminal_mem_roof
    (L.splitSuccessorStage hlegal (L.finiteTerminalStage x))
      q hs hpure hrun
    (L.splitFiniteTerminal_mem_strictRoof_successorFrontier hlegal x)

/-- Target-pure paths beginning at a split proxy transport their old endpoint
into the represented record's successor roof. -/
theorem IsSplitLegal.splitTargetPure_proxy_successorRoofTransport
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (q : FinitePath (L.splitPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitPopularAuxiliaryInput hlegal).IsTargetPure q)
    (i : L.splitInfiniteRecords) (y : V)
    (hqi : q.start = .proxy i) (hqy : q.finish = .old y) :
    y ∈ Gamma.roof
      (L.frontier
        (L.splitSuccessorStage hlegal (L.splitInfiniteStage i))) := by
  let I := L.splitPopularAuxiliaryInput hlegal
  obtain ⟨z, hzProxy, hrun⟩ :=
    I.decodeWalkSteps_runs_from_eq_proxy q.walk hqi (by
      rw [hqy]
      rfl)
  exact hlegal.splitTargetPure_run_terminal_mem_roof
    (L.splitSuccessorStage hlegal (L.splitInfiniteStage i))
      q hs hpure hrun
    (L.splitPopularAuxiliary_proxyPath_support_subset_strictRoof
      hlegal i hzProxy)

/-- Exact weak chronology for one target-pure path of the split auxiliary. -/
theorem splitTargetPure_auxiliaryNonincreasing
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (q : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph)
    (hs : q.start ∈
      (L.splitPopularAuxiliaryInput hL.legal).lambda.source)
    (ht : q.finish ∈
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (hpure : (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure q) :
    (L.splitPopularAuxiliaryIndexed hL).g ⟨q.finish, ht⟩ ≤
      (L.splitPopularAuxiliaryIndexed hL).f ⟨q.start, hs⟩ := by
  let I := L.splitPopularAuxiliaryInput hL.legal
  let U := L.splitPopularAuxiliaryIndexed hL
  obtain ⟨y, hyTarget, hqy⟩ := I.finish_of_mem_lambda_target q ht
  have hyMarker : y ∈ L.markerSet := hyTarget.1
  let b : Stage kappa := L.markerStage ⟨y, hyMarker⟩
  have hmarker : L.marker b = some y :=
    L.markerStage_spec ⟨y, hyMarker⟩
  have hyNotRoof : y ∉ Gamma.roof (L.frontier b) :=
    L.splitMarker_not_mem_roof_frontier hL.legal hmarker
  rcases I.start_of_mem_lambda_source q hs with
      ⟨x, hxSource, hqx⟩ | ⟨i, hqi⟩
  · let xs : L.finiteTerminalSet := ⟨x, hxSource⟩
    let a : Stage kappa := L.finiteTerminalStage xs
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal a)) :=
      hL.legal.splitTargetPure_finite_successorRoofTransport
        q hs hpure xs y hqx hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : L.splitSuccessorStage hL.legal a ≤ b :=
        (L.splitSuccessorStage_le_iff_lt hL.legal).2 hab
      apply hyNotRoof
      rcases hsuccle.lt_or_eq with hlt | heq
      · exact Gamma.roof_cut (hL.legal.frontierChronology hlt) hyRoofSucc
      · rwa [heq] at hyRoofSucc
    have htEq : (⟨q.finish, ht⟩ : I.lambda.target) =
        ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsEq : (⟨q.start, hs⟩ : I.lambda.source) =
        ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
      Subtype.ext hqx
    rw [htEq, hsEq]
    exact hba
  · let a : Stage kappa := L.splitInfiniteStage i
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal a)) :=
      hL.legal.splitTargetPure_proxy_successorRoofTransport
        q hs hpure i y hqi hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : L.splitSuccessorStage hL.legal a ≤ b :=
        (L.splitSuccessorStage_le_iff_lt hL.legal).2 hab
      apply hyNotRoof
      rcases hsuccle.lt_or_eq with hlt | heq
      · exact Gamma.roof_cut (hL.legal.frontierChronology hlt) hyRoofSucc
      · rwa [heq] at hyRoofSucc
    have htEq : (⟨q.finish, ht⟩ : I.lambda.target) =
        ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsEq : (⟨q.start, hs⟩ : I.lambda.source) =
        ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
      Subtype.ext hqi
    rw [htEq, hsEq]
    exact hba



/-- The split auxiliary has an unconditional first-target-normalized
grounded equal branch or a popular separator.  The genuine same-stage
records are eliminated only after constructing the equal target warp. -/
theorem splitPopularAuxiliary_targetPure_groundEqual_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    (∃ P : Popular.XSWarp
        (L.splitPopularAuxiliaryInput hL.legal).lambda
        (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
      (∀ p (_hp : p ∈ P.paths),
        (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p) ∧
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          L.phiGround)) ∨
      Nonempty
        (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  let U := L.splitPopularAuxiliaryIndexed hL
  have hsource : U.SourceBounded :=
    U.sourceBounded_of_sourceIndexed
      (L.splitPopularAuxiliaryIndexed_sourceIndexed hL)
  rcases Popular.stronglyPopular_target_or_popularSeparator U hsource with
      ⟨P, hP⟩ | hseparator
  · let Q := P.firstTargetWarp
    have hQstat : Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf U Q.paths Q.starts_in_source) :=
      hP.mono (P.initialIndices_subset_firstTargetWarp U)
    have hQpure : ∀ p (hp : p ∈ Q.paths),
        (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p := by
      intro p hp
      rcases hp with ⟨q, rfl⟩
      exact (L.splitPopularAuxiliaryInput hL.legal)
        |>.firstHit_target_isTargetPure q.1
          ⟨q.1.finish, q.1.finish_mem_support,
            P.ends_in_target q.2⟩
    have hmono : ∀ p (hp : p ∈ Q.paths),
        U.g ⟨p.finish, Q.ends_in_target hp⟩ ≤
          U.f ⟨p.start, Q.starts_in_source hp⟩ := by
      intro p hp
      exact L.splitTargetPure_auxiliaryNonincreasing hL p
        (Q.starts_in_source hp) (Q.ends_in_target hp) (hQpure p hp)
    have hequal : Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf U (U.equalSubwarp Q).paths
          (U.equalSubwarp Q).starts_in_source) :=
      U.stationary_equalSubwarp_of_pathwise_nonincreasing
        Q hQstat hmono
    exact Or.inl ⟨Q, hQpure,
      L.splitEqualSubwarp_ground_isStationary hL Q hequal⟩
  · exact Or.inr hseparator

/-- Unconditional prior-ground/fresh-ground/separator reduction for split
legality.  No successor-roof provider and no false strict provenance are
used. -/
theorem splitPopularAuxiliary_targetPure_prior_or_fresh_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages ∨
      Stationary.IsStationaryBelow kappa
          L.freshInessentialGroundStages ∨
        Nonempty
          (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  rcases L.splitPopularAuxiliary_targetPure_groundEqual_or_separator hL with
      ⟨P, _hPpure, hgroundEqual⟩ | hseparator
  · have hground : Stationary.IsStationaryBelow kappa L.phiGround :=
      hgroundEqual.mono (fun _ ha ↦ ha.2)
    rcases L.stationary_prior_or_fresh_of_stationary_phiGround
        hL.legal hground with hprior | hfresh
    · exact Or.inl hprior
    · exact Or.inr (Or.inl hfresh)
  · exact Or.inr (Or.inr hseparator)


end KappaLadder
end DWeb
end Erdos599



