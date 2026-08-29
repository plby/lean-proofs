/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingFreshEmergenceGap
import ErdosProblems.Erdos599.SplitGroundingAuxiliary
import ErdosProblems.Erdos599.SplitGroundingTargetPureChronology

/-!
# Fresh target markers lie outside the pre-marker successor roof

At a successor stage the accumulated warp is the exact arrow part together
with the optional singleton marker.  If the new marker were already roofed
by the terminal frontier of the arrow part, its singleton component would
be inessential in the full successor.  Canonical inessential persistence
would then keep that singleton inessential in the limiting warp, which is
incompatible with the marker lying on an essential limiting component.

This is the precise positive pre-marker fact available in the genuinely
fresh branch.  It does not by itself say that every auxiliary path starting
at a fresh record is confined to the pre-marker roof.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Two exact realizations of the same functional rung-arrow relation agree.
The proof only uses the warp property of the rung. -/
private theorem isRungArrowResult_eq
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hrung : (L.stageWeb a).IsWarp (L.rung a))
    {Z W : Set G.DPath}
    (hZ : L.IsRungArrowResult a Z)
    (hW : L.IsRungArrowResult a W) : Z = W := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := hZ.2 q hq
    obtain ⟨r, hr, _hrUnique⟩ := hW.1 p hp
    have hqr : q = r :=
      L.isRungArrowPair_unique_of_rungWarp a hrung p q r hpq hr.2
    exact hqr ▸ hr.1
  · intro hq
    obtain ⟨p, hp, hpq⟩ := hW.2 q hq
    obtain ⟨r, hr, _hrUnique⟩ := hZ.1 p hp
    have hqr : q = r :=
      L.isRungArrowPair_unique_of_rungWarp a hrung p q r hpq hr.2
    exact hqr ▸ hr.1

/-- The abstract arrow part in a split-legal ladder is the concrete arrow
through the lifted rung. -/
theorem IsSplitLegal.arrowPart_eq_arrow
    {L : G.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (a : Ladder.Stage kappa) :
    L.arrowPart a = G.arrow (L.warpAt a) (L.liftedRung a) := by
  have hself : G.vertexSet (L.warpAt a) ⊆
      G.roof (G.terminalFrontier (L.warpAt a)) :=
    hlegal.vertexSet_warpAt_subset_roof_terminalFrontier a
  have hrealize : L.ArrowRealizesRung a :=
    L.arrowRealizesRung_of_isWarp_selfRoof a
      (hlegal.warpStages (Ladder.Stage.toExtended a)) hself
      (hlegal.waveRungs a).1
  exact isRungArrowResult_eq L a (hlegal.waveRungs a).1
    (hlegal.exactSuccessorArrows a).1
    (L.isRungArrowResult_arrow a hrealize)

/-- The arrow part is a subwarp of the full successor warp. -/
theorem IsSplitLegal.arrowPart_isWarp
    {L : G.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (a : Ladder.Stage kappa) : G.IsWarp (L.arrowPart a) := by
  intro p hp q hq hpq
  have hpSuccessor : p ∈ L.successorWarp a := by
    rw [(hlegal.exactSuccessorArrows a).2]
    exact Or.inl hp
  have hqSuccessor : q ∈ L.successorWarp a := by
    rw [(hlegal.exactSuccessorArrows a).2]
    exact Or.inl hq
  exact hlegal.warpStages (Ladder.Stage.succExtended a)
    hpSuccessor hqSuccessor hpq

/-- The arrow-only part of a canonical successor is self-roofing before
the optional singleton marker is adjoined. -/
theorem canonicalLadder_arrowPart_selfRoofing
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) :
    G.vertexSet ((canonicalLadder G kappa preferred).arrowPart a) ⊆
      G.roof (G.terminalFrontier
        ((canonicalLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  rw [hlegal.arrowPart_eq_arrow a]
  let s := G.canonicalLadderState kappa preferred
    (Ladder.Stage.toExtended a)
  have hinv : CanonicalRecursionInvariant (G := G)
      (G.ladderSuccessorState
        (extendLadderPreference kappa preferred)) a.1 :=
    canonicalRecursionInvariant_all hNoEnter
      (extendLadderPreference kappa preferred) a.1
  change G.vertexSet
      (G.arrow s.1 (G.liftedLadderRungOfState s)) ⊆
    G.roof (G.terminalFrontier
      (G.arrow s.1 (G.liftedLadderRungOfState s)))
  exact G.canonicalArrow_self_roofing hNoEnter s
    hinv.warp hinv.selfRoof hinv.sourceRoof

/-- In a self-roofing warp, the tail of every directed family edge lies in
the strict roof of the terminal frontier. -/
theorem edge_tail_mem_strictRoof_of_selfRoofing
    {W : Set G.DPath} (hW : G.IsWarp W)
    (hself : G.vertexSet W ⊆ G.roof (G.terminalFrontier W))
    {u v : V} (he : (u, v) ∈ G.pathFamilyEdgeSet W) :
    u ∈ G.strictRoof (G.terminalFrontier W) := by
  obtain ⟨p, hp, hep⟩ := he
  have huSupport : u ∈ p.support :=
    (p.edgeSet_subset_support_prod hep).1
  refine ⟨hself ⟨p, hp, huSupport⟩, ?_⟩
  intro huEssential
  obtain ⟨q, hq, hqTerminal⟩ := huEssential.1
  have hpq : p = q := by
    by_contra hpq
    exact Set.disjoint_left.1 (hW hp hq hpq) huSupport
      (G.terminal_mem_support hqTerminal)
  subst q
  rcases p with p | r
  · exact _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
      p hep (Option.some.inj hqTerminal).symm
  · simp at hqTerminal

/-- A limiting-ladder edge whose head is in the pre-marker arrow roof was
already present in that arrow.  Consequently its tail is in the strict
pre-marker roof. -/
theorem canonicalLadder_limitFamilyEdge_tail_mem_strictRoof_arrowPartFrontier
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) {u v : V}
    (he : (u, v) ∈ G.pathFamilyEdgeSet
      (canonicalLadder G kappa preferred).limitWarp)
    (hv : v ∈ G.roof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a))) :
    u ∈ G.strictRoof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  let c := L.splitSuccessorStage hlegal a
  have hfrontierSubset : G.terminalFrontier (L.arrowPart a) ⊆
      G.terminalFrontier (L.successorWarp a) := by
    rintro z ⟨q, hq, hqz⟩
    refine ⟨q, ?_, hqz⟩
    rw [(hlegal.exactSuccessorArrows a).2]
    exact Or.inl hq
  have hvSuccessor : v ∈
      G.roof (G.terminalFrontier (L.successorWarp a)) :=
    G.roof_mono hfrontierSubset hv
  have hvFrontier : v ∈ G.roof (L.frontier c) := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      G.roof_essential, L.warpAt_splitSuccessorStage hlegal]
    exact hvSuccessor
  have heSuccessor : (u, v) ∈
      G.pathFamilyEdgeSet (L.successorWarp a) := by
    have heAt := hlegal.pathFamilyEdgeSet_of_head_mem_roof_frontier
      c kappa.ord le_rfl c.2.le he hvFrontier
    dsimp only [c] at heAt
    rw [L.warpAt_splitSuccessorStage hlegal] at heAt
    exact heAt
  have heArrow : (u, v) ∈
      G.pathFamilyEdgeSet (L.arrowPart a) := by
    obtain ⟨q, hqSuccessor, heq⟩ := heSuccessor
    rw [(hlegal.exactSuccessorArrows a).2] at hqSuccessor
    rcases hqSuccessor with hqArrow | hqMarker
    · exact ⟨q, hqArrow, heq⟩
    · cases hm : L.marker a with
      | none =>
          simp [markerPathSet, hm] at hqMarker
      | some y =>
          have hq : q = G.trivialPath y := by
            simpa [markerPathSet, hm] using hqMarker
          subst q
          change (u, v) ∈
            (G.trivialPath y).edgeSet at heq
          simpa [DWeb.trivialPath, DirectedPath.Path.trivial,
            DirectedPath.FinitePath.edgeSet,
            DirectedPath.FinitePath.trivial,
            DirectedPath.Walk.edgeSet] using heq
  exact edge_tail_mem_strictRoof_of_selfRoofing
    (hlegal.arrowPart_isWarp a)
    (canonicalLadder_arrowPart_selfRoofing
      preferred hkappa huncountable hNoEnter a) heArrow

/-- A directed edge leaving the strict roof of a cut still ends in its
roof.  The proof uses the essential part of the cut, so it remains valid
when the tail itself is a redundant member of the raw cut. -/
private theorem edge_head_mem_roof_of_tail_mem_strictRoof
    (S : Set V) {u v : V} (huv : G.graph.Adj u v)
    (hu : u ∈ G.strictRoof S) : v ∈ G.roof S := by
  by_contra hv
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (G.not_mem_roof_iff S v).1 hv
  let tail : DirectedPath.Walk G.graph v p.finish :=
    RelationalRoof.castStart G.graph.Adj hpTarget.1 p.walk
  let joined : DirectedPath.Walk G.graph u p.finish := .cons huv tail
  obtain ⟨q, hqsub⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := G.graph.Adj) joined
  let r : DirectedPath.FinitePath G.graph :=
    { start := u
      finish := p.finish
      walk := q.1
      isPath := q.2 }
  have huEssentialRoof : u ∈ G.roof (G.essential S) := by
    rw [G.roof_essential]
    exact hu.1
  obtain ⟨z, hzr, hzEssential⟩ :=
    huEssentialRoof r ⟨rfl, hpTarget.2⟩
  have hzjoined : z ∈ joined.support := hqsub hzr
  simp only [joined, DirectedPath.Walk.support_cons,
    List.mem_cons] at hzjoined
  rcases hzjoined with rfl | hztail
  · exact hu.2 hzEssential
  · have hzp : z ∈ p.support := by
      change z ∈ p.walk.support
      simpa only [tail, RelationalRoof.support_castStart] using hztail
    exact Set.disjoint_left.1 hpAvoid hzp hzEssential.1

/-- Any point of the arrow terminal frontier occurs on the limiting warp.
Thus an off-ladder old vertex which is roofed by the pre-marker frontier is
in its strict roof. -/
theorem canonicalLadder_mem_strictRoof_arrowPartFrontier_of_not_mem_limit
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) {z : V}
    (hzRoof : z ∈ G.roof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a)))
    (hzOff : z ∉ G.vertexSet
      (canonicalLadder G kappa preferred).limitWarp) :
    z ∈ G.strictRoof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  refine ⟨hzRoof, ?_⟩
  intro hzEssential
  obtain ⟨q, hqArrow, hqz⟩ := hzEssential.1
  let c := L.splitSuccessorStage hlegal a
  have hqSuccessor : q ∈ L.successorWarp a := by
    rw [(hlegal.exactSuccessorArrows a).2]
    exact Or.inl hqArrow
  have hqStage : q ∈ L.warpAt c := by
    dsimp only [c]
    rw [L.warpAt_splitSuccessorStage hlegal]
    exact hqSuccessor
  obtain ⟨r, hrLimit, hqr⟩ :=
    CardinalInduction.ControlledSlices.stagesEmbedInLimit_of_limitStages
      G L hlegal.regular hlegal.limitStages c q hqStage
  apply hzOff
  refine ⟨r, hrLimit, ?_⟩
  exact hqr.1 (G.terminal_mem_support hqz)

/-- A target-pure decoded run in any presentation of the same limiting
ladder that starts in the strict pre-marker roof cannot leave the
corresponding closed roof.  This presentation-independent form is needed
for the grounded auxiliary, whose proxy type is a subtype of the split
auxiliary's proxy type. -/
theorem canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
    {I : Type u}
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (J : PopularAuxiliary.Input G I)
    (hJladder : J.ladder.paths =
      (canonicalLadder G kappa preferred).limitWarp)
    (a : Ladder.Stage kappa)
    (p : DirectedPath.FinitePath J.lambda.graph)
    (hs : p.start ∈ J.lambda.source)
    (hpure : J.IsTargetPure p)
    {x y : V}
    (hrun : PopularAuxiliary.Input.RunsFromTo x y
      (J.decodeWalkSteps p.walk))
    (hx : x ∈ G.strictRoof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a))) :
    y ∈ G.roof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  change J.ladder.paths = L.limitWarp at hJladder
  change x ∈ G.strictRoof (G.terminalFrontier (L.arrowPart a)) at hx
  change y ∈ G.roof (G.terminalFrontier (L.arrowPart a))
  apply PopularAuxiliary.Input.RunsFromTo.terminal_mem_roof_of_forwardPairsRecoverStrict
      (L := J) hrun
      (R := G.roof (G.terminalFrontier (L.arrowPart a)))
      (Rs := G.strictRoof (G.terminalFrontier (L.arrowPart a)))
  · exact fun _ hz ↦ hz.1
  · exact hx.1
  · intro _ _ _
    exact hx
  · intro s hsmem hback hsEntry
    have hedge : s.edge ∈ J.familyEdges :=
      J.decodeWalkSteps_backward_on_ladder p hs hsmem hback
    have heLimit : s.edge ∈ G.pathFamilyEdgeSet L.limitWarp := by
      change ∃ q ∈ L.limitWarp, s.edge ∈ q.edgeSet
      change ∃ q ∈ J.ladder.paths, s.edge ∈ q.edgeSet at hedge
      simpa only [hJladder] using hedge
    have htail :=
      canonicalLadder_limitFamilyEdge_tail_mem_strictRoof_arrowPartFrontier
        preferred hkappa huncountable hNoEnter a heLimit
        (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hback]
          using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hback] using htail
  · intro s hsmem hforward hsEntry
    have hadj : G.graph.Adj s.edge.1 s.edge.2 :=
      J.decodeWalkSteps_valid p hs hsmem
    have hhead := edge_head_mem_roof_of_tail_mem_strictRoof
      (G := G) (G.terminalFrontier (L.arrowPart a)) hadj
      (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hforward]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hforward] using hhead
  · intro z hzRoof hzOff
    exact canonicalLadder_mem_strictRoof_arrowPartFrontier_of_not_mem_limit
      preferred hkappa huncountable hNoEnter a hzRoof (by
        intro hzLimit
        apply hzOff.2
        rw [hJladder]
        exact hzLimit)
  · exact J.decodeWalkSteps_forwardPairsRecoverStrict p hpure

/-- A target-pure decoded run that starts in the strict pre-marker roof
cannot leave the corresponding closed roof. -/
theorem canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa)
    (p : DirectedPath.FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.graph)
    (hs : p.start ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.source)
    (hpure :
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).IsTargetPure p)
    {x y : V}
    (hrun : PopularAuxiliary.Input.RunsFromTo x y
      (((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).decodeWalkSteps p.walk))
    (hx : x ∈ G.strictRoof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a))) :
    y ∈ G.roof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  let I := L.splitPopularAuxiliaryInput hlegal
  change p.start ∈ I.lambda.source at hs
  change I.IsTargetPure p at hpure
  change PopularAuxiliary.Input.RunsFromTo x y
    (I.decodeWalkSteps p.walk) at hrun
  change x ∈ G.strictRoof (G.terminalFrontier (L.arrowPart a)) at hx
  change y ∈ G.roof (G.terminalFrontier (L.arrowPart a))
  apply PopularAuxiliary.Input.RunsFromTo.terminal_mem_roof_of_forwardPairsRecoverStrict
      (L := I) hrun
      (R := G.roof (G.terminalFrontier (L.arrowPart a)))
      (Rs := G.strictRoof (G.terminalFrontier (L.arrowPart a)))
  · exact fun _ hz ↦ hz.1
  · exact hx.1
  · intro _ _ _
    exact hx
  · intro s hsmem hback hsEntry
    have hedge : s.edge ∈ I.familyEdges :=
      I.decodeWalkSteps_backward_on_ladder p hs hsmem hback
    have heLimit : s.edge ∈ G.pathFamilyEdgeSet L.limitWarp := by
      change ∃ q ∈ L.limitWarp, s.edge ∈ q.edgeSet at hedge
      exact hedge
    have htail :=
      canonicalLadder_limitFamilyEdge_tail_mem_strictRoof_arrowPartFrontier
        preferred hkappa huncountable hNoEnter a heLimit
        (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hback]
          using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hback] using htail
  · intro s hsmem hforward hsEntry
    have hadj : G.graph.Adj s.edge.1 s.edge.2 :=
      I.decodeWalkSteps_valid p hs hsmem
    have hhead := edge_head_mem_roof_of_tail_mem_strictRoof
      (G := G) (G.terminalFrontier (L.arrowPart a)) hadj
      (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hforward]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hforward] using hhead
  · intro z hzRoof hzOff
    exact canonicalLadder_mem_strictRoof_arrowPartFrontier_of_not_mem_limit
      preferred hkappa huncountable hNoEnter a hzRoof hzOff.2
  · exact I.decodeWalkSteps_forwardPairsRecoverStrict p hpure

/-- A fresh grounded record belongs to the arrow part of its successor,
not to the optional marker singleton. -/
theorem freshGroundRecordPath_mem_arrowPart
    (L : G.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : L.freshInessentialGroundStages) :
    L.freshGroundRecordPath hlegal a ∈ L.arrowPart a.1 := by
  let p := L.freshGroundRecordPath hlegal a
  have hpChosen : L.chosen a.1 = some p :=
    L.chosen_freshGroundRecordPath hlegal a
  obtain ⟨q, hqChosen, hqSuccessor, _hqNotCurrent, _hqNotRecorded⟩ :=
    L.freshInessentialRecordStages_spec hlegal.validBookkeeping a.2.2
  have hqp : q = p := Option.some.inj (hqChosen.symm.trans hpChosen)
  subst q
  have hpSuccessor : p ∈ L.successorWarp a.1 := hqSuccessor.1
  rw [(hlegal.exactSuccessorArrows a.1).2] at hpSuccessor
  rcases hpSuccessor with hpArrow | hpMarker
  · exact hpArrow
  · obtain ⟨r, hrChosen, hrSource⟩ := a.2.1
    have hrp : r = p := Option.some.inj (hrChosen.symm.trans hpChosen)
    subst r
    cases hm : L.marker a.1 with
    | none =>
        simp [markerPathSet, hm] at hpMarker
    | some y =>
        have hp : p = G.trivialPath y := by
          simpa [markerPathSet, hm] using hpMarker
        have hySource : y ∈ G.source := by
          simpa [hp] using hrSource
        have hyRoof : y ∈ G.roof (L.frontier a.1) := by
          rw [L.frontier_eq_essential_terminalFrontier
              hlegal.roofsSourceAtStages,
            G.roof_essential]
          exact hlegal.roofsSourceAtStages
            (Ladder.Stage.toExtended a.1) hySource
        exact (hlegal.marker_not_mem_roof_frontier hm hyRoof).elim

/-- If the fresh grounded record is a ray, its complete support is in the
strict pre-marker roof.  A ray cannot be the finite arrow component whose
terminal supplies an essential point of that frontier. -/
theorem canonicalLadder_freshRay_support_subset_strictRoof_arrowPartFrontier
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : (canonicalLadder G kappa preferred).freshInessentialGroundStages)
    (r : DirectedPath.Ray G.graph)
    (hrecord :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a = .inr r) :
    r.support ⊆ G.strictRoof (G.terminalFrontier
      ((canonicalLadder G kappa preferred).arrowPart a.1)) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  change L.freshGroundRecordPath hlegal a = .inr r at hrecord
  have hrArrow : (Sum.inr r : G.DPath) ∈ L.arrowPart a.1 := by
    rw [← hrecord]
    exact L.freshGroundRecordPath_mem_arrowPart hlegal a
  intro z hzr
  refine ⟨canonicalLadder_arrowPart_selfRoofing
      preferred hkappa huncountable hNoEnter a.1 ⟨.inr r, hrArrow, hzr⟩,
    ?_⟩
  intro hzEssential
  obtain ⟨q, hqArrow, hqz⟩ := hzEssential.1
  have hqr : q = (Sum.inr r : G.DPath) := by
    by_contra hne
    exact Set.disjoint_left.1 (hlegal.arrowPart_isWarp a.1
      hqArrow hrArrow hne) (G.terminal_mem_support hqz) hzr
  subst q
  simp at hqz

/-- A canonical marker retained by the essential limiting warp is outside
the roof of the arrow-only terminal frontier at its birth stage. -/
theorem canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Ladder.Stage kappa} {y : V}
    (hmarker : (canonicalLadder G kappa preferred).marker a = some y)
    (htarget : y ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).targetMarkers) :
    y ∉ G.roof
      (G.terminalFrontier
        ((canonicalLadder G kappa preferred).arrowPart a)) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  change L.marker a = some y at hmarker
  change y ∈ (L.splitPopularAuxiliaryInput hlegal).targetMarkers at htarget
  intro hyRoof
  have hmarkerMem : G.trivialPath y ∈ L.markerPathSet a := by
    simp [markerPathSet, hmarker]
  have hmarkerSuccessor : G.trivialPath y ∈ L.successorWarp a := by
    rw [(hlegal.exactSuccessorArrows a).2]
    exact Or.inr hmarkerMem
  have hyNotArrowVertex : y ∉ G.vertexSet (L.arrowPart a) := by
    rintro ⟨q, hqArrow, hyq⟩
    have hqSuccessor : q ∈ L.successorWarp a := by
      rw [(hlegal.exactSuccessorArrows a).2]
      exact Or.inl hqArrow
    have hqNotMarker : q ∉ L.markerPathSet a := hqArrow.2
    have hqNe : q ≠ G.trivialPath y := by
      intro hq
      exact hqNotMarker (hq ▸ hmarkerMem)
    have hdisjoint := hlegal.warpStages (Ladder.Stage.succExtended a)
      hqSuccessor hmarkerSuccessor hqNe
    exact Set.disjoint_left.1 hdisjoint hyq (by
      rw [G.support_trivialPath]
      exact Set.mem_singleton y)
  have hArrowFrontierSubset :
      G.terminalFrontier (L.arrowPart a) ⊆
        G.terminalFrontier (L.successorWarp a) \ {y} := by
    rintro z ⟨q, hqArrow, hqz⟩
    refine ⟨⟨q, ?_, hqz⟩, ?_⟩
    · rw [(hlegal.exactSuccessorArrows a).2]
      exact Or.inl hqArrow
    · intro hzy
      subst z
      apply hyNotArrowVertex
      refine ⟨q, hqArrow, ?_⟩
      exact G.terminal_mem_support hqz
  have hmarkerInessentialSuccessor :
      G.trivialPath y ∈ G.inessentialPaths (L.successorWarp a) := by
    refine ⟨hmarkerSuccessor, ?_⟩
    rintro ⟨_, z, hzTerminal, hzEssential⟩
    have hzy : z = y := by
      exact (Option.some.inj
        ((G.terminal?_trivialPath y).symm.trans hzTerminal)).symm
    subst z
    exact hzEssential.2
      (G.roof_mono hArrowFrontierSubset hyRoof)
  have hmarkerInessentialLimit :
      G.trivialPath y ∈ G.inessentialPaths L.limitWarp := by
    apply canonicalAccumulated_inessential_mono preferred hNoEnter
      (a := Ladder.Stage.succExtended a)
      (b := Ladder.finalStage kappa)
    · change a.1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 a.2
    · exact hmarkerInessentialSuccessor
  obtain ⟨q, hqEssential, hyq⟩ := htarget.2
  have hmeet :
      ((G.trivialPath y).support ∩ q.support).Nonempty := by
    refine ⟨y, ?_, hyq⟩
    rw [G.support_trivialPath]
    exact Set.mem_singleton y
  exact (G.not_mem_inessentialPaths_of_intersects_essential
      (hlegal.warpStages (Ladder.finalStage kappa)) hqEssential hmeet)
    hmarkerInessentialLimit

/-- Therefore a finite fresh grounded record admitting a target-pure route
to its own retained marker must be *essential* in the pre-marker arrow.
The marker insertion, rather than the rung arrow itself, is what makes this
record inessential in the full successor. -/
theorem canonicalLadder_freshFinite_equalRoute_mem_essential_arrowPart
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : (canonicalLadder G kappa preferred).freshInessentialGroundStages)
    (f : DirectedPath.FinitePath G.graph)
    (hrecord :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a = .inl f)
    (q : DirectedPath.FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.graph)
    (hs : q.start ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.source)
    (hpure :
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).IsTargetPure q)
    {y : V} (hqstart : q.start = .old f.finish)
    (hqfinish : q.finish = .old y)
    (hmarker : (canonicalLadder G kappa preferred).marker a.1 = some y)
    (htarget : y ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).targetMarkers) :
    (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a ∈
      G.essentialWarpPart
        ((canonicalLadder G kappa preferred).arrowPart a.1) := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  change L.freshGroundRecordPath hlegal a = .inl f at hrecord
  change q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source at hs
  change (L.splitPopularAuxiliaryInput hlegal).IsTargetPure q at hpure
  change L.marker a.1 = some y at hmarker
  change y ∈ (L.splitPopularAuxiliaryInput hlegal).targetMarkers at htarget
  have hpArrow : L.freshGroundRecordPath hlegal a ∈
      L.arrowPart a.1 := L.freshGroundRecordPath_mem_arrowPart hlegal a
  by_contra hpEssential
  have hpInessential : L.freshGroundRecordPath hlegal a ∈
      G.inessentialPaths (L.arrowPart a.1) :=
    ⟨hpArrow, hpEssential⟩
  have hxStrict : f.finish ∈
      G.strictRoof (G.terminalFrontier (L.arrowPart a.1)) := by
    apply G.terminal_mem_strictRoof_of_mem_inessentialPaths hpInessential
    rw [hrecord]
    rfl
  let I := L.splitPopularAuxiliaryInput hlegal
  have hrun : PopularAuxiliary.Input.RunsFromTo f.finish y
      (I.decodeWalkSteps q.walk) :=
    I.decodeWalkSteps_runs_from_entry q.walk (by rw [hqstart]; rfl)
      (by rw [hqfinish]; rfl)
  have hyRoof : y ∈ G.roof
      (G.terminalFrontier (L.arrowPart a.1)) :=
    canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter a.1 q hs hpure hrun hxStrict
  exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
    preferred hkappa huncountable hNoEnter hmarker htarget hyRoof

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
