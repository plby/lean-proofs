/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.LadderBookkeepingChoice
import ErdosProblems.Erdos599.Normalization
import ErdosProblems.Erdos599.QuotientRoofTransport

/-!
# Scheduled markers in the canonical ladder

This file records the exact consequence of the preferred-marker stream used
by the canonical ladder recursion.  At an active stage, an eligible preferred
vertex is selected.  Every selected vertex is then inserted as a singleton
path in the successor family, hence belongs to its terminal frontier and to
the roof of that frontier.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

universe u

namespace DWeb.KappaLadder

variable {V : Type u} {G : DWeb V} {κ : Cardinal.{u}}

/-- Reachability is unchanged when a web is trimmed to its essential part. -/
private theorem mem_essentialPart_reachableToTarget_of_mem
    (Q : DWeb V) {x : V} (hx : x ∈ Q.reachableToTarget) :
    x ∈ Q.essentialPart.reachableToTarget := by
  obtain ⟨p, hpStart, hpFinish⟩ := hx
  have hsupport : p.support ⊆ Q.reachableToTarget :=
    Q.finitePath_support_subset_reachableToTarget p hpFinish
  let q : DirectedPath.FinitePath Q.essentialPart.graph :=
    p.restrictGraphOnSupport fun e hu hv ↦ ⟨e, hsupport hu, hsupport hv⟩
  exact ⟨q,
    by simpa only [q, DirectedPath.FinitePath.restrictGraphOnSupport] using hpStart,
    by
      change q.finish ∈ Q.target
      simpa only [q, DirectedPath.FinitePath.restrictGraphOnSupport] using hpFinish⟩

/-- A point outside the current accumulated roof survives in the trimmed
quotient stage and remains target-reachable there. -/
theorem mem_stageVertexSet_of_not_mem_accumulatedRoof
    (L : G.KappaLadder κ) (a : Ladder.Stage κ) {x : V}
    (hx : x ∉ G.roof (G.terminalFrontier (L.warpAt a))) :
    x ∈ L.stageVertexSet a := by
  let T := G.terminalFrontier (L.warpAt a)
  obtain ⟨p, hpTarget, hpAvoid⟩ := (G.not_mem_roof_iff T x).1 hx
  have hdisjoint := Set.disjoint_left.1 hpAvoid
  have hstrict : ∀ {y}, y ∈ p.walk.support → y ∉ G.strictRoof T := by
    intro y hy hyStrict
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      G.graph.Adj p.walk).1 hy with hyeq | hytail
    · have hyx : y = x := hyeq.trans hpTarget.1
      exact hx (hyx ▸ hyStrict.1)
    · have hyne : y ≠ p.start := by
        intro h
        exact p.isPath.rel_head_tail hytail (p.walk.head_support.trans h.symm)
      have hpAvoid' : RelationalRoof.Avoids G.graph.Adj
          p (T \ {p.start}) := by
        intro z hz hzT
        exact hdisjoint hz hzT.1
      have hyNotRoof :=
        RelationalRoof.not_mem_roof_of_later_mem_targetPath
          G.graph.Adj G.target p hpTarget hpAvoid' hy hyne
      exact hyNotRoof hyStrict.1
  have hcommit : ∀ {y}, y ∈ p.walk.support.tail → y ∉ T := by
    intro y hy hyT
    exact hdisjoint (List.mem_of_mem_tail hy) hyT
  let q := G.restrictFinitePathToQuotient T p hstrict hcommit
  have hqReach : x ∈ (G.quotient T).reachableToTarget := by
    refine ⟨q, ?_, ?_⟩
    · change p.start = x
      exact hpTarget.1
    · change p.finish ∈ G.target
      exact hpTarget.2
  refine ⟨mem_essentialPart_reachableToTarget_of_mem (G.quotient T) hqReach, ?_⟩
  exact fun hxStrict ↦ hx hxStrict.1

/-- Under the accumulated separation invariant, every source of the
trimmed quotient stage is already in the current accumulated roof. -/
private theorem stageWeb_source_subset_accumulatedRoof
    (L : G.KappaLadder κ) (hroof : L.RoofsSourceAtStages)
    (a : Ladder.Stage κ) :
    (L.stageWeb a).source ⊆
      G.roof (G.terminalFrontier (L.warpAt a)) := by
  let T := G.terminalFrontier (L.warpAt a)
  have hsource : G.source ⊆ G.roof T :=
    hroof (Ladder.Stage.toExtended a)
  have hqsource : (G.quotient T).source = G.essential T := by
    simpa only [T, G.terminalFrontier_trivialPaths] using
      (G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
        (W := G.trivialPath '' T) (by
          simpa only [G.terminalFrontier_trivialPaths] using hsource))
  intro x hx
  exact G.essential_subset_roof T (hqsource ▸ hx.1)

/-- The separation invariant identifies a trimmed quotient source with the
essential terminal frontier of the accumulated family. -/
private theorem frontier_eq_essential_terminalFrontier_schedule
    (L : G.KappaLadder κ) (hroof : L.RoofsSourceAtStages)
    (a : Ladder.Stage κ) :
    L.frontier a = G.essential (G.terminalFrontier (L.warpAt a)) := by
  let T := G.terminalFrontier (L.warpAt a)
  have hsource : G.source ⊆ G.roof T :=
    hroof (Ladder.Stage.toExtended a)
  have hqsource : (G.quotient T).source = G.essential T := by
    simpa only [T, G.terminalFrontier_trivialPaths] using
      (G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
        (W := G.trivialPath '' T) (by
          simpa only [G.terminalFrontier_trivialPaths] using hsource))
  change (G.quotient T).source ∩
      (G.quotient T).reachableToTarget = G.essential T
  rw [hqsource]
  apply Set.Subset.antisymm Set.inter_subset_left
  intro x hx
  refine ⟨hx, ?_⟩
  obtain ⟨p, hpStart, hpFinish⟩ :=
    G.exists_quotientTargetPath_from_essential T hx
  exact ⟨p, hpStart, hpFinish⟩

/-- Consequently the roof of a ladder frontier is exactly the roof of the
full accumulated terminal frontier. -/
private theorem roof_frontier_eq_accumulatedRoof
    (L : G.KappaLadder κ) (hroof : L.RoofsSourceAtStages)
    (a : Ladder.Stage κ) :
    G.roof (L.frontier a) =
      G.roof (G.terminalFrontier (L.warpAt a)) := by
  rw [frontier_eq_essential_terminalFrontier_schedule L hroof a,
    G.roof_essential]

/-- Lifting a rung path through the essential quotient and then into the
ambient web preserves its terminal option. -/
private theorem terminal_liftStagePath_schedule
    (L : G.KappaLadder κ) (a : Ladder.Stage κ)
    (r : (L.stageWeb a).DPath) :
    G.terminal? (L.liftStagePath a r) = (L.stageWeb a).terminal? r := by
  rcases r with r | r <;> rfl

/-- Every rung terminal is an actual terminal of the exact successor
arrow of a legal ladder. -/
private theorem rung_terminalFrontier_subset_successorFrontier
    {L : G.KappaLadder κ} (hwave : L.HasWaveRungs)
    (hexact : L.HasExactSuccessorArrows)
    (hroofs : L.RoofsSourceAtStages) (a : Ladder.Stage κ) :
    (L.stageWeb a).terminalFrontier (L.rung a) ⊆
      G.terminalFrontier (L.successorWarp a) := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := ht
  have hrInitial : r.initial ∈ (L.stageWeb a).source :=
    (hwave a).2.1 ⟨r, hr, rfl⟩
  have hOldRoof :
      G.source ⊆ G.roof (G.terminalFrontier (L.warpAt a)) :=
    hroofs (Ladder.Stage.toExtended a)
  obtain ⟨p, hpEssential, hpTerminal⟩ :=
    G.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      hOldRoof hrInitial
  obtain ⟨q, hq, _hqunique⟩ :=
    (by
      simpa only [arrowPart, Set.mem_sdiff] using
        (hexact a).1.1 p hpEssential.1)
  refine ⟨q, hq.1.1, ?_⟩
  rcases hq.2 with hRay | ⟨z, hpz, hcontinue | hfixed⟩
  · rw [hpTerminal] at hRay
    simp at hRay
  · have hz : z = r.initial := Option.some.inj (hpz.symm.trans hpTerminal)
    obtain ⟨r', hr'Initial, hr'Rung, _hpTerminal, _hextends,
      _hsupport, _hedges, hqTerminal⟩ := hcontinue
    have hrr' : r' = r := by
      apply IsWarp.eq_of_initial_eq (L.stageWeb a) (hwave a).1
        hr'Rung hr
      exact hr'Initial.trans hz
    rw [hqTerminal, hrr', terminal_liftStagePath_schedule, hrt]
  · have hz : z = r.initial := Option.some.inj (hpz.symm.trans hpTerminal)
    exfalso
    apply hfixed.1
    exact ⟨r, hr, hz.symm⟩

/-- Every vertex used by a rung of a legal ladder is roofed by the
immediately following accumulated frontier. -/
private theorem rungVertex_subset_successorRoof
    {L : G.KappaLadder κ} (hG : G.IsNormalized)
    (hwave : L.HasWaveRungs) (hexact : L.HasExactSuccessorArrows)
    (hroofs : L.RoofsSourceAtStages)
    (a : Ladder.Stage κ) :
    (L.stageWeb a).vertexSet (L.rung a) ⊆
      G.roof (G.terminalFrontier (L.successorWarp a)) := by
  let T := G.terminalFrontier (L.warpAt a)
  let Q := G.quotient T
  let R : Set Q.essentialPart.DPath := L.rung a
  let U : Set Q.DPath := Q.liftEssentialPartFamily R
  have hU : Q.IsWave U := Q.isWave_liftEssentialPartFamily (hwave a)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro u v huv hv
    exact (hG huv).1 hv
  intro x hx
  change x ∈ Q.essentialPart.vertexSet R at hx
  obtain ⟨r, hr, hxr⟩ := hx
  have hxU : x ∈ Q.vertexSet U := by
    refine ⟨Q.liftEssentialPartPath r, ⟨r, hr, rfl⟩, ?_⟩
    simpa only [Q.support_liftEssentialPartPath] using hxr
  have hxQRoof : x ∈ Q.roof (Q.terminalFrontier U) :=
    DWeb.IsWave.self_roofing (Γ := Q) hU hxU
  have hxAmbient : x ∈ G.roof ((L.stageWeb a).terminalFrontier (L.rung a)) := by
    have hx' := G.quotientWave_roof_subset_original_roof_general
      hNoEnter hU hxQRoof
    change x ∈ G.roof (Q.terminalFrontier U) at hx'
    rw [show U = Q.liftEssentialPartFamily R from rfl,
      Q.terminalFrontier_liftEssentialPartFamily] at hx'
    change x ∈ G.roof (Q.essentialPart.terminalFrontier R)
    exact hx'
  exact G.roof_mono
    (rung_terminalFrontier_subset_successorFrontier hwave hexact hroofs a)
      hxAmbient

/-- A marker chosen by the canonical recursion is inserted as its trivial
path in the immediately following accumulated family. -/
theorem canonicalLadderCore_trivialPath_mem_successorWarp
    (preferred : Ladder.Stage κ → Option V) (a : Ladder.Stage κ) {x : V}
    (hx : (G.canonicalLadderCore κ preferred).marker a = some x) :
    G.trivialPath x ∈
      (G.canonicalLadderCore κ preferred).successorWarp a := by
  classical
  let s := G.canonicalLadderState κ preferred (Ladder.Stage.toExtended a)
  have hx' : G.ladderMarkerOfState (preferred a) s = some x := hx
  change G.trivialPath x ∈
    G.canonicalLadderAccumulated κ preferred (Ladder.Stage.succExtended a)
  rw [canonicalLadderAccumulated, canonicalLadderState,
    ladderAccumulatedState_succ]
  change G.trivialPath x ∈
    (G.ladderSuccessorState (extendLadderPreference κ preferred) a.1 s).1
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    apply Or.inr
    rw [extendLadderPreference_stage preferred a]
    simp [ladderMarkerPathSetOfState, hx']
  · have hnone : G.ladderMarkerOfState (preferred a) s = none := by
      simp [ladderMarkerOfState, hs]
    rw [hnone] at hx'
    contradiction

/-- A marker chosen by the canonical recursion is a terminal vertex of the
immediately following accumulated family. -/
theorem canonicalLadderCore_marker_mem_successorFrontier
    (preferred : Ladder.Stage κ → Option V) (a : Ladder.Stage κ) {x : V}
    (hx : (G.canonicalLadderCore κ preferred).marker a = some x) :
    x ∈ G.terminalFrontier
      ((G.canonicalLadderCore κ preferred).successorWarp a) := by
  exact ⟨G.trivialPath x,
    canonicalLadderCore_trivialPath_mem_successorWarp preferred a hx,
    G.terminal?_trivialPath x⟩

/-- A marker chosen by the canonical recursion lies in the roof of the
immediately following accumulated frontier. -/
theorem canonicalLadderCore_marker_mem_successorRoof
    (preferred : Ladder.Stage κ → Option V) (a : Ladder.Stage κ) {x : V}
    (hx : (G.canonicalLadderCore κ preferred).marker a = some x) :
    x ∈ G.roof (G.terminalFrontier
      ((G.canonicalLadderCore κ preferred).successorWarp a)) :=
  G.subset_roof _
    (canonicalLadderCore_marker_mem_successorFrontier preferred a hx)

/-- Exact one-stage capture for the preferred stream: if its requested
vertex is eligible at an active stage, it is inserted at that successor. -/
theorem canonicalLadderCore_preferred_trivialPath_mem_successorWarp
    (preferred : Ladder.Stage κ → Option V) (a : Ladder.Stage κ) {x : V}
    (hactive : CanonicalStageActive (G := G) preferred a)
    (hpref : preferred a = some x)
    (heligible :
      x ∈ (G.canonicalLadderCore κ preferred).markerCandidates a) :
    G.trivialPath x ∈
      (G.canonicalLadderCore κ preferred).successorWarp a := by
  apply canonicalLadderCore_trivialPath_mem_successorWarp preferred a
  exact canonicalLadderCore_marker_eq_preferred preferred a hactive hpref
    heligible

/-- Exact one-stage roofing for the preferred stream. -/
theorem canonicalLadderCore_preferred_mem_successorRoof
    (preferred : Ladder.Stage κ → Option V) (a : Ladder.Stage κ) {x : V}
    (hactive : CanonicalStageActive (G := G) preferred a)
    (hpref : preferred a = some x)
    (heligible :
      x ∈ (G.canonicalLadderCore κ preferred).markerCandidates a) :
    x ∈ G.roof (G.terminalFrontier
      ((G.canonicalLadderCore κ preferred).successorWarp a)) := by
  apply canonicalLadderCore_marker_mem_successorRoof preferred a
  exact canonicalLadderCore_marker_eq_preferred preferred a hactive hpref
    heligible

/-- Total capture dichotomy for the preferred stream.  In a normalized web,
once the canonical core has its legal construction laws, every requested
vertex is already under the current accumulated roof or is put under the
successor accumulated roof.  No reachability hypothesis is necessary:
being outside a roof itself supplies a target path avoiding that roof. -/
theorem canonicalLadderCore_preferred_mem_current_or_successorRoof_of_fields
    (preferred : Ladder.Stage κ → Option V)
    (hG : G.IsNormalized)
    (hfresh : (G.canonicalLadderCore κ preferred).HasFreshMarkers)
    (hwave : (G.canonicalLadderCore κ preferred).HasWaveRungs)
    (hexact : (G.canonicalLadderCore κ preferred).HasExactSuccessorArrows)
    (hroofs : (G.canonicalLadderCore κ preferred).RoofsSourceAtStages)
    (a : Ladder.Stage κ) {x : V} (hpref : preferred a = some x) :
    x ∈ G.roof (G.terminalFrontier
        ((G.canonicalLadderCore κ preferred).warpAt a)) ∨
      x ∈ G.roof (G.terminalFrontier
        ((G.canonicalLadderCore κ preferred).successorWarp a)) := by
  let L := (G.canonicalLadderCore κ preferred).withValidBookkeeping
  by_cases hxCurrent :
      x ∈ G.roof (G.terminalFrontier (L.warpAt a))
  · exact Or.inl hxCurrent
  have hxStage : x ∈ L.stageVertexSet a :=
    mem_stageVertexSet_of_not_mem_accumulatedRoof L a hxCurrent
  by_cases hxCandidate : x ∈ L.markerCandidates a
  · have hactive : CanonicalStageActive (G := G) preferred a := by
      by_contra hnotActive
      have hnone : L.marker a = none := by
        change G.ladderMarkerOfState (preferred a)
          (G.canonicalLadderState κ preferred
            (Ladder.Stage.toExtended a)) = none
        rw [Erdos599.DWeb.ladderMarkerOfState.eq_def]
        split
        · rename_i hactive'
          exact (hnotActive hactive').elim
        · rfl
      have hempty : L.markerCandidates a = ∅ :=
        (hfresh.1 a).1 hnone
      rw [hempty] at hxCandidate
      exact hxCandidate
    have hmarker : L.marker a = some x :=
      canonicalLadderCore_marker_eq_preferred preferred a hactive hpref
        hxCandidate
    exact Or.inr
      (canonicalLadderCore_marker_mem_successorRoof preferred a hmarker)
  · have hxUsed :
        x ∈ (L.stageWeb a).source ∪
          (L.stageWeb a).vertexSet (L.rung a) := by
      by_contra hxOutside
      apply hxCandidate
      exact ⟨hxStage, hxOutside⟩
    rcases hxUsed with hxSource | hxRung
    · exact Or.inl
        (stageWeb_source_subset_accumulatedRoof L
          hroofs a hxSource)
    · exact Or.inr
        (rungVertex_subset_successorRoof hG hwave hexact hroofs a hxRung)

/-- Compatibility wrapper for a legacy legal ladder. -/
theorem canonicalLadderCore_preferred_mem_current_or_successorRoof
    (preferred : Ladder.Stage κ → Option V)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore κ preferred).withValidBookkeeping.IsLegal)
    (a : Ladder.Stage κ) {x : V} (hpref : preferred a = some x) :
    x ∈ G.roof (G.terminalFrontier
        ((G.canonicalLadderCore κ preferred).warpAt a)) ∨
      x ∈ G.roof (G.terminalFrontier
        ((G.canonicalLadderCore κ preferred).successorWarp a)) := by
  exact canonicalLadderCore_preferred_mem_current_or_successorRoof_of_fields
    preferred hG hL.freshMarkers hL.waveRungs hL.exactSuccessorArrows
      hL.roofsSourceAtStages a hpref

/-- Geometric scheduling form: deferred and legacy bookkeeping use the
same canonical accumulated families, so limit-roof capture needs only the
construction fields that occur in the proof. -/
theorem canonicalLadderCore_preferred_mem_limitRoof_of_fields
    (preferred : Ladder.Stage κ → Option V)
    (hG : G.IsNormalized)
    (hfresh : (G.canonicalLadderCore κ preferred).HasFreshMarkers)
    (hwave : (G.canonicalLadderCore κ preferred).HasWaveRungs)
    (hexact : (G.canonicalLadderCore κ preferred).HasExactSuccessorArrows)
    (hroofs : (G.canonicalLadderCore κ preferred).RoofsSourceAtStages)
    (a b : Ladder.Stage κ) (hab : b.1 = a.1 + 1) {x : V}
    (hpref : preferred a = some x) :
    x ∈ (G.canonicalLadderCore κ preferred).limitRoof := by
  let L := G.canonicalLadderCore κ preferred
  have hwarp : L.warpAt b = L.successorWarp a := by
    apply congrArg L.accumulated
    apply Subtype.ext
    exact hab
  rcases canonicalLadderCore_preferred_mem_current_or_successorRoof_of_fields
      preferred hG hfresh hwave hexact hroofs a hpref with
      hxCurrent | hxSuccessor
  · apply Set.mem_iUnion.2
    refine ⟨a, ?_⟩
    change x ∈ G.roof (L.frontier a)
    rw [roof_frontier_eq_accumulatedRoof L hroofs a]
    exact hxCurrent
  · apply Set.mem_iUnion.2
    refine ⟨b, ?_⟩
    change x ∈ G.roof (L.frontier b)
    rw [roof_frontier_eq_accumulatedRoof L hroofs b, hwarp]
    exact hxSuccessor

/-- A preferred request whose successor is still an ordinary stage is
captured by the union of the canonical ladder's frontier roofs. -/
theorem canonicalLadderCore_preferred_mem_limitRoof
    (preferred : Ladder.Stage κ → Option V)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore κ preferred).withValidBookkeeping.IsLegal)
    (a b : Ladder.Stage κ) (hab : b.1 = a.1 + 1) {x : V}
    (hpref : preferred a = some x) :
    x ∈ (G.canonicalLadderCore κ preferred).limitRoof := by
  let L := (G.canonicalLadderCore κ preferred).withValidBookkeeping
  have hwarp : L.warpAt b = L.successorWarp a := by
    apply congrArg L.accumulated
    apply Subtype.ext
    exact hab
  rcases canonicalLadderCore_preferred_mem_current_or_successorRoof
      preferred hG hL a hpref with hxCurrent | hxSuccessor
  · apply Set.mem_iUnion.2
    refine ⟨a, ?_⟩
    change x ∈ G.roof (L.frontier a)
    rw [roof_frontier_eq_accumulatedRoof L hL.roofsSourceAtStages a]
    exact hxCurrent
  · apply Set.mem_iUnion.2
    refine ⟨b, ?_⟩
    change x ∈ G.roof (L.frontier b)
    rw [roof_frontier_eq_accumulatedRoof L hL.roofsSourceAtStages b,
      hwarp]
    exact hxSuccessor

/-- If the ordinal successor of `a` is still below `κ`, a marker at `a` is
already roofed by the ladder frontier at that successor stage.  The only
global input is the exact accumulated-stage separation invariant. -/
theorem canonicalLadderCore_marker_mem_successorStageFrontierRoof
    (preferred : Ladder.Stage κ → Option V)
    (hroof :
      (G.canonicalLadderCore κ preferred).RoofsSourceAtStages)
    (a b : Ladder.Stage κ) (hab : b.1 = a.1 + 1) {x : V}
    (hx : (G.canonicalLadderCore κ preferred).marker a = some x) :
    x ∈ G.roof ((G.canonicalLadderCore κ preferred).frontier b) := by
  let L := G.canonicalLadderCore κ preferred
  have hwarp : L.warpAt b = L.successorWarp a := by
    apply congrArg L.accumulated
    apply Subtype.ext
    exact hab
  rw [frontier_eq_essential_terminalFrontier_schedule L hroof b,
    G.roof_essential, hwarp]
  exact canonicalLadderCore_marker_mem_successorRoof preferred a hx

/-- Eventual roofing of a chosen marker.  Once its successor is an ordinary
stage, frontier chronology propagates its roof membership to every later
ordinary stage. -/
theorem canonicalLadderCore_marker_mem_laterFrontierRoof
    (preferred : Ladder.Stage κ → Option V)
    (hroof :
      (G.canonicalLadderCore κ preferred).RoofsSourceAtStages)
    (hchron :
      (G.canonicalLadderCore κ preferred).HasFrontierChronology)
    (a b c : Ladder.Stage κ) (hab : b.1 = a.1 + 1) (hbc : b ≤ c)
    {x : V}
    (hx : (G.canonicalLadderCore κ preferred).marker a = some x) :
    x ∈ G.roof ((G.canonicalLadderCore κ preferred).frontier c) := by
  have hxb := canonicalLadderCore_marker_mem_successorStageFrontierRoof
    preferred hroof a b hab hx
  rcases hbc.lt_or_eq with hbc | rfl
  · exact G.roof_cut (hchron hbc) hxb
  · exact hxb

/-- Scheduled eventual roofing: an eligible requested marker at an active
stage is roofed by every frontier from the following ordinary stage on. -/
theorem canonicalLadderCore_preferred_mem_laterFrontierRoof
    (preferred : Ladder.Stage κ → Option V)
    (hroof :
      (G.canonicalLadderCore κ preferred).RoofsSourceAtStages)
    (hchron :
      (G.canonicalLadderCore κ preferred).HasFrontierChronology)
    (a b c : Ladder.Stage κ) (hab : b.1 = a.1 + 1) (hbc : b ≤ c)
    {x : V}
    (hactive : CanonicalStageActive (G := G) preferred a)
    (hpref : preferred a = some x)
    (heligible :
      x ∈ (G.canonicalLadderCore κ preferred).markerCandidates a) :
    x ∈ G.roof ((G.canonicalLadderCore κ preferred).frontier c) := by
  apply canonicalLadderCore_marker_mem_laterFrontierRoof preferred hroof
    hchron a b c hab hbc
  exact canonicalLadderCore_marker_eq_preferred preferred a hactive hpref
    heligible

end DWeb.KappaLadder

end Erdos599
