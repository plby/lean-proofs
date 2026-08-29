/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderRoofRecursion
import ErdosProblems.Erdos599.LadderPersistence
import ErdosProblems.Erdos599.LadderStrictChronology

/-!
# Assembly of the canonical legal ladder

This file is the final, deliberately small, assembly layer for the ladder
construction.  The transfinite recursion first produces
`canonicalLadderCore`; `withValidBookkeeping` then installs the independent
ray-preferring choice without changing any geometric datum.  The theorem
below records exactly which construction invariants remain to be supplied by
the successor and limit arguments.  The elementary clauses (initial stage,
wave rungs, roof-maximality, and valid bookkeeping) are discharged here.

Keeping this theorem separate is useful while proving the local invariants:
none of those proofs may assume the desired legal ladder as an input.
-/

noncomputable section

open Cardinal
open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {κ : Cardinal.{u}}

/-- Installing valid bookkeeping does not change `warpAt`. -/
@[simp]
theorem withValidBookkeeping_warpAt (L : G.KappaLadder κ)
    (a : Ladder.Stage κ) :
    L.withValidBookkeeping.warpAt a = L.warpAt a :=
  rfl

/-- Installing valid bookkeeping does not change `successorWarp`. -/
@[simp]
theorem withValidBookkeeping_successorWarp (L : G.KappaLadder κ)
    (a : Ladder.Stage κ) :
    L.withValidBookkeeping.successorWarp a = L.successorWarp a :=
  rfl

/-- Installing valid bookkeeping does not change quotient stages. -/
@[simp]
theorem withValidBookkeeping_stageWeb (L : G.KappaLadder κ)
    (a : Ladder.Stage κ) :
    L.withValidBookkeeping.stageWeb a = L.stageWeb a :=
  rfl

/-- Installing valid bookkeeping does not change ladder frontiers. -/
@[simp]
theorem withValidBookkeeping_frontier (L : G.KappaLadder κ)
    (a : Ladder.Stage κ) :
    L.withValidBookkeeping.frontier a = L.frontier a :=
  rfl

/-- Installing valid bookkeeping does not change marker candidates. -/
@[simp]
theorem withValidBookkeeping_markerCandidates (L : G.KappaLadder κ)
    (a : Ladder.Stage κ) :
    L.withValidBookkeeping.markerCandidates a = L.markerCandidates a :=
  rfl

/-- The accumulated source-roof invariant alone implies that every ladder
frontier is essential.  This is the small quotient calculation used by the
assembly theorem; it is independent of successor chronology. -/
theorem frontiersAreEssential_of_roofsSourceAtStages_assembly
    (L : G.KappaLadder κ) (hroof : L.RoofsSourceAtStages) :
    L.FrontiersAreEssential := by
  intro a
  have hqsource :
      (G.quotient (G.terminalFrontier (L.warpAt a))).source =
        G.essential (G.terminalFrontier (L.warpAt a)) :=
    G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
      (W := L.warpAt a) (hroof (Ladder.Stage.toExtended a))
  have hfrontier :
      L.frontier a = G.essential (G.terminalFrontier (L.warpAt a)) := by
    change
      (G.quotient (G.terminalFrontier (L.warpAt a))).source ∩
          (G.quotient
            (G.terminalFrontier (L.warpAt a))).reachableToTarget =
        G.essential (G.terminalFrontier (L.warpAt a))
    rw [hqsource]
    apply Set.Subset.antisymm Set.inter_subset_left
    intro x hx
    refine ⟨hx, ?_⟩
    obtain ⟨p, hpStart, hpFinish⟩ :=
      G.exists_quotientTargetPath_from_essential
        (G.terminalFrontier (L.warpAt a)) hx
    exact ⟨p, hpStart, hpFinish⟩
  rw [hfrontier, G.essential_idem]

/-- Every marker chosen by the canonical recursion is inserted as its
trivial path in the successor family. -/
theorem canonicalLadder_marker_mem_successorWarp
    (preferred : Ladder.Stage κ → Option V)
    (a : Ladder.Stage κ) {y : V}
    (hy : (canonicalLadder G κ preferred).marker a = some y) :
    G.trivialPath y ∈
      (canonicalLadder G κ preferred).successorWarp a := by
  classical
  have hyState :
      G.ladderMarkerOfState (preferred a)
        (G.canonicalLadderState κ preferred
          (Ladder.Stage.toExtended a)) = some y :=
    hy
  change G.trivialPath y ∈
    G.canonicalLadderAccumulated κ preferred
      (Ladder.Stage.succExtended a)
  simp only [canonicalLadderAccumulated, canonicalLadderState,
    ladderAccumulatedState_succ, ladderSuccessorState]
  split
  · apply Or.inr
    rw [extendLadderPreference_stage]
    change G.trivialPath y ∈
      G.ladderMarkerPathSetOfState (preferred a)
        (G.canonicalLadderState κ preferred
          (Ladder.Stage.toExtended a))
    rw [ladderMarkerPathSetOfState, hyState]
    exact Set.mem_singleton (G.trivialPath y)
  · rename_i hinactive
    have hactive :
        (G.canonicalLadderState κ preferred
          (Ladder.Stage.toExtended a)).2 = true := by
      by_contra hne
      have hfalse :
          (G.canonicalLadderState κ preferred
            (Ladder.Stage.toExtended a)).2 = false := by
        cases hflag : (G.canonicalLadderState κ preferred
            (Ladder.Stage.toExtended a)).2 <;> simp_all
      simp [ladderMarkerOfState, hfalse] at hyState
    exact (hinactive hactive).elim

/-- For the canonical recursion, the positive half of marker freshness is
automatic: every chosen marker is eligible and its trivial path is inserted
at the successor.  Thus only the exhaustion equivalence remains as a local
construction obligation. -/
theorem canonicalLadder_hasFreshMarkers_of_none_iff
    (preferred : Ladder.Stage κ → Option V)
    (hnone : ∀ a : Ladder.Stage κ,
      (canonicalLadder G κ preferred).marker a = none ↔
        (canonicalLadder G κ preferred).markerCandidates a = ∅) :
    (canonicalLadder G κ preferred).HasFreshMarkers := by
  refine ⟨hnone, ?_⟩
  intro a y hy
  constructor
  · change y ∈ G.ladderMarkerCandidatesOfState
      (G.canonicalLadderState κ preferred (Ladder.Stage.toExtended a))
    exact G.ladderMarkerOfState_mem_candidates hy
  · exact canonicalLadder_marker_mem_successorWarp preferred a hy

/-- Canonical markers are pairwise distinct.  A marker path inserted at an
earlier successor grows into every later accumulated family, whereas the
later marker choice is outside that old family by the two roof invariants. -/
theorem canonicalLadder_markersInjective
    (preferred : Ladder.Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G κ preferred).MarkersInjective := by
  let L := canonicalLadder G κ preferred
  have hgeometry : CanonicalLadderGeometry L :=
    canonicalLadder_geometry preferred hNoEnter
  intro a b y ha hb
  rcases lt_trichotomy a b with hab | hab | hba
  · have hsab : Ladder.Stage.succExtended a ≤
        Ladder.Stage.toExtended b := by
      change a.1 + 1 ≤ b.1
      exact (Order.add_one_le_iff).2 hab
    obtain ⟨q, hq, hpq⟩ := hgeometry.grows hsab
      (G.trivialPath y)
      (canonicalLadder_marker_mem_successorWarp preferred a ha)
    let sb := G.canonicalLadderState κ preferred
      (Ladder.Stage.toExtended b)
    have hbState : G.ladderMarkerOfState (preferred b) sb = some y := hb
    have hcontact : G.LadderStateContactsStageSource sb :=
      G.ladderStateContactsStageSource_of_roofs sb
        (hgeometry.roofsSourceAtStages (Ladder.Stage.toExtended b))
        (hgeometry.selfRoofing (Ladder.Stage.toExtended b))
    have hnot := G.ladderMarkerOfState_not_mem_old_vertexSet hcontact hbState
    exfalso
    apply hnot
    refine ⟨q, hq, G.support_mono_of_extends hpq ?_⟩
    rw [G.support_trivialPath]
    exact Set.mem_singleton y
  · exact hab
  · have hsba : Ladder.Stage.succExtended b ≤
        Ladder.Stage.toExtended a := by
      change b.1 + 1 ≤ a.1
      exact (Order.add_one_le_iff).2 hba
    obtain ⟨q, hq, hpq⟩ := hgeometry.grows hsba
      (G.trivialPath y)
      (canonicalLadder_marker_mem_successorWarp preferred b hb)
    let sa := G.canonicalLadderState κ preferred
      (Ladder.Stage.toExtended a)
    have haState : G.ladderMarkerOfState (preferred a) sa = some y := ha
    have hcontact : G.LadderStateContactsStageSource sa :=
      G.ladderStateContactsStageSource_of_roofs sa
        (hgeometry.roofsSourceAtStages (Ladder.Stage.toExtended a))
        (hgeometry.selfRoofing (Ladder.Stage.toExtended a))
    have hnot := G.ladderMarkerOfState_not_mem_old_vertexSet hcontact haState
    exfalso
    apply hnot
    refine ⟨q, hq, G.support_mono_of_extends hpq ?_⟩
    rw [G.support_trivialPath]
    exact Set.mem_singleton y

/-- Final assembly theorem for the canonical construction.

The hypotheses are precisely the non-elementary geometric and persistence
invariants.  In particular there is no maximal-rung hypothesis: the core
chooses `chosenMaximalWave`, so roof-maximality is proved by construction.
There is also no bookkeeping-validity hypothesis: it is supplied by
`withValidBookkeeping`.
-/
theorem canonicalLadderWithBookkeeping_isLegal
    (preferred : Ladder.Stage κ → Option V)
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hexact : (canonicalLadder G κ preferred).HasExactSuccessorArrows)
    (hmarkerExhaustion : ∀ a : Ladder.Stage κ,
      (canonicalLadder G κ preferred).marker a = none ↔
        (canonicalLadder G κ preferred).markerCandidates a = ∅)
    (hmarks : (canonicalLadder G κ preferred).MarksTimeAfterExhaustion)
    (hhanging : (canonicalLadder G κ preferred).HasHangingProvenance) :
    (canonicalLadder G κ preferred).IsLegal := by
  let L₀ := G.canonicalLadderCore κ preferred
  let L := canonicalLadder G κ preferred
  have hgeometry : CanonicalLadderGeometry L :=
    canonicalLadder_geometry preferred hNoEnter
  have hstrict : L.HasStrictFrontierChronology :=
    canonicalLadder_hasStrictFrontierChronology preferred hNoEnter
  have hcurrent : L.CurrentInessentialPersists :=
    canonicalLadder_currentInessentialPersists preferred hNoEnter
  have hrecorded : L.RecordedPathsPersist :=
    canonicalLadder_recordedPathsPersist preferred hNoEnter
  have hinitial : L.HasInitialStage := by
    change (G.canonicalLadderCore κ preferred).HasInitialStage
    exact G.ladderAccumulated_zero κ _
  have hwave : L.HasWaveRungs := by
    intro a
    exact ((G.canonicalLadderCore κ preferred).stageWeb a)
      |>.chosenMaximalWave.property
  have hmax : L.HasRoofMaximalRungs := by
    exact canonicalLadder_withValidBookkeeping_hasRoofMaximalRungs preferred
  have hvalid : L.HasValidBookkeeping := by
    exact L₀.withValidBookkeeping_hasValidBookkeeping
  have hfresh : L.HasFreshMarkers :=
    canonicalLadder_hasFreshMarkers_of_none_iff preferred hmarkerExhaustion
  have hinjective : L.MarkersInjective :=
    canonicalLadder_markersInjective preferred hNoEnter
  have hessential : L.FrontiersAreEssential :=
    L.frontiersAreEssential_of_roofsSourceAtStages_assembly
      hgeometry.roofsSourceAtStages
  exact
    { regular := hκ
      uncountable := hκu
      initialStage := hinitial
      limitStages := hgeometry.limitStages
      warpStages := hgeometry.warpStages
      waveRungs := hwave
      roofMaximalRungs := hmax
      exactSuccessorArrows := hexact
      freshMarkers := hfresh
      markersInjective := hinjective
      marksTime := hmarks
      validBookkeeping := hvalid
      hangingProvenance := hhanging
      recordedPathsPersist := hrecorded
      currentInessentialPersists := hcurrent
      roofsSourceAtStages := hgeometry.roofsSourceAtStages
      frontiersEssential := hessential
      frontierChronology := hgeometry.frontierChronology
      strictFrontierChronology := hstrict }

/-- Existential form of the checked canonical assembly.  The second
conjunct makes the maximal-rung output explicit for the regular-cardinal
and halfway arguments. -/
theorem exists_legalLadder_with_maximalRungs_of_invariants
    (preferred : Ladder.Stage κ → Option V)
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hexact : (canonicalLadder G κ preferred).HasExactSuccessorArrows)
    (hmarkerExhaustion : ∀ a : Ladder.Stage κ,
      (canonicalLadder G κ preferred).marker a = none ↔
        (canonicalLadder G κ preferred).markerCandidates a = ∅)
    (hmarks : (canonicalLadder G κ preferred).MarksTimeAfterExhaustion)
    (hhanging : (canonicalLadder G κ preferred).HasHangingProvenance) :
    ∃ L : G.KappaLadder κ, L.IsLegal ∧ L.HasRoofMaximalRungs := by
  let L := canonicalLadder G κ preferred
  have hlegal : L.IsLegal := canonicalLadderWithBookkeeping_isLegal preferred
    hκ hκu hNoEnter hexact hmarkerExhaustion hmarks hhanging
  exact ⟨L, hlegal, hlegal.roofMaximalRungs⟩

end KappaLadder
end DWeb
end Erdos599
