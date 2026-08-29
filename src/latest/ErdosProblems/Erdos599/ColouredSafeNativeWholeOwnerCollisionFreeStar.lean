/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerFiniteCollisionRepair

/-!
# Completing the native whole-owner star at a collision-free finite state

The display of a finite collision-repair state links its safely designated
survivor sources and every nonsurviving old terminal to the ambient target.
The remaining canonical interval family is restricted to survivor sources
which are not designated.  If the actual collision-candidate set is empty,
this restricted family is carrier-disjoint from the display.

Their union therefore is an honest finite-character continuation whose
initial set is the complete terminal frontier of the old row.  Starring the
old row with this continuation retains every old initial and has no unmatched
old terminal.  The conclusion is conditional on actual candidate emptiness;
no termination or limit-safety assertion is made.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.RegularSliceSurvivors
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction
namespace FiniteCollisionRepairState

variable {T : NativePostClosureIntervalTransaction C seed z R}
variable {seed' : Set V} {R' : LimitClosure C seed'}

/-- Canonical later-frontier intervals for precisely the survivor sources
which are not already represented by the safely designated display. -/
def undesignatedSurvivorFamily
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) : Set Gamma.DPath :=
  {q | q ∈ SliceSegmentCore.segmentFamily
      (T.nativeWholeOwnerSurvivingTerminalRealization
        R' hlater).toSegmentRealization ∧
    q.initial ∉ S.designated}

theorem undesignatedSurvivorFamily_subset
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    S.undesignatedSurvivorFamily hlater ⊆
      SliceSegmentCore.segmentFamily
        (T.nativeWholeOwnerSurvivingTerminalRealization
          R' hlater).toSegmentRealization := by
  intro q hq
  exact hq.1

/-- The restricted canonical family starts at exactly the undesignated
surviving old terminals. -/
theorem undesignatedSurvivorFamily_initialSet
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.initialSet (S.undesignatedSurvivorFamily hlater) =
      T.nativeWholeOwnerSurvivingTerminals R' \ S.designated := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    refine ⟨?_, hq.2⟩
    rw [← (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).initialSet_eq]
    exact ⟨q, hq.1, rfl⟩
  · rintro x ⟨hxSurviving, hxNotDesignated⟩
    have hxInitial : x ∈ Gamma.initialSet
        (SliceSegmentCore.segmentFamily
          (T.nativeWholeOwnerSurvivingTerminalRealization
            R' hlater).toSegmentRealization) := by
      rw [(T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
        R' hlater).initialSet_eq]
      exact hxSurviving
    obtain ⟨q, hq, hqx⟩ := hxInitial
    refine ⟨q, ⟨hq, ?_⟩, hqx⟩
    intro hqDesignated
    exact hxNotDesignated (hqx ▸ hqDesignated)

/-- The ambient display is the literal lift of its stage linkage. -/
theorem ambientDisplay_isLinkageBetween
    (S : FiniteCollisionRepairState T R') :
    IsLinkageBetween Gamma
      (S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R')
      Gamma.target S.ambientDisplay :=
  SliceDeltaLift.IsLinkageBetween.liftStageFamily S.display_linkage

theorem displaySources_subset_oldTerminalFrontier
    (S : FiniteCollisionRepairState T R') :
    S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R' ⊆
      Gamma.terminalFrontier T.nativeWholeOwnerInterval := by
  rintro x (hxDesignated | hxResidual)
  · exact (S.designated_subset_surviving hxDesignated).1
  · exact hxResidual.1

theorem displaySources_subset_oldFrontier
    (S : FiniteCollisionRepairState T R') :
    S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R' ⊆
      C.ladder.frontier R.later.stage := by
  exact S.displaySources_subset_oldTerminalFrontier.trans
    T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset

/-- The lifted display meets the old roof exactly in its displayed source
set. -/
theorem vertexSet_ambientDisplay_inter_oldRoof
    (S : FiniteCollisionRepairState T R') :
    Gamma.vertexSet S.ambientDisplay ∩
        (nativeCapturedGeometry R).outerRoof =
      S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R' := by
  exact vertexSet_liftResidualStageFamily_inter_oldRoof
    S.displaySources_subset_oldFrontier S.display_linkage

/-- Every display path is star-compatible with the old normalized row. -/
theorem ambientDisplay_starCompatible
    (S : FiniteCollisionRepairState T R') :
    Gamma.StarCompatible T.nativeWholeOwnerInterval S.ambientDisplay := by
  have hP : IsLinkageBetween Gamma
      (S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R')
      Gamma.target S.ambientDisplay :=
    S.ambientDisplay_isLinkageBetween
  intro p hp q hq x hxp hxq
  have hxOldRoof : x ∈ (nativeCapturedGeometry R).outerRoof :=
    T.nativeWholeOwnerInterval_vertices_subset_capturedRoof ⟨p, hp, hxp⟩
  have hxDisplay : x ∈ Gamma.vertexSet S.ambientDisplay := ⟨q, hq, hxq⟩
  have hxA : x ∈
      S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R' := by
    rw [← S.vertexSet_ambientDisplay_inter_oldRoof]
    exact ⟨hxDisplay, hxOldRoof⟩
  constructor
  · apply T.nativeWholeOwnerInterval_meetsOnlyAtTerminal p hp x hxp
    exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
      (S.displaySources_subset_oldTerminalFrontier hxA)
  · obtain ⟨f, rfl, _hends, hsource⟩ := hP.endpointPure q hq
    have hxSource : x ∈ f.support ∩
        (S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R') :=
      ⟨hxq, hxA⟩
    rw [hsource] at hxSource
    exact (Set.mem_singleton_iff.mp hxSource).symm

/-- At a collision-free state, every undesignated survivor interval avoids
the complete ambient display. -/
theorem undesignatedSurvivorFamily_disjoint_ambientDisplay
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hfree : S.collisionCandidates hlater = ∅) :
    Disjoint
      (Gamma.vertexSet (S.undesignatedSurvivorFamily hlater))
      (Gamma.vertexSet S.ambientDisplay) := by
  rw [Set.disjoint_left]
  intro x hxSurvivor hxDisplay
  obtain ⟨q, hq, hxq⟩ := hxSurvivor
  have hqBad : q ∈ T.nativeWholeOwnerCollidingSurvivorFamily
      R' hlater S.ambientDisplay := by
    refine ⟨hq.1, Set.not_disjoint_iff.mpr ?_⟩
    exact ⟨x, hxq, hxDisplay⟩
  have hqCandidate : q.initial ∈ S.collisionCandidates hlater :=
    ⟨⟨q, hqBad, rfl⟩, hq.2⟩
  rw [hfree] at hqCandidate
  exact hqCandidate

/-- The collision-free continuation: target paths for designated and
nonsurviving terminals, together with canonical intervals for every other
survivor. -/
def collisionFreeContinuation
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) : Set Gamma.DPath :=
  S.ambientDisplay ∪ S.undesignatedSurvivorFamily hlater

theorem collisionFreeContinuation_isWarp
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hfree : S.collisionCandidates hlater = ∅) :
    Gamma.IsWarp (S.collisionFreeContinuation hlater) := by
  let E := SliceSegmentCore.segmentFamily
    (T.nativeWholeOwnerSurvivingTerminalRealization
      R' hlater).toSegmentRealization
  have hE : Gamma.IsWarp E :=
    (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).isWarp
  have hdisjoint : Disjoint
      (Gamma.vertexSet (S.undesignatedSurvivorFamily hlater))
      (Gamma.vertexSet S.ambientDisplay) :=
    S.undesignatedSurvivorFamily_disjoint_ambientDisplay hlater hfree
  intro p hp q hq hpq
  rcases hp with hpDisplay | hpSurvivor <;>
      rcases hq with hqDisplay | hqSurvivor
  · exact S.ambientDisplay_isLinkageBetween.isWarp
      hpDisplay hqDisplay hpq
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.1 hdisjoint
      ⟨q, hqSurvivor, hxq⟩ ⟨p, hpDisplay, hxp⟩
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.1 hdisjoint
      ⟨p, hpSurvivor, hxp⟩ ⟨q, hqDisplay, hxq⟩
  · exact hE hpSurvivor.1 hqSurvivor.1 hpq

theorem collisionFreeContinuation_finiteCharacter
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.HasFiniteCharacter (S.collisionFreeContinuation hlater) := by
  intro q hq
  rcases hq with hqDisplay | hqSurvivor
  · exact S.ambientDisplay_isLinkageBetween.finiteCharacter hqDisplay
  · exact (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).finiteCharacter hqSurvivor.1

/-- Every old-row terminal, and no other vertex, is an initial of the
collision-free continuation. -/
theorem collisionFreeContinuation_initialSet
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.initialSet (S.collisionFreeContinuation hlater) =
      Gamma.terminalFrontier T.nativeWholeOwnerInterval := by
  rw [collisionFreeContinuation, Gamma.initialSet_union,
    S.ambientDisplay_isLinkageBetween.initialSet_eq,
    S.undesignatedSurvivorFamily_initialSet hlater]
  apply Set.Subset.antisymm
  · rintro x ((hxDesignated | hxResidual) | hxSurviving)
    · exact (S.designated_subset_surviving hxDesignated).1
    · exact hxResidual.1
    · exact hxSurviving.1.1
  · intro x hxOld
    by_cases hxSurvivingSource : x ∈ survivorSources Gamma C.ladder
        R.later.stage R'.later.stage
    · have hxSurviving : x ∈ T.nativeWholeOwnerSurvivingTerminals R' :=
        ⟨hxOld, hxSurvivingSource⟩
      by_cases hxDesignated : x ∈ S.designated
      · exact Or.inl (Or.inl hxDesignated)
      · exact Or.inr ⟨hxSurviving, hxDesignated⟩
    · exact Or.inl (Or.inr ⟨hxOld, hxSurvivingSource⟩)

theorem collisionFreeContinuation_starCompatible
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.StarCompatible T.nativeWholeOwnerInterval
      (S.collisionFreeContinuation hlater) := by
  intro p hp q hq x hxp hxq
  rcases hq with hqDisplay | hqSurvivor
  · exact S.ambientDisplay_starCompatible p hp q hqDisplay x hxp hxq
  · exact T.nativeWholeOwnerSurvivingTerminalFamily_starCompatible
      R' hlater p hp q hqSurvivor.1 x hxp hxq

/-- The complete collision-free star of the whole old normalized row. -/
noncomputable def collisionFreeCompleteStar
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) : Set Gamma.DPath :=
  Gamma.star (S.collisionFreeContinuation_starCompatible hlater)

theorem collisionFreeCompleteStar_isWarp
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hfree : S.collisionCandidates hlater = ∅) :
    Gamma.IsWarp (S.collisionFreeCompleteStar hlater) := by
  apply Gamma.isWarp_star
    T.nativeWholeOwnerInterval_isLinkageBetween.isWarp
    (S.collisionFreeContinuation_isWarp hlater hfree)

theorem collisionFreeCompleteStar_finiteCharacter
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.HasFiniteCharacter (S.collisionFreeCompleteStar hlater) := by
  apply SliceSpliceSource.hasFiniteCharacter_star
    T.nativeWholeOwnerInterval_isLinkageBetween.finiteCharacter
    (S.collisionFreeContinuation_finiteCharacter hlater)

/-- The complete star retains exactly every old-row initial. -/
theorem collisionFreeCompleteStar_initialSet
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.initialSet (S.collisionFreeCompleteStar hlater) =
      (nativeCapturedGeometry R).oldSlice := by
  rw [collisionFreeCompleteStar, SliceSpliceSource.initialSet_star_eq,
    T.nativeWholeOwnerInterval_isLinkageBetween.initialSet_eq]

/-- Since every old terminal is matched, the complete star exposes exactly
the terminals of the combined continuation. -/
theorem collisionFreeCompleteStar_terminalFrontier
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hfree : S.collisionCandidates hlater = ∅) :
    Gamma.terminalFrontier (S.collisionFreeCompleteStar hlater) =
      Gamma.terminalFrontier S.ambientDisplay ∪
        Gamma.terminalFrontier (S.undesignatedSurvivorFamily hlater) := by
  let U := S.collisionFreeContinuation hlater
  let hcompat := S.collisionFreeContinuation_starCompatible hlater
  have hbase := terminalFrontier_star_eq_union_unmatched
    T.nativeWholeOwnerInterval_isLinkageBetween.finiteCharacter
    (S.collisionFreeContinuation_isWarp hlater hfree)
    hcompat (by
      rw [S.collisionFreeContinuation_initialSet hlater])
  have hunmatched :
      Gamma.terminalFrontier T.nativeWholeOwnerInterval \
          Gamma.initialSet U = ∅ := by
    rw [S.collisionFreeContinuation_initialSet hlater]
    exact Set.sdiff_self
  rw [hunmatched, Set.union_empty] at hbase
  simpa only [collisionFreeCompleteStar, U, hcompat,
    Set.union_empty, collisionFreeContinuation,
    Gamma.terminalFrontier_union] using hbase

theorem collisionFreeCompleteStar_terminalFrontier_subset
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hfree : S.collisionCandidates hlater = ∅) :
    Gamma.terminalFrontier (S.collisionFreeCompleteStar hlater) ⊆
      Gamma.target ∪ C.ladder.frontier R'.later.stage := by
  rw [S.collisionFreeCompleteStar_terminalFrontier hlater hfree]
  apply Set.union_subset
  · exact S.ambientDisplay_isLinkageBetween.terminalFrontier_subset.trans
      Set.subset_union_left
  · rintro x ⟨q, hq, hqx⟩
    apply Set.subset_union_right
    exact (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).terminalFrontier_subset ⟨q, hq.1, hqx⟩

/-- Bundled collision-free output for downstream use. -/
theorem collisionFreeCompleteStar_spec
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hfree : S.collisionCandidates hlater = ∅) :
    Gamma.IsWarp (S.collisionFreeCompleteStar hlater) ∧
      Gamma.HasFiniteCharacter (S.collisionFreeCompleteStar hlater) ∧
      Gamma.initialSet (S.collisionFreeCompleteStar hlater) =
        (nativeCapturedGeometry R).oldSlice ∧
      Gamma.terminalFrontier (S.collisionFreeCompleteStar hlater) =
        Gamma.terminalFrontier S.ambientDisplay ∪
          Gamma.terminalFrontier (S.undesignatedSurvivorFamily hlater) ∧
      Gamma.terminalFrontier (S.collisionFreeCompleteStar hlater) ⊆
        Gamma.target ∪ C.ladder.frontier R'.later.stage := by
  exact ⟨S.collisionFreeCompleteStar_isWarp hlater hfree,
    S.collisionFreeCompleteStar_finiteCharacter hlater,
    S.collisionFreeCompleteStar_initialSet hlater,
    S.collisionFreeCompleteStar_terminalFrontier hlater hfree,
    S.collisionFreeCompleteStar_terminalFrontier_subset hlater hfree⟩

#print axioms FiniteCollisionRepairState.collisionFreeContinuation_initialSet
#print axioms FiniteCollisionRepairState.collisionFreeCompleteStar_isWarp
#print axioms FiniteCollisionRepairState.collisionFreeCompleteStar_terminalFrontier
#print axioms FiniteCollisionRepairState.collisionFreeCompleteStar_spec

end FiniteCollisionRepairState
end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
