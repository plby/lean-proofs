/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerCollisionSafeStep

/-!
# Finite protected collision-repair states

A state remembers only finitely many safely designated survivor sources.
Their target paths are safely deletable and are literal members of a current
display linkage.  The display also solves the fixed bounded nonsurviving
block, but is not itself declared safely deletable.

Collision candidates are computed from the actual ambient lift of the
display and the canonical survivor intervals, after removing already
designated sources.  One true successor chooses a candidate, adds it by the
certified safe-completion theorem, and re-solves only the bounded residual in
the resulting unhindered deletion.  This gives finite successor iteration;
no limit-union deletion assertion is made.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.RegularSafeCompletion
open _root_.Erdos599.CardinalInduction.SingularSafeDesignatedLinkage
open _root_.Erdos599.CardinalInduction.SingularCertifiedSafeHistory
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- A finite safe history together with the current target linkage for it
and the fixed nonsurviving block. -/
structure FiniteCollisionRepairState
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed') where
  designated : Set V
  designated_finite : designated.Finite
  designated_subset_surviving :
    designated ⊆ T.nativeWholeOwnerSurvivingTerminals R'
  safe : SafeDesignatedLinkage
    (C.ladder.stageWeb R.later.stage) designated
  display : Set (C.ladder.stageWeb R.later.stage).DPath
  display_linkage : IsLinkageBetween
    (C.ladder.stageWeb R.later.stage)
    (designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R')
    (C.ladder.stageWeb R.later.stage).target display
  safe_subset_display : safe.paths ⊆ display

namespace FiniteCollisionRepairState

variable {T : NativePostClosureIntervalTransaction C seed z R}
variable {seed' : Set V} {R' : LimitClosure C seed'}

/-- The current display lifted literally to the ambient web. -/
def ambientDisplay (S : FiniteCollisionRepairState T R') :
    Set Gamma.DPath :=
  SliceSegmentCore.liftStageFamily C.ladder R.later.stage S.display

/-- Canonical survivor sources whose intervals meet the current display,
excluding sources already safely designated. -/
def collisionCandidates
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) : Set V :=
  T.nativeWholeOwnerCollidingSurvivorSources
      R' hlater S.ambientDisplay \
    S.designated

theorem collisionCandidates_subset_surviving
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    S.collisionCandidates hlater ⊆
      T.nativeWholeOwnerSurvivingTerminals R' := by
  intro t ht
  exact T.nativeWholeOwnerCollidingSurvivorSources_subset_surviving
    R' hlater S.ambientDisplay ht.1

theorem collisionCandidate_not_designated
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    {t : V} (ht : t ∈ S.collisionCandidates hlater) :
    t ∉ S.designated :=
  ht.2

/-- The unresolved collision candidates retain the same `kappa` bound as
the full collision family. -/
theorem collisionCandidates_card_le
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage) :
    #(S.collisionCandidates hlater) ≤ kappa := by
  let P := S.ambientDisplay
  let E := SliceSegmentCore.segmentFamily
    (T.nativeWholeOwnerSurvivingTerminalRealization
      R' hlater).toSegmentRealization
  let Bad := T.nativeWholeOwnerCollidingSurvivorFamily R' hlater P
  have hP : IsLinkageBetween Gamma
      (S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R')
      Gamma.target P :=
    SliceDeltaLift.IsLinkageBetween.liftStageFamily S.display_linkage
  have hsourceCard :
      #(S.designated ∪ T.nativeWholeOwnerNonsurvivingTerminals R' : Set V) ≤
        kappa := by
    apply (Cardinal.mk_union_le _ _).trans
    exact Cardinal.add_le_of_le C.capacity_infinite
      (S.designated_finite.countable.le_aleph0.trans C.capacity_infinite)
      (T.nativeWholeOwnerNonsurvivingTerminals_card_le R' hlater)
  have hPvertices : #(Gamma.vertexSet P) ≤ kappa := by
    refine (SingularSafeCarrierCardinal.mk_vertexSet_le_max_initial_aleph0
      hP).trans ?_
    exact max_le hsourceCard C.capacity_infinite
  have hBad : #Bad ≤ #(Gamma.vertexSet P) := by
    change #({q | q ∈ E ∧ ¬ Disjoint q.support (Gamma.vertexSet P)} :
      Set Gamma.DPath) ≤ #(Gamma.vertexSet P)
    exact Gamma.mk_pathsMeeting_le E (Gamma.vertexSet P)
      (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
        R' hlater).isWarp
  apply (Cardinal.mk_subtype_mono Set.sdiff_subset).trans
  exact (RegularProtectedAmbientRebuild.mk_initialSet_le_family
    Gamma Bad).trans (hBad.trans hPvertices)

/-- The empty safe history and the ordinary bounded residual linkage form
the initial finite repair state. -/
theorem exists_initial
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa) :
    Nonempty (FiniteCollisionRepairState T R') := by
  obtain ⟨P, hP⟩ :=
    T.exists_nativeWholeOwnerResidualStageTargetLinkage R' hlater hext
  let G := C.ladder.stageWeb R.later.stage
  have hG : G.IsUnhindered :=
    (nativeCapturedGeometry R).newStage_isUnhindered
  let safe : SafeDesignatedLinkage G ∅ :=
    SingularSafeDesignatedLinkage.empty G hG
  refine ⟨{
    designated := ∅
    designated_finite := Set.finite_empty
    designated_subset_surviving := Set.empty_subset _
    safe := safe
    display := P
    display_linkage := ?_
    safe_subset_display := ?_ }⟩
  · simpa using hP
  · intro p hp
    change p ∈ (∅ : Set G.DPath) at hp
    exact hp.elim

/-- One genuine finite successor.  The selected vertex is an actual current
collision candidate; the entire old safe family is retained literally. -/
theorem exists_successor
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    {t : V} (ht : t ∈ S.collisionCandidates hlater) :
    ∃ S' : FiniteCollisionRepairState T R',
      S'.designated = insert t S.designated ∧
      S.safe.paths ⊆ S'.safe.paths := by
  let G := C.ladder.stageWeb R.later.stage
  let A := T.nativeWholeOwnerNonsurvivingTerminals R'
  have hNorm : G.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized
      C.normalized C.ladder R.later.stage
  have htSurviving : t ∈ T.nativeWholeOwnerSurvivingTerminals R' :=
    S.collisionCandidates_subset_surviving hlater ht
  have hBsource : S.designated ⊆ G.source := by
    intro x hx
    change x ∈ C.ladder.frontier R.later.stage
    exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
      (S.designated_subset_surviving hx).1
  have htSource : t ∈ G.source := by
    change t ∈ C.ladder.frontier R.later.stage
    exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
      htSurviving.1
  have hAsource : A ⊆ G.source := by
    change A ⊆ C.ladder.frontier R.later.stage
    exact T.nativeWholeOwnerNonsurvivingTerminals_subset_oldFrontier R'
  have hAdisjoint : Disjoint A (insert t S.designated) := by
    rw [Set.disjoint_left]
    intro x hxA hxInsert
    rcases hxInsert with rfl | hxB
    · exact hxA.2 htSurviving.2
    · exact hxA.2 (S.designated_subset_surviving hxB).2
  have hGBase : ∀ {x y : V}, G.graph.Adj x y → Gamma.graph.Adj x y := by
    intro x y hxy
    exact C.stageWeb_adj_ambient R.later.stage hxy
  obtain ⟨E, W, hW, hsafeW, _hold, _hnew⟩ :=
    exists_boundedAdditionalLinkage_containing_safeSuccessor
      hext hGBase hNorm S.safe hBsource htSource
      (S.collisionCandidate_not_designated hlater ht)
      hAsource hAdisjoint
      (T.nativeWholeOwnerNonsurvivingTerminals_card_le R' hlater)
  let S' : FiniteCollisionRepairState T R' := {
    designated := insert t S.designated
    designated_finite := S.designated_finite.insert t
    designated_subset_surviving := by
      intro x hx
      rcases hx with rfl | hxOld
      · exact htSurviving
      · exact S.designated_subset_surviving hxOld
    safe := E.extended
    display := W
    display_linkage := hW
    safe_subset_display := hsafeW }
  exact ⟨S', rfl, E.old_subset_paths⟩

/-- A single-step relation for finite repair histories. -/
def IsSuccessor
    (hlater : R.later.stage < R'.later.stage)
    (S S' : FiniteCollisionRepairState T R') : Prop :=
  ∃ t ∈ S.collisionCandidates hlater,
    S'.designated = insert t S.designated ∧
      S.safe.paths ⊆ S'.safe.paths

theorem exists_isSuccessor_of_collisionCandidates_nonempty
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    (hne : (S.collisionCandidates hlater).Nonempty) :
    ∃ S' : FiniteCollisionRepairState T R',
      IsSuccessor hlater S S' := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨S', hdesignated, hretain⟩ :=
    S.exists_successor hlater hext ht
  exact ⟨S', t, ht, hdesignated, hretain⟩

/-- A finite chain of genuine collision-repair successors. -/
inductive ReachesBySuccessors
    (hlater : R.later.stage < R'.later.stage) :
    Nat → FiniteCollisionRepairState T R' →
      FiniteCollisionRepairState T R' → Prop
  | refl (S : FiniteCollisionRepairState T R') :
      ReachesBySuccessors hlater 0 S S
  | step {n : Nat} {S U F : FiniteCollisionRepairState T R'}
      (hSU : IsSuccessor hlater S U)
      (hUF : ReachesBySuccessors hlater n U F) :
      ReachesBySuccessors hlater (Nat.succ n) S F

/-- Every finite repair chain literally retains the safe family at its
initial state. -/
theorem ReachesBySuccessors.safe_subset
    {hlater : R.later.stage < R'.later.stage}
    {n : Nat} {S F : FiniteCollisionRepairState T R'}
    (h : ReachesBySuccessors hlater n S F) :
    S.safe.paths ⊆ F.safe.paths := by
  induction h with
  | refl _ => exact Set.Subset.rfl
  | step hSU _hUF ih =>
      obtain ⟨_t, _ht, _hdesignated, hretain⟩ := hSU
      exact hretain.trans ih

/-- For every finite budget, genuine successors can be taken until the
budget is exhausted or the actual collision-candidate set becomes empty.
This is finite iteration only; it uses no assertion about deletion at an
infinite union. -/
theorem exists_finiteRepair_or_collisionFree
    (S : FiniteCollisionRepairState T R')
    (hlater : R.later.stage < R'.later.stage)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    (n : Nat) :
    ∃ m ≤ n, ∃ F : FiniteCollisionRepairState T R',
      ReachesBySuccessors hlater m S F ∧
        (m = n ∨ F.collisionCandidates hlater = ∅) := by
  induction n generalizing S with
  | zero =>
      exact ⟨0, Nat.le_refl 0, S, ReachesBySuccessors.refl S,
        Or.inl rfl⟩
  | succ n ih =>
      by_cases hempty : S.collisionCandidates hlater = ∅
      · exact ⟨0, Nat.zero_le _, S, ReachesBySuccessors.refl S,
          Or.inr hempty⟩
      · have hne : (S.collisionCandidates hlater).Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨U, hSU⟩ :=
          S.exists_isSuccessor_of_collisionCandidates_nonempty
            hlater hext hne
        obtain ⟨m, hmn, F, hUF, hend⟩ := ih U
        refine ⟨Nat.succ m, Nat.succ_le_succ hmn, F,
          ReachesBySuccessors.step hSU hUF, ?_⟩
        rcases hend with hmnEq | hFempty
        · exact Or.inl (congrArg Nat.succ hmnEq)
        · exact Or.inr hFempty

#print axioms FiniteCollisionRepairState.collisionCandidates_card_le
#print axioms FiniteCollisionRepairState.exists_initial
#print axioms FiniteCollisionRepairState.exists_successor
#print axioms
  FiniteCollisionRepairState.exists_isSuccessor_of_collisionCandidates_nonempty
#print axioms FiniteCollisionRepairState.ReachesBySuccessors.safe_subset
#print axioms FiniteCollisionRepairState.exists_finiteRepair_or_collisionFree

end FiniteCollisionRepairState
end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
