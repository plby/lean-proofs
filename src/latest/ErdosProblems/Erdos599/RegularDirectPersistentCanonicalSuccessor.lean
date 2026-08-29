/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPersistentCanonicalSuccessor
import ErdosProblems.Erdos599.RegularDirectInstalledStage

/-!
# Direct persistent/movable successor

This is the proof-method-independent version of `PersistentSplitInput`.
Instead of retaining a strict-roof comparison certificate, it receives the
exact `IsCleanTargetStep` conclusion.  The rest of the successor argument
is unchanged: the persistent track completes its selected coordinates, the
movable clean track preserves target links, and its maverick terminals form
the next small request.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularDirectPersistentCanonicalSuccessor

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

structure DirectPersistentSplitInput
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  baseStage : Ladder.Stage kappa
  base : Set G.DPath
  base_warp : G.IsWarp base
  base_finite : G.HasFiniteCharacter base
  base_initial : G.initialSet base = A
  base_extends : ∀ j (hji : j < i),
    G.ForwardExtension (previous j hji).row base
  base_freezes : ∀ j (hji : j < i),
    completedPart G (previous j hji).row ⊆ completedPart G base

  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_strict : ∀ j (hji : j < i),
    (previous j hji).stageIndex < stageIndex

  slice : RegularCompletedPendingSplice.CleanTargetSlice
    G (G.terminalFrontier (pendingPart G base)) (L.frontier stageIndex)
      (RegularPersistentRequestSplit.persistentPart G L
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base))
  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
  cleanStep : RegularCompletedPendingSplice.IsCleanTargetStep G base
    (slice.target ∪ slice.clean) compatible
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)

  vertices_closed : G.vertexSet
    (RegularCompletedPendingSplice.freezeCompletedStar
      G base (slice.target ∪ slice.clean) compatible) ⊆ Z
  pending_below_roof : G.vertexSet (pendingPart G
    (RegularCompletedPendingSplice.freezeCompletedStar
      G base (slice.target ∪ slice.clean) compatible)) ⊆
      G.roof (L.frontier stageIndex)

  old_pending_boundary : MeetsOnlyAtTerminal G (pendingPart G base)
    (L.frontier stageIndex)
  old_pending_status : ∀ p ∈ pendingPart G base,
    SliceSpliceConstructor.IsStagePrefix G L baseStage p ∨
      ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base,
        G.terminal? p = some x

  clean_links_movable : LinksToTarget G slice.clean
    (RegularPersistentRequestSplit.movablePart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous base))
  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean baseStage stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) < kappa
  cleanMavericks_closed : G.vertexSet
    (ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) ⊆ Z

namespace DirectPersistentSplitInput

/-- Every required old pending component is completed by one of the two
tracks. -/
theorem completes_required
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectPersistentSplitInput G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized)
    {p : G.DPath} (hp : p ∈ pendingPart G S.base) {a : V}
    (hpa : G.terminal? p = some a)
    (ha : a ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous S.base) :
    ∃ q ∈ G.star S.compatible,
      q.initial = p.initial ∧
        SliceSpliceConstructor.ReachesTarget G q := by
  let U := RegularGlobalAdmissibleProvider.requiredPendingTerminals
    G L Sigma Z A request i previous S.base
  by_cases haPersistent : a ∈
      RegularPersistentRequestSplit.persistentPart G L U
  · exact S.slice.exists_completed_starPath hNorm S.compatible hp hpa
      haPersistent
  · have haMovable : a ∈
        RegularPersistentRequestSplit.movablePart G L U :=
      ⟨ha, haPersistent⟩
    have haLeft : a ∈ G.terminalFrontier (pendingPart G S.base) :=
      RegularGlobalAdmissibleProvider.requiredPendingTerminals_subset_terminalFrontier
        ha
    have haCleanInitial : a ∈ G.initialSet S.slice.clean := by
      rw [S.slice.clean_initial]
      exact ⟨haLeft, haPersistent⟩
    obtain ⟨t, htClean, htInitial⟩ := haCleanInitial
    have hcompletedLinks : LinksToTarget G
        (completedPart G S.slice.clean)
        (RegularPersistentRequestSplit.movablePart G L U) :=
      linksToTarget_completedPart hNorm S.clean_links_movable
    obtain ⟨q, hqCompleted, f, hqf, hfpure, _hfsuffix⟩ :=
      hcompletedLinks a haMovable
    have haSupportQ : a ∈ q.support := by
      have haInter : a ∈ f.support ∩
          RegularPersistentRequestSplit.movablePart G L U := by
        rw [hfpure]
        exact Set.mem_singleton a
      rw [hqf]
      exact haInter.1
    have htq : t = q := by
      by_contra htq
      exact Set.disjoint_left.1
        (S.slice.union_warp (Or.inr htClean) (Or.inr hqCompleted.1) htq)
        (htInitial ▸ t.initial_mem_support) haSupportQ
    have htTarget : SliceSpliceConstructor.ReachesTarget G t := by
      rw [htq]
      exact hqCompleted.2
    exact RegularPersistentCanonicalSuccessor.exists_completed_starPath_of_continuation
      S.slice.union_warp S.compatible hp hpa (Or.inr htClean)
        htInitial htTarget

theorem maverickTerminals_subset
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectPersistentSplitInput G L Sigma Z A request i previous) :
    G.terminalFrontier
        (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
          S.slice.clean) ⊆
      L.frontier S.stageIndex ∩ Z := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨S.slice.clean_terminal ⟨p, hp.1, hpx⟩,
    S.cleanMavericks_closed ⟨p, hp, G.terminal_mem_support hpx⟩⟩

/-- Derive the direct installed stage.  This is the same completion and
status argument as the comparison-based adapter, but its clean-step proof
is consumed directly. -/
def toDirectInstalledStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectPersistentSplitInput G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) (hL : L.SliceGeometry) (hA : A ⊆ G.source) :
    RegularDirectInstalledStage.DirectInstalledStage
      G L Sigma Z A request i previous := by
  let nextRequest := G.terminalFrontier
    (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
      S.slice.clean)
  have hpendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G
        (RegularCompletedPendingSplice.freezeCompletedStar G S.base
          (S.slice.target ∪ S.slice.clean) S.compatible)))
      (L.frontier S.stageIndex)
      (pendingPart G
        (RegularCompletedPendingSplice.freezeCompletedStar G S.base
          (S.slice.target ∪ S.slice.clean) S.compatible)) := by
    apply S.slice.pendingPart_freezeCompletedStar_tightLinkageBetween hNorm
    · rw [S.base_initial]
      exact hA
    · exact S.base_finite
    · exact S.old_pending_boundary
    · exact S.cleanStep
    · exact S.installed_star_finite
  have hpendingStatus : ∀ r ∈ pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G S.base
        (S.slice.target ∪ S.slice.clean) S.compatible),
      SliceSpliceConstructor.IsStagePrefix G L S.stageIndex r ∨
        ∃ x ∈ nextRequest, G.terminal? r = some x := by
    apply RegularPersistentCanonicalSuccessor.pendingPart_freezeCompletedStar_status_of_completedExceptions
      hNorm S.base_warp S.slice hL S.cleanIntervals S.compatible
      S.old_pending_status
    intro p hp x hx hpx
    exact S.completes_required hNorm hp hpx hx
  refine
    { baseStage := S.baseStage
      base := S.base
      base_warp := S.base_warp
      base_finite := S.base_finite
      base_initial := S.base_initial
      base_extends := S.base_extends
      base_freezes := S.base_freezes
      stageIndex := S.stageIndex
      stageIndex_mem := S.stageIndex_mem
      index_strict := S.index_strict
      installed := S.slice.target ∪ S.slice.clean
      compatible := S.compatible
      cleanStep := S.cleanStep
      installed_star_finite := S.installed_star_finite
      vertices_closed := S.vertices_closed
      pending_tight := hpendingTight
      pending_below_roof := S.pending_below_roof
      pendingRequest := nextRequest
      pendingRequest_subset := S.maverickTerminals_subset
      pendingRequest_small :=
        (SliceSpliceConstructor.mk_terminalFrontier_le G
          (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
            S.slice.clean)).trans_lt S.cleanMavericks_small
      pending_status := hpendingStatus
      resolves_pending := ?_
      realizes_request := ?_ }
  · intro j hji p hp hrequested
    obtain ⟨q, hqBase, hpq⟩ := (S.base_extends j hji).1 p hp.1
    by_cases hqCompleted : q ∈ completedPart G S.base
    · refine ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base (S.slice.target ∪ S.slice.clean) S.compatible
            hqCompleted, ?_⟩
      exact (G.extends_initial hpq).symm
    · have hqPending : q ∈ pendingPart G S.base :=
        ⟨hqBase, hqCompleted⟩
      have hrequired :
          RegularGlobalAdmissibleProvider.IsRequiredInitial
            G L Sigma Z A request i previous q.initial :=
        Or.inr ⟨j, hji, p, hp, hrequested,
          (G.extends_initial hpq).symm⟩
      obtain ⟨u, huRequired, hqu⟩ :=
        RegularGlobalAdmissibleProvider.exists_mem_requiredPendingTerminals
          S.base_finite hqPending hrequired
      obtain ⟨r, hrStar, hrInitial, hrTarget⟩ :=
        S.completes_required hNorm hqPending hqu huRequired
      refine ⟨r, ⟨Or.inr hrStar, hrTarget⟩, ?_⟩
      exact hrInitial.trans (G.extends_initial hpq).symm
  · intro a haRequest
    have haBase : a.1 ∈ G.initialSet S.base := by
      rw [S.base_initial]
      exact a.2
    obtain ⟨q, hqBase, hqInitial⟩ := haBase
    by_cases hqCompleted : q ∈ completedPart G S.base
    · exact ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base (S.slice.target ∪ S.slice.clean) S.compatible
            hqCompleted,
        hqInitial⟩
    · have hqPending : q ∈ pendingPart G S.base :=
        ⟨hqBase, hqCompleted⟩
      have hrequired :
          RegularGlobalAdmissibleProvider.IsRequiredInitial
            G L Sigma Z A request i previous q.initial :=
        Or.inl ⟨a, haRequest, hqInitial⟩
      obtain ⟨u, huRequired, hqu⟩ :=
        RegularGlobalAdmissibleProvider.exists_mem_requiredPendingTerminals
          S.base_finite hqPending hrequired
      obtain ⟨r, hrStar, hrInitial, hrTarget⟩ :=
        S.completes_required hNorm hqPending hqu huRequired
      exact ⟨r, ⟨Or.inr hrStar, hrTarget⟩,
        hrInitial.trans hqInitial⟩

end DirectPersistentSplitInput

/-- Source-faithful selected-coordinate successor input.  The causal
diagonal request may contain more coordinates than the currently required
set, so the selected target track is not required to equal the persistent
part of that set.  Every required coordinate is nevertheless either
selected or linked by the clean track. -/
structure DirectSelectedSplitInput
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  baseStage : Ladder.Stage kappa
  base : Set G.DPath
  base_warp : G.IsWarp base
  base_finite : G.HasFiniteCharacter base
  base_initial : G.initialSet base = A
  base_extends : ∀ j (hji : j < i),
    G.ForwardExtension (previous j hji).row base
  base_freezes : ∀ j (hji : j < i),
    completedPart G (previous j hji).row ⊆ completedPart G base

  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_strict : ∀ j (hji : j < i),
    (previous j hji).stageIndex < stageIndex

  selected : Set V
  required_subset_left :
    RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous base ⊆
        G.terminalFrontier (pendingPart G base)
  slice : RegularCompletedPendingSplice.CleanTargetSlice
    G (G.terminalFrontier (pendingPart G base)) (L.frontier stageIndex)
      selected
  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
  cleanStep : RegularCompletedPendingSplice.IsCleanTargetStep G base
    (slice.target ∪ slice.clean) compatible
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)

  vertices_closed : G.vertexSet
    (RegularCompletedPendingSplice.freezeCompletedStar
      G base (slice.target ∪ slice.clean) compatible) ⊆ Z
  pending_below_roof : G.vertexSet (pendingPart G
    (RegularCompletedPendingSplice.freezeCompletedStar
      G base (slice.target ∪ slice.clean) compatible)) ⊆
      G.roof (L.frontier stageIndex)

  old_pending_boundary : MeetsOnlyAtTerminal G (pendingPart G base)
    (L.frontier stageIndex)
  old_pending_status : ∀ p ∈ pendingPart G base,
    SliceSpliceConstructor.IsStagePrefix G L baseStage p ∨
      ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base,
        G.terminal? p = some x

  clean_links_unselected : LinksToTarget G slice.clean
    (RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous base \ selected)
  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean baseStage stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) < kappa
  cleanMavericks_closed : G.vertexSet
    (ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) ⊆ Z

namespace DirectSelectedSplitInput

/-- Every required old pending component is completed, independently of
whether its terminal was one of the table's extra selected coordinates. -/
theorem completes_required
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectSelectedSplitInput G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized)
    {p : G.DPath} (hp : p ∈ pendingPart G S.base) {a : V}
    (hpa : G.terminal? p = some a)
    (ha : a ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous S.base) :
    ∃ q ∈ G.star S.compatible,
      q.initial = p.initial ∧
        SliceSpliceConstructor.ReachesTarget G q := by
  by_cases haSelected : a ∈ S.selected
  · exact S.slice.exists_completed_starPath hNorm S.compatible hp hpa
      haSelected
  · have haUnselected : a ∈
        RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous S.base \ S.selected :=
      ⟨ha, haSelected⟩
    have haLeft : a ∈ G.terminalFrontier (pendingPart G S.base) :=
      S.required_subset_left ha
    have haCleanInitial : a ∈ G.initialSet S.slice.clean := by
      rw [S.slice.clean_initial]
      exact ⟨haLeft, haSelected⟩
    obtain ⟨t, htClean, htInitial⟩ := haCleanInitial
    have hcompletedLinks : LinksToTarget G
        (completedPart G S.slice.clean)
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous S.base \ S.selected) :=
      linksToTarget_completedPart hNorm S.clean_links_unselected
    obtain ⟨q, hqCompleted, f, hqf, hfpure, _hfsuffix⟩ :=
      hcompletedLinks a haUnselected
    have haSupportQ : a ∈ q.support := by
      have haInter : a ∈ f.support ∩
          (RegularGlobalAdmissibleProvider.requiredPendingTerminals
            G L Sigma Z A request i previous S.base \ S.selected) := by
        rw [hfpure]
        exact Set.mem_singleton a
      rw [hqf]
      exact haInter.1
    have htq : t = q := by
      by_contra htq
      exact Set.disjoint_left.1
        (S.slice.union_warp (Or.inr htClean) (Or.inr hqCompleted.1) htq)
        (htInitial ▸ t.initial_mem_support) haSupportQ
    have htTarget : SliceSpliceConstructor.ReachesTarget G t := by
      rw [htq]
      exact hqCompleted.2
    exact RegularPersistentCanonicalSuccessor.exists_completed_starPath_of_continuation
      S.slice.union_warp S.compatible hp hpa (Or.inr htClean)
        htInitial htTarget

theorem maverickTerminals_subset
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectSelectedSplitInput G L Sigma Z A request i previous) :
    G.terminalFrontier
        (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
          S.slice.clean) ⊆
      L.frontier S.stageIndex ∩ Z := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨S.slice.clean_terminal ⟨p, hp.1, hpx⟩,
    S.cleanMavericks_closed ⟨p, hp, G.terminal_mem_support hpx⟩⟩

/-- Compile a selected-coordinate input to the recursive installed stage. -/
def toDirectInstalledStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectSelectedSplitInput G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) (hL : L.SliceGeometry) (hA : A ⊆ G.source) :
    RegularDirectInstalledStage.DirectInstalledStage
      G L Sigma Z A request i previous := by
  let nextRequest := G.terminalFrontier
    (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
      S.slice.clean)
  have hpendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G
        (RegularCompletedPendingSplice.freezeCompletedStar G S.base
          (S.slice.target ∪ S.slice.clean) S.compatible)))
      (L.frontier S.stageIndex)
      (pendingPart G
        (RegularCompletedPendingSplice.freezeCompletedStar G S.base
          (S.slice.target ∪ S.slice.clean) S.compatible)) := by
    apply S.slice.pendingPart_freezeCompletedStar_tightLinkageBetween hNorm
    · rw [S.base_initial]
      exact hA
    · exact S.base_finite
    · exact S.old_pending_boundary
    · exact S.cleanStep
    · exact S.installed_star_finite
  have hpendingStatus : ∀ r ∈ pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G S.base
        (S.slice.target ∪ S.slice.clean) S.compatible),
      SliceSpliceConstructor.IsStagePrefix G L S.stageIndex r ∨
        ∃ x ∈ nextRequest, G.terminal? r = some x := by
    apply RegularPersistentCanonicalSuccessor.pendingPart_freezeCompletedStar_status_of_completedExceptions
      hNorm S.base_warp S.slice hL S.cleanIntervals S.compatible
      S.old_pending_status
    intro p hp x hx hpx
    exact S.completes_required hNorm hp hpx hx
  refine
    { baseStage := S.baseStage
      base := S.base
      base_warp := S.base_warp
      base_finite := S.base_finite
      base_initial := S.base_initial
      base_extends := S.base_extends
      base_freezes := S.base_freezes
      stageIndex := S.stageIndex
      stageIndex_mem := S.stageIndex_mem
      index_strict := S.index_strict
      installed := S.slice.target ∪ S.slice.clean
      compatible := S.compatible
      cleanStep := S.cleanStep
      installed_star_finite := S.installed_star_finite
      vertices_closed := S.vertices_closed
      pending_tight := hpendingTight
      pending_below_roof := S.pending_below_roof
      pendingRequest := nextRequest
      pendingRequest_subset := S.maverickTerminals_subset
      pendingRequest_small :=
        (SliceSpliceConstructor.mk_terminalFrontier_le G
          (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
            S.slice.clean)).trans_lt S.cleanMavericks_small
      pending_status := hpendingStatus
      resolves_pending := ?_
      realizes_request := ?_ }
  · intro j hji p hp hrequested
    obtain ⟨q, hqBase, hpq⟩ := (S.base_extends j hji).1 p hp.1
    by_cases hqCompleted : q ∈ completedPart G S.base
    · refine ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base (S.slice.target ∪ S.slice.clean) S.compatible
            hqCompleted, ?_⟩
      exact (G.extends_initial hpq).symm
    · have hqPending : q ∈ pendingPart G S.base :=
        ⟨hqBase, hqCompleted⟩
      have hrequired :
          RegularGlobalAdmissibleProvider.IsRequiredInitial
            G L Sigma Z A request i previous q.initial :=
        Or.inr ⟨j, hji, p, hp, hrequested,
          (G.extends_initial hpq).symm⟩
      obtain ⟨u, huRequired, hqu⟩ :=
        RegularGlobalAdmissibleProvider.exists_mem_requiredPendingTerminals
          S.base_finite hqPending hrequired
      obtain ⟨r, hrStar, hrInitial, hrTarget⟩ :=
        S.completes_required hNorm hqPending hqu huRequired
      refine ⟨r, ⟨Or.inr hrStar, hrTarget⟩, ?_⟩
      exact hrInitial.trans (G.extends_initial hpq).symm
  · intro a haRequest
    have haBase : a.1 ∈ G.initialSet S.base := by
      rw [S.base_initial]
      exact a.2
    obtain ⟨q, hqBase, hqInitial⟩ := haBase
    by_cases hqCompleted : q ∈ completedPart G S.base
    · exact ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base (S.slice.target ∪ S.slice.clean) S.compatible
            hqCompleted,
        hqInitial⟩
    · have hqPending : q ∈ pendingPart G S.base :=
        ⟨hqBase, hqCompleted⟩
      have hrequired :
          RegularGlobalAdmissibleProvider.IsRequiredInitial
            G L Sigma Z A request i previous q.initial :=
        Or.inl ⟨a, haRequest, hqInitial⟩
      obtain ⟨u, huRequired, hqu⟩ :=
        RegularGlobalAdmissibleProvider.exists_mem_requiredPendingTerminals
          S.base_finite hqPending hrequired
      obtain ⟨r, hrStar, hrInitial, hrTarget⟩ :=
        S.completes_required hNorm hqPending hqu huRequired
      exact ⟨r, ⟨Or.inr hrStar, hrTarget⟩,
        hrInitial.trans hqInitial⟩

end DirectSelectedSplitInput

end RegularDirectPersistentCanonicalSuccessor
end CardinalInduction
end Erdos599
