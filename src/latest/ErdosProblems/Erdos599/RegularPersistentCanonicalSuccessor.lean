/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalAdmissibleProvider

/-!
# The persistent/movable canonical regular successor

A right-tight target-linking slice cannot contain a persistent non-target
request on its right boundary.  The regular successor must therefore split
the canonical pending-terminal request.  Persistent coordinates use the
target track, while the movable coordinates use the terminal-clean track.

This file packages exactly that one-step geometry.  It retains the full
comparison warp and suffix shadows of every frozen completed component, and
derives both recursive completion laws from the two tracks.  In particular,
it makes no whole-row tightness assertion and no deletion/quotient
commutation assertion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularPersistentCanonicalSuccessor

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- If an installed continuation at the terminal of an old finite path
reaches the ambient target, then the corresponding starred path reaches the
target as well.  This elementary lemma is independent of how the
continuation was selected. -/
theorem exists_completed_starPath_of_continuation
    {G : DWeb V} {old T : Set G.DPath}
    (hT : G.IsWarp T) (hcompat : G.StarCompatible old T)
    {p : G.DPath} (hp : p ∈ old) {a : V}
    (hpa : G.terminal? p = some a)
    {q : G.DPath} (hqT : q ∈ T) (hqInitial : q.initial = a)
    (hqTarget : SliceSpliceConstructor.ReachesTarget G q) :
    ∃ r ∈ G.star hcompat,
      r.initial = p.initial ∧
        SliceSpliceConstructor.ReachesTarget G r := by
  rcases p with f | ray
  · change some f.finish = some a at hpa
    have hfinish : f.finish = a := Option.some.inj hpa
    let oldPath : old := ⟨Sum.inl f, hp⟩
    have hmatch : ∃ t ∈ T, t.initial = f.finish :=
      ⟨q, hqT, hqInitial.trans hfinish.symm⟩
    let chosen : G.DPath := Classical.choose hmatch
    have hchosenT : chosen ∈ T := (Classical.choose_spec hmatch).1
    have hchosenInitial : chosen.initial = f.finish :=
      (Classical.choose_spec hmatch).2
    have hchosenEq : chosen = q := by
      apply DWeb.IsWarp.eq_of_initial_eq G hT hchosenT hqT
      exact hchosenInitial.trans (hqInitial.trans hfinish.symm).symm
    let r := G.starPath hcompat oldPath
    have hrMem : r ∈ G.star hcompat := ⟨oldPath, rfl⟩
    have hrInitial : r.initial = f.start :=
      G.initial_starPath hcompat oldPath
    refine ⟨r, hrMem, hrInitial, ?_⟩
    obtain ⟨b, hbTarget, hqTerminal⟩ := hqTarget
    refine ⟨b, hbTarget, ?_⟩
    dsimp only [r, oldPath]
    simp only [DWeb.starPath]
    rw [dif_pos hmatch]
    calc
      G.terminal? (DirectedPath.Path.appendFinite f
          (Classical.choose hmatch) _ _) =
          G.terminal? (Classical.choose hmatch) :=
        DirectedPath.Path.terminal?_appendFinite f
          (Classical.choose hmatch) _ _
      _ = some b := by
        change G.terminal? chosen = some b
        rw [hchosenEq]
        exact hqTerminal
  · simp at hpa

/-- Aggregate pending-status transport when exceptional old components are
completed by an arbitrary certified track.  The standard status lemma only
handles exceptions selected by `CleanTargetSlice.target`; the
persistent/movable construction also completes movable exceptions through
`slice.clean`. -/
theorem pendingPart_freezeCompletedStar_status_of_completedExceptions
    {G : DWeb V} (hNorm : G.IsNormalized)
    {kappa : Cardinal.{u}} {L : G.KappaLadder kappa}
    {alpha beta : Ladder.Stage kappa} {right selected U : Set V}
    {W : Set G.DPath}
    (hW : G.IsWarp W)
    (S : RegularCompletedPendingSplice.CleanTargetSlice
      G (G.terminalFrontier (pendingPart G W)) right selected)
    (hL : L.SliceGeometry)
    (hinterval : SliceCandidate.HasStageIntervalSegments
      G L S.clean alpha beta)
    (hcompat : G.StarCompatible (pendingPart G W)
      (S.target ∪ S.clean))
    (hOldStatus : ∀ p ∈ pendingPart G W,
      SliceSpliceConstructor.IsStagePrefix G L alpha p ∨
        ∃ x ∈ U, G.terminal? p = some x)
    (hcomplete : ∀ p ∈ pendingPart G W, ∀ x ∈ U,
      G.terminal? p = some x →
        ∃ q ∈ G.star hcompat,
          q.initial = p.initial ∧
            SliceSpliceConstructor.ReachesTarget G q) :
    ∀ r ∈ pendingPart G
        (RegularCompletedPendingSplice.freezeCompletedStar
          G W (S.target ∪ S.clean) hcompat),
      SliceSpliceConstructor.IsStagePrefix G L beta r ∨
        ∃ x ∈ G.terminalFrontier
            (ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean),
          G.terminal? r = some x := by
  intro r hrPending
  have hrStar : r ∈ G.star hcompat :=
    RegularCompletedPendingSplice.pendingPart_freezeCompletedStar_subset_star
      G W (S.target ∪ S.clean) hcompat hrPending
  obtain ⟨old, rfl⟩ := hrStar
  rcases hOldStatus old.1 old.2 with hpPrefix | hpExceptional
  · exact S.pendingStarPath_stagePrefix_or_maverickTerminal
      hNorm hL hinterval hcompat old hpPrefix hrPending
  · obtain ⟨x, hxU, hpTerminal⟩ := hpExceptional
    obtain ⟨q, hqStar, hqInitial, hqTarget⟩ :=
      hcomplete old.1 old.2 x hxU hpTerminal
    have hstarWarp : G.IsWarp (G.star hcompat) :=
      G.isWarp_star (hW.subset Set.sdiff_subset) S.union_warp hcompat
    have hqeq : q = G.starPath hcompat old := by
      apply DWeb.IsWarp.eq_of_initial_eq G hstarWarp hqStar
        ⟨old, rfl⟩
      exact hqInitial.trans (G.initial_starPath hcompat old).symm
    exfalso
    apply hrPending.2
    exact ⟨hrPending.1, hqeq ▸ hqTarget⟩

/-- The source-faithful one-step regular comparison stage.  Its selected
set is only the persistent part of the full required request.  The clean
track is separately certified to link the movable part to the target.

The inherited comparison geometry is the protected provenance: the used
family is contained in one comparison warp, avoids the old strict roof, and
every frozen completed component has an unused suffix shadow there. -/
structure PersistentSplitComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    extends RegularGlobalAdmissibleProvider.InstalledComparisonGeometry
      G L Sigma Z A request i previous where
  slice : RegularCompletedPendingSplice.CleanTargetSlice
    G (G.terminalFrontier (pendingPart G base)) (L.frontier stageIndex)
      (RegularPersistentRequestSplit.persistentPart G L
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base))
  installed_eq : installed = slice.target ∪ slice.clean
  clean_links_movable : LinksToTarget G slice.clean
    (RegularPersistentRequestSplit.movablePart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous base))

namespace PersistentSplitComparisonStage

/-- Every required pending coordinate is completed by the split stage.
Persistent coordinates use `slice.target`; movable coordinates use the
target-reaching member of `slice.clean`. -/
theorem completes_required
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : PersistentSplitComparisonStage
      G L Sigma Z A request i previous)
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
  · exact S.slice.exists_completed_starPath_of_installed_eq hNorm
      S.installed_eq S.compatible hp hpa haPersistent
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
    obtain ⟨q, hqCompleted, f, hqf, hfpure, hfsuffix⟩ :=
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
    have hinstalledWarp : G.IsWarp S.installed :=
      S.comparison_warp.subset S.installed_subset
    have htInstalled : t ∈ S.installed := by
      rw [S.installed_eq]
      exact Or.inr htClean
    exact exists_completed_starPath_of_continuation hinstalledWarp
      S.compatible hp hpa htInstalled htInitial htTarget

/-- Forget the split provenance only after deriving the two recursive
completion consequences.  This is the exact adapter consumed by the weak
canonical history recursion. -/
def toInstalledComparisonStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : PersistentSplitComparisonStage
      G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) :
    RegularGlobalAdmissibleProvider.InstalledComparisonStage
      G L Sigma Z A request i previous where
  toInstalledComparisonGeometry := S.toInstalledComparisonGeometry
  resolves_pending := by
    intro j hji p hp hrequested
    obtain ⟨q, hqBase, hpq⟩ := (S.base_extends j hji).1 p hp.1
    by_cases hqCompleted : q ∈ completedPart G S.base
    · refine ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base S.installed S.compatible hqCompleted, ?_⟩
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
  realizes_request := by
    intro a haRequest
    have haBase : a.1 ∈ G.initialSet S.base := by
      rw [S.base_initial]
      exact a.2
    obtain ⟨q, hqBase, hqInitial⟩ := haBase
    by_cases hqCompleted : q ∈ completedPart G S.base
    · exact ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base S.installed S.compatible hqCompleted,
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

end PersistentSplitComparisonStage

/-! ## A non-circular producer input -/

/-- Raw persistent/movable successor geometry.  Unlike
`PersistentSplitComparisonStage`, this record does not ask the producer for
the next pending tightness, request, or status.  Those are conclusions of
the clean splice and are derived below. -/
structure PersistentSplitInput
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

  comparison : Set G.DPath
  comparison_warp : G.IsWarp comparison
  slice : RegularCompletedPendingSplice.CleanTargetSlice
    G (G.terminalFrontier (pendingPart G base)) (L.frontier stageIndex)
      (RegularPersistentRequestSplit.persistentPart G L
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base))
  installed_subset : slice.target ∪ slice.clean ⊆ comparison
  installed_avoids_old_strictRoof :
    G.vertexSet (slice.target ∪ slice.clean) ⊆
      (G.strictRoof (L.frontier baseStage))ᶜ
  completed_shadow : ∀ f ∈ completedPart G base,
    ∃ t ∈ comparison, t ∉ slice.target ∪ slice.clean ∧
      f.support \ G.strictRoof (L.frontier baseStage) ⊆ t.support
  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
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

namespace PersistentSplitInput

/-- The protected comparison warp proves that the split installed family is
disjoint from all frozen completed components. -/
theorem cleanStep
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : PersistentSplitInput G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.IsCleanTargetStep G S.base
      (S.slice.target ∪ S.slice.clean) S.compatible := by
  exact RegularEventualCompatibility.cleanTargetStep_of_used_suffixShadow
    G S.base_warp S.comparison_warp S.installed_subset
      S.installed_avoids_old_strictRoof S.completed_shadow S.compatible

/-- Every required old pending component is completed, using the target
track on the persistent part and the clean track on the movable part. -/
theorem completes_required
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : PersistentSplitInput G L Sigma Z A request i previous)
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
    exact exists_completed_starPath_of_continuation S.slice.union_warp
      S.compatible hp hpa (Or.inr htClean) htInitial htTarget

/-- The clean maverick terminals form the next small registered request. -/
theorem maverickTerminals_subset
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : PersistentSplitInput G L Sigma Z A request i previous) :
    G.terminalFrontier
        (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
          S.slice.clean) ⊆
      L.frontier S.stageIndex ∩ Z := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨S.slice.clean_terminal ⟨p, hp.1, hpx⟩,
    S.cleanMavericks_closed ⟨p, hp, G.terminal_mem_support hpx⟩⟩

/-- Derive the full installed comparison stage from the non-circular split
input.  This is the successor adapter consumed by the weak canonical
history recursion. -/
def toInstalledComparisonStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : PersistentSplitInput G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) (hL : L.SliceGeometry) (hA : A ⊆ G.source) :
    RegularGlobalAdmissibleProvider.InstalledComparisonStage
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
    apply pendingPart_freezeCompletedStar_status_of_completedExceptions
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
      comparison := S.comparison
      installed := S.slice.target ∪ S.slice.clean
      comparison_warp := S.comparison_warp
      installed_subset := S.installed_subset
      installed_avoids_old_strictRoof :=
        S.installed_avoids_old_strictRoof
      completed_shadow := S.completed_shadow
      compatible := S.compatible
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

end PersistentSplitInput

end RegularPersistentCanonicalSuccessor
end CardinalInduction
end Erdos599
