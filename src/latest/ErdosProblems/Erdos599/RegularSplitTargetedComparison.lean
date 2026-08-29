/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalSuccessor

/-!
# Split targeted comparisons at a regular stage

A requested vertex which persists on the next ladder frontier cannot be on
one family which is both target-linking and right-tight.  The sound successor
therefore has two installed tracks.  The target track completes persistent
requests and is frozen; only the clean track is required to be right-tight at
the new frontier.  Movable requests are completed by the clean track.

This file packages the resulting source-9.15 interface independently of the
particular lower-cardinal construction.  In particular, the completion lemma
below uses neither right-tightness nor a linkage-to-the-new-frontier statement
for the target track.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSplitTargetedComparison

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A target-linking warp whose members meet the old boundary only at their
initial vertex completes every requested old terminal under source star.

Unlike `SliceSpliceConstructor.star_realizes_requested_terminal`, this lemma
does not ask the new family to be a linkage to one common right boundary.
That strengthening is false for the persistent target track. -/
theorem star_realizes_requested_terminal_of_sourcePure
    {G : DWeb V} {old installed : Set G.DPath} {left U : Set V}
    (hNorm : G.IsNormalized)
    (hwarp : G.IsWarp installed)
    (hlinks : LinksToTarget G installed U)
    (hsource : ∀ q ∈ installed,
      q.support ∩ left = {q.initial})
    (hUleft : U ⊆ left)
    (hcompat : G.StarCompatible old installed)
    {p : G.DPath} (hpOld : p ∈ old) {a : V}
    (hpa : G.terminal? p = some a) (haU : a ∈ U) :
    ∃ r ∈ G.star hcompat,
      r.initial = p.initial ∧
        ∃ b ∈ G.target, G.terminal? r = some b := by
  obtain ⟨q, hqInstalled, f, hqf, hfU, hfsuffix⟩ := hlinks a haU
  have haSupport : a ∈ f.support := by
    have haInter : a ∈ f.support ∩ U := by
      rw [hfU]
      exact Set.mem_singleton a
    exact haInter.1
  have hqInitial : q.initial = a := by
    have haLeft : a ∈ left := hUleft haU
    have haSource : a ∈ q.support ∩ left := by
      rw [hqf]
      exact ⟨haSupport, haLeft⟩
    rw [hsource q hqInstalled] at haSource
    exact (Set.mem_singleton_iff.mp haSource).symm
  obtain ⟨_before, _after, hsupport, b, hbTarget, hbAfter⟩ := hfsuffix
  have hbf : b ∈ f.support := by
    change b ∈ f.walk.support
    rw [hsupport]
    exact List.mem_append_right _ hbAfter
  have hbFinish : b = f.finish :=
    hNorm.eq_finish_of_mem_walk f.walk hbf hbTarget
  rcases p with p | ray
  · have hpFinish : p.finish = a := Option.some.inj hpa
    let oldMember : old := ⟨Sum.inl p, hpOld⟩
    refine ⟨G.starPath hcompat oldMember, ⟨oldMember, rfl⟩,
      G.initial_starPath hcompat oldMember, b, hbTarget, ?_⟩
    dsimp only [oldMember]
    simp only [DWeb.starPath]
    split
    next hex =>
      let q' := Classical.choose hex
      have hq'Mem : q' ∈ installed := (Classical.choose_spec hex).1
      have hq'Start : q'.initial = p.finish :=
        (Classical.choose_spec hex).2
      have hqEq : q' = q := by
        apply DWeb.IsWarp.eq_of_initial_eq G hwarp hq'Mem hqInstalled
        exact hq'Start.trans (hpFinish.trans hqInitial.symm)
      calc
        G.terminal? (DirectedPath.Path.appendFinite p
            (Classical.choose hex) _ _) =
            (Classical.choose hex).terminal? :=
          DirectedPath.Path.terminal?_appendFinite p
            (Classical.choose hex) _ _
        _ = some b := by
          rw [show Classical.choose hex = q from hqEq]
          rw [hqf]
          exact congrArg some hbFinish.symm
    next hnone =>
      exfalso
      apply hnone
      exact ⟨q, hqInstalled, hqInitial.trans hpFinish.symm⟩
  · simp at hpa

/-- The exact split comparison datum needed by a completed/pending regular
successor.  The `target` field of `slice` is indexed only by `persistent`;
the additional `clean_links_movable` field records the requests completed by
the right-tight clean track.

The full comparison remains a weak annular slice.  No right-boundary
tightness is asserted for it or for the target track. -/
structure SplitTargetedComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z : Set V) (base : Set G.DPath)
    (alpha : Ladder.Stage kappa) (U : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_lt_stageIndex : alpha < stageIndex

  base_warp : G.IsWarp base
  request_subset : U ⊆
    G.terminalFrontier (pendingPart G base)
  persistent : Set V
  movable : Set V
  persistent_union_movable : persistent ∪ movable = U
  persistent_movable_disjoint : Disjoint persistent movable

  comparison : Set G.DPath
  comparison_annular : SliceSplice.IsAnnularSlice G L comparison
    alpha stageIndex U

  slice : RegularCompletedPendingSplice.CleanTargetSlice G
    (G.terminalFrontier (pendingPart G base))
      (L.frontier stageIndex) persistent
  target_small : #(slice.target) < kappa
  movable_subset_clean_initial : movable ⊆
    G.terminalFrontier (pendingPart G base) \ persistent
  clean_links_movable : LinksToTarget G slice.clean movable

  installed_subset : slice.target ∪ slice.clean ⊆ comparison
  installed_avoids_old_strictRoof :
    G.vertexSet (slice.target ∪ slice.clean) ⊆
      (G.strictRoof (L.frontier alpha))ᶜ
  completed_shadow : ∀ f ∈ completedPart G base,
    ∃ t ∈ comparison, t ∉ slice.target ∪ slice.clean ∧
      f.support \ G.strictRoof (L.frontier alpha) ⊆ t.support
  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)

  vertices_closed :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible) ⊆ Z
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)))
    (L.frontier stageIndex)
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible))
  pending_below_roof : G.vertexSet
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)) ⊆
      G.roof (L.frontier stageIndex)

  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean alpha stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) < kappa
  cleanMavericks_closed :
    G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
        slice.clean) ⊆ Z

namespace SplitTargetedComparisonStage

variable {kappa : Cardinal.{u}} {G : DWeb V}
  {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
  {Z : Set V} {base : Set G.DPath} {alpha : Ladder.Stage kappa}
  {U : Set V}

/-- The annular comparison is deliberately weak: it supplies a full warp,
but no `MeetsOnlyAtTerminal` conclusion at the new frontier. -/
theorem comparison_warp
    (S : SplitTargetedComparisonStage G L Sigma Z base alpha U) :
    G.IsWarp S.comparison :=
  S.comparison_annular.1.1.isWarp

/-- Suffix shadows in the full comparison protect previously completed
components from both installed tracks. -/
theorem cleanStep
    (S : SplitTargetedComparisonStage G L Sigma Z base alpha U) :
    RegularCompletedPendingSplice.IsCleanTargetStep G base
      (S.slice.target ∪ S.slice.clean) S.compatible := by
  exact RegularEventualCompatibility.cleanTargetStep_of_used_suffixShadow
    G S.base_warp S.comparison_warp S.installed_subset
      S.installed_avoids_old_strictRoof S.completed_shadow S.compatible

/-- The two installed tracks together link every requested coordinate to
the original target. -/
theorem installed_links
    (S : SplitTargetedComparisonStage G L Sigma Z base alpha U) :
    LinksToTarget G (S.slice.target ∪ S.slice.clean) U := by
  intro a ha
  have ha' : a ∈ S.persistent ∪ S.movable := by
    rw [S.persistent_union_movable]
    exact ha
  rcases ha' with haPersistent | haMovable
  · obtain ⟨p, hp, f, hpf, hpure, hsuffix⟩ :=
      S.slice.target_links a haPersistent
    have haSupport : a ∈ f.support := by
      have : a ∈ f.support ∩ S.persistent := by
        rw [hpure]
        exact Set.mem_singleton a
      exact this.1
    have hpInitial : p.initial = a := by
      have haOld : a ∈ p.support ∩
          G.terminalFrontier (pendingPart G base) := by
        rw [hpf]
        exact ⟨haSupport, S.request_subset
          (S.persistent_union_movable ▸ Or.inl haPersistent)⟩
      rw [S.slice.source_pure p (Or.inl hp)] at haOld
      exact (Set.mem_singleton_iff.mp haOld).symm
    refine ⟨p, Or.inl hp, f, hpf, ?_, hsuffix⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxU⟩
      have hxOld : x ∈ p.support ∩
          G.terminalFrontier (pendingPart G base) := by
        rw [hpf]
        exact ⟨hxf, S.request_subset hxU⟩
      rw [S.slice.source_pure p (Or.inl hp)] at hxOld
      exact Set.mem_singleton_iff.mpr
        ((Set.mem_singleton_iff.mp hxOld).trans hpInitial)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨haSupport, ha⟩
  · obtain ⟨p, hp, f, hpf, hpure, hsuffix⟩ :=
      S.clean_links_movable a haMovable
    have haSupport : a ∈ f.support := by
      have : a ∈ f.support ∩ S.movable := by
        rw [hpure]
        exact Set.mem_singleton a
      exact this.1
    have hpInitial : p.initial = a := by
      have haOld : a ∈ p.support ∩
          G.terminalFrontier (pendingPart G base) := by
        rw [hpf]
        exact ⟨haSupport, S.request_subset
          (S.persistent_union_movable ▸ Or.inr haMovable)⟩
      rw [S.slice.source_pure p (Or.inr hp)] at haOld
      exact (Set.mem_singleton_iff.mp haOld).symm
    refine ⟨p, Or.inr hp, f, hpf, ?_, hsuffix⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxU⟩
      have hxOld : x ∈ p.support ∩
          G.terminalFrontier (pendingPart G base) := by
        rw [hpf]
        exact ⟨hxf, S.request_subset hxU⟩
      rw [S.slice.source_pure p (Or.inr hp)] at hxOld
      exact Set.mem_singleton_iff.mpr
        ((Set.mem_singleton_iff.mp hxOld).trans hpInitial)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨haSupport, ha⟩

/-- Every installed component meets the old pending boundary only at its
initial vertex. -/
theorem installed_sourcePure
    (S : SplitTargetedComparisonStage G L Sigma Z base alpha U) :
    ∀ p ∈ S.slice.target ∪ S.slice.clean,
      p.support ∩ G.terminalFrontier (pendingPart G base) =
        {p.initial} :=
  S.slice.source_pure

/-- A requested pending component is completed by this split successor.
Persistent requests use the target track; movable requests use the clean
track.  The conclusion identifies the actual source-star component, so it
is directly consumable by recursive status bookkeeping. -/
theorem star_realizes_requested_terminal
    (S : SplitTargetedComparisonStage G L Sigma Z base alpha U)
    (hNorm : G.IsNormalized)
    {p : G.DPath} (hp : p ∈ pendingPart G base) {a : V}
    (hpa : G.terminal? p = some a) (haU : a ∈ U) :
    ∃ r ∈ G.star S.compatible,
      r.initial = p.initial ∧
        ∃ b ∈ G.target, G.terminal? r = some b := by
  apply star_realizes_requested_terminal_of_sourcePure
    hNorm S.slice.union_warp S.installed_links
      S.installed_sourcePure S.request_subset S.compatible hp hpa haU

/-- The preceding completion belongs to the frozen/starred result and is
therefore recorded as a genuinely completed component. -/
theorem exists_completed_result_of_requested_terminal
    (S : SplitTargetedComparisonStage G L Sigma Z base alpha U)
    (hNorm : G.IsNormalized)
    {p : G.DPath} (hp : p ∈ pendingPart G base) {a : V}
    (hpa : G.terminal? p = some a) (haU : a ∈ U) :
    ∃ r ∈ completedPart G
        (RegularCompletedPendingSplice.freezeCompletedStar G base
          (S.slice.target ∪ S.slice.clean) S.compatible),
      r.initial = p.initial := by
  obtain ⟨r, hrStar, hrInitial, b, hbTarget, hrTerminal⟩ :=
    S.star_realizes_requested_terminal hNorm hp hpa haU
  exact ⟨r, ⟨Or.inr hrStar, b, hbTarget, hrTerminal⟩, hrInitial⟩

end SplitTargetedComparisonStage

end RegularSplitTargetedComparison
end CardinalInduction
end Erdos599
