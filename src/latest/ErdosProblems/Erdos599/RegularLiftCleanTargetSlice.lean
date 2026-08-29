/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCompletedPendingSplice
import ErdosProblems.Erdos599.SliceDeltaLift

/-!
# Lifting a clean target slice out of a ladder stage web

The local source-9.15 construction is naturally performed in
`L.stageWeb alpha`, whose source is the old ladder frontier.  The canonical
recursion, however, installs ambient paths.  This file lifts both tracks of
a `CleanTargetSlice` simultaneously and records the exact set equalities
needed by the ambient successor adapter.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLiftCleanTargetSlice

open SliceSpliceSource

universe u

variable {V : Type u}

/-- The clean track by itself is an exact linkage from the complementary
left coordinates to the right boundary. -/
theorem clean_isLinkageBetween
    {G : DWeb V} {left right U : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U) :
    IsLinkageBetween G (left \ U) right S.clean := by
  refine ⟨S.union_warp.subset S.clean_subset,
    (fun {_} hp ↦ S.finiteCharacter (Or.inr hp)), S.clean_initial,
    S.clean_terminal, ?_⟩
  intro p hp
  obtain ⟨q, rfl⟩ := S.finiteCharacter (Or.inr hp)
  refine ⟨q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxLeft | hxRight⟩
      · have hx : x ∈
            DirectedPath.Path.support (Sum.inl q : G.DPath) ∩ left :=
          ⟨hxq, hxLeft.1⟩
        have hpure := S.source_pure (Sum.inl q) (Or.inr hp)
        change DirectedPath.Path.support (Sum.inl q : G.DPath) ∩ left =
          {q.start} at hpure
        rw [hpure] at hx
        exact Set.mem_insert_iff.2 (Or.inl
          (Set.mem_singleton_iff.mp hx))
      · have hxTerminal := S.clean_terminal_only
          (Sum.inl q) hp x hxq hxRight
        exact Set.mem_insert_iff.2 (Or.inr
          (Set.mem_singleton_iff.2
            (Option.some.inj hxTerminal).symm))
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with hxStart | hxFinish
      · subst x
        have hxInitial : q.start ∈ G.initialSet S.clean :=
          ⟨Sum.inl q, hp, rfl⟩
        rw [S.clean_initial] at hxInitial
        exact ⟨q.start_mem_support, Or.inl hxInitial⟩
      · have hxTerminal : q.finish ∈ G.terminalFrontier S.clean :=
          ⟨Sum.inl q, hp, rfl⟩
        subst x
        exact ⟨q.finish_mem_support, Or.inr
          (S.clean_terminal hxTerminal)⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxLeft⟩
      have hx : x ∈
          DirectedPath.Path.support (Sum.inl q : G.DPath) ∩ left :=
        ⟨hxq, hxLeft.1⟩
      have hpure := S.source_pure (Sum.inl q) (Or.inr hp)
      change DirectedPath.Path.support (Sum.inl q : G.DPath) ∩ left =
        {q.start} at hpure
      rw [hpure] at hx
      exact hx
    · intro x hx
      have hxStart : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      have hxInitial : q.start ∈ G.initialSet S.clean :=
        ⟨Sum.inl q, hp, rfl⟩
      rw [S.clean_initial] at hxInitial
      exact ⟨q.start_mem_support, hxInitial⟩

/-- Restrict a clean target slice to a smaller exposed left boundary.  The
selected target coordinates are retained verbatim, while the clean track is
restricted to components rooted in the smaller complement. -/
def restrictLeft
    {G : DWeb V} {left right U D : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U)
    (hUD : U ⊆ D) (hDleft : D ⊆ left) :
    RegularCompletedPendingSplice.CleanTargetSlice G D right U := by
  let clean' := initialRestriction G S.clean (D \ U)
  have hclean' : IsLinkageBetween G (D \ U) right clean' :=
    isLinkageBetween_initialRestriction (clean_isLinkageBetween S)
      (fun _ hx ↦ ⟨hDleft hx.1, hx.2⟩)
  refine
    { target := S.target
      clean := clean'
      union_warp := S.union_warp.subset ?_
      finiteCharacter := fun {_} hp ↦ S.finiteCharacter ?_
      target_initial := S.target_initial
      clean_initial := hclean'.initialSet_eq
      initial_cover := hUD
      target_links := S.target_links
      clean_terminal := hclean'.terminalFrontier_subset
      clean_terminal_only := fun p hp ↦ S.clean_terminal_only p hp.1
      source_pure := ?_ }
  · rintro p (hpTarget | hpClean)
    · exact Or.inl hpTarget
    · exact Or.inr hpClean.1
  · rcases hp with hpTarget | hpClean
    · exact Or.inl hpTarget
    · exact Or.inr hpClean.1
  · intro p hp
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxD⟩
      have hxLeft : x ∈ left := hDleft hxD
      have hx : x ∈ p.support ∩ left := ⟨hxp, hxLeft⟩
      rw [S.source_pure p
        (hp.elim Or.inl (fun hpClean ↦ Or.inr hpClean.1))] at hx
      exact hx
    · intro x hx
      have hxEq : x = p.initial := Set.mem_singleton_iff.mp hx
      subst x
      have hxInitial : p.initial ∈ D := by
        rcases hp with hpTarget | hpClean
        · apply hUD
          rw [← S.target_initial]
          exact ⟨p, hpTarget, rfl⟩
        · exact hpClean.2.1
      have hxp : p.initial ∈ p.support := p.initial_mem_support
      simpa only [Set.mem_singleton_iff] using
        (show p.initial ∈ p.support ∩ D from ⟨hxp, hxInitial⟩)

namespace restrictLeft

variable {G : DWeb V} {left right U D : Set V}
  (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U)
  (hUD : U ⊆ D) (hDleft : D ⊆ left)

@[simp] theorem target :
    (restrictLeft S hUD hDleft).target = S.target :=
  by simp [restrictLeft]

@[simp] theorem clean :
    (restrictLeft S hUD hDleft).clean =
      initialRestriction G S.clean (D \ U) :=
  by simp [restrictLeft]

theorem union_subset :
    (restrictLeft S hUD hDleft).target ∪
        (restrictLeft S hUD hDleft).clean ⊆
      S.target ∪ S.clean := by
  rw [target, clean]
  rintro p (hpTarget | hpClean)
  · exact Or.inl hpTarget
  · exact Or.inr hpClean.1

theorem clean_subset :
    (restrictLeft S hUD hDleft).clean ⊆ S.clean := by
  rw [clean]
  exact fun _ hp ↦ hp.1

theorem cleanIntervals
    {kappa : Cardinal.{u}} {L : G.KappaLadder kappa}
    {alpha beta : Ladder.Stage kappa}
    (h : SliceCandidate.HasStageIntervalSegments
      G L S.clean alpha beta) :
    SliceCandidate.HasStageIntervalSegments G L
      (restrictLeft S hUD hDleft).clean alpha beta := by
  intro p hp
  exact h p (clean_subset S hUD hDleft hp)

theorem cleanMavericks_subset
    {Y : Set G.DPath} :
    ControlledSlices.sliceMavericks G Y
        (restrictLeft S hUD hDleft).clean ⊆
      ControlledSlices.sliceMavericks G Y S.clean := by
  intro p hp
  exact ⟨clean_subset S hUD hDleft hp.1, hp.2⟩

theorem cleanMavericks_small
    {kappa : Cardinal.{u}} {Y : Set G.DPath}
    (hsmall : #(ControlledSlices.sliceMavericks G Y S.clean) < kappa) :
    #(ControlledSlices.sliceMavericks G Y
      (restrictLeft S hUD hDleft).clean) < kappa :=
  (Cardinal.mk_subtype_mono
    (cleanMavericks_subset S hUD hDleft)).trans_lt hsmall

theorem cleanMavericks_closed
    {Y : Set G.DPath} {Z : Set V}
    (hclosed : G.vertexSet
      (ControlledSlices.sliceMavericks G Y S.clean) ⊆ Z) :
    G.vertexSet (ControlledSlices.sliceMavericks G Y
      (restrictLeft S hUD hDleft).clean) ⊆ Z := by
  rintro x ⟨p, hp, hxp⟩
  exact hclosed ⟨p, cleanMavericks_subset S hUD hDleft hp, hxp⟩

/-- Target links on a set of retained clean coordinates survive the left
restriction.  Source purity identifies the link-witness component's initial
vertex with the requested coordinate. -/
theorem clean_links
    {M : Set V} (hlinks : LinksToTarget G S.clean M)
    (hM : M ⊆ D \ U) :
    LinksToTarget G (restrictLeft S hUD hDleft).clean M := by
  intro a haM
  obtain ⟨p, hpClean, f, rfl, hfM, hsuffix⟩ := hlinks a haM
  have haSupport : a ∈ f.support := by
    have ha : a ∈ f.support ∩ M := by
      rw [hfM]
      exact Set.mem_singleton a
    exact ha.1
  have haLeft : a ∈ left := hDleft (hM haM).1
  have haInitial : f.start = a := by
    have ha : a ∈
        DirectedPath.Path.support (Sum.inl f : G.DPath) ∩ left :=
      ⟨haSupport, haLeft⟩
    have hpure := S.source_pure (Sum.inl f) (Or.inr hpClean)
    change DirectedPath.Path.support (Sum.inl f : G.DPath) ∩ left =
      {f.start} at hpure
    rw [hpure] at ha
    exact (Set.mem_singleton_iff.mp ha).symm
  rw [clean]
  refine ⟨Sum.inl f, ⟨hpClean, ?_⟩, f, rfl, hfM, hsuffix⟩
  change f.start ∈ D \ U
  simpa only [haInitial] using hM haM

end restrictLeft

/-- Restrict a clean target slice to a smaller exposed left boundary without
assuming that every selected coordinate belongs to that boundary.  Selected
coordinates outside `D` are discarded together with their target components;
the retained selected set is exactly `U ∩ D`.

This is the form needed by the diagonal weak-split table: its request may
contain coordinates unrelated to the current pending row, whereas the
canonical successor may install only components rooted on the current pending
terminal frontier. -/
def restrictLeftInter
    {G : DWeb V} {left right U D : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U)
    (hDleft : D ⊆ left) :
    RegularCompletedPendingSplice.CleanTargetSlice G D right (U ∩ D) := by
  let target' := initialRestriction G S.target (U ∩ D)
  let clean' := initialRestriction G S.clean (D \ U)
  have hclean' : IsLinkageBetween G (D \ U) right clean' :=
    isLinkageBetween_initialRestriction (clean_isLinkageBetween S)
      (fun _ hx ↦ ⟨hDleft hx.1, hx.2⟩)
  refine
    { target := target'
      clean := clean'
      union_warp := S.union_warp.subset ?_
      finiteCharacter := fun {_} hp ↦ S.finiteCharacter ?_
      target_initial := ?_
      clean_initial := ?_
      initial_cover := Set.inter_subset_right
      target_links := ?_
      clean_terminal := hclean'.terminalFrontier_subset
      clean_terminal_only := fun p hp ↦ S.clean_terminal_only p hp.1
      source_pure := ?_ }
  · rintro p (hpTarget | hpClean)
    · exact Or.inl hpTarget.1
    · exact Or.inr hpClean.1
  · rcases hp with hpTarget | hpClean
    · exact Or.inl hpTarget.1
    · exact Or.inr hpClean.1
  · apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact hp.2
    · intro x hx
      have hxInitial : x ∈ G.initialSet S.target := by
        rw [S.target_initial]
        exact hx.1
      obtain ⟨p, hpTarget, hpInitial⟩ := hxInitial
      refine ⟨p, ⟨hpTarget, ?_⟩, hpInitial⟩
      simpa only [hpInitial] using hx
  · rw [hclean'.initialSet_eq]
    ext x
    constructor
    · rintro ⟨hxD, hxNotU⟩
      exact ⟨hxD, fun hxUD ↦ hxNotU hxUD.1⟩
    · rintro ⟨hxD, hxNotUD⟩
      exact ⟨hxD, fun hxU ↦ hxNotUD ⟨hxU, hxD⟩⟩
  · intro a ha
    obtain ⟨p, hpTarget, f, rfl, hfU, hsuffix⟩ :=
      S.target_links a ha.1
    have haSupport : a ∈ f.support := by
      have haInter : a ∈ f.support ∩ U := by
        rw [hfU]
        exact Set.mem_singleton a
      exact haInter.1
    have haLeft : a ∈ left := hDleft ha.2
    have haInitial : f.start = a := by
      have haInter : a ∈
          DirectedPath.Path.support (Sum.inl f : G.DPath) ∩ left :=
        ⟨haSupport, haLeft⟩
      have hpure := S.source_pure (Sum.inl f) (Or.inl hpTarget)
      change DirectedPath.Path.support (Sum.inl f : G.DPath) ∩ left =
        {f.start} at hpure
      rw [hpure] at haInter
      exact (Set.mem_singleton_iff.mp haInter).symm
    refine ⟨Sum.inl f, ⟨hpTarget, ?_⟩, f, rfl, ?_, hsuffix⟩
    · change f.start ∈ U ∩ D
      simpa only [haInitial] using ha
    · apply Set.Subset.antisymm
      · rintro x ⟨hxf, hxU, _hxD⟩
        have hx : x ∈ ({a} : Set V) := by
          rw [← hfU]
          exact ⟨hxf, hxU⟩
        exact hx
      · intro x hx
        have hxa : x = a := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨haSupport, ha⟩
  · intro p hp
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxD⟩
      have hx : x ∈ p.support ∩ left := ⟨hxp, hDleft hxD⟩
      rw [S.source_pure p
        (hp.elim (fun hpTarget ↦ Or.inl hpTarget.1)
          (fun hpClean ↦ Or.inr hpClean.1))] at hx
      exact hx
    · intro x hx
      have hxEq : x = p.initial := Set.mem_singleton_iff.mp hx
      subst x
      have hxInitial : p.initial ∈ D := by
        rcases hp with hpTarget | hpClean
        · exact hpTarget.2.2
        · exact hpClean.2.1
      exact ⟨p.initial_mem_support, hxInitial⟩

namespace restrictLeftInter

variable {G : DWeb V} {left right U D : Set V}
  (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U)
  (hDleft : D ⊆ left)

@[simp] theorem target :
    (restrictLeftInter S hDleft).target =
      initialRestriction G S.target (U ∩ D) :=
  rfl

@[simp] theorem clean :
    (restrictLeftInter S hDleft).clean =
      initialRestriction G S.clean (D \ U) :=
  rfl

/-- The clean restriction can equivalently be written as the complement of
the retained selected set inside the new left boundary. -/
theorem clean_eq_selectedComplement :
    (restrictLeftInter S hDleft).clean =
      initialRestriction G S.clean (D \ (U ∩ D)) := by
  rw [clean]
  congr 1
  ext x
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨hxD, hxNotU⟩
    exact ⟨hxD, fun hx ↦ hxNotU hx.1⟩
  · rintro ⟨hxD, hxNotUD⟩
    exact ⟨hxD, fun hxU ↦ hxNotUD ⟨hxU, hxD⟩⟩

theorem target_subset :
    (restrictLeftInter S hDleft).target ⊆ S.target :=
  fun _ hp ↦ hp.1

theorem clean_subset :
    (restrictLeftInter S hDleft).clean ⊆ S.clean :=
  fun _ hp ↦ hp.1

theorem union_subset :
    (restrictLeftInter S hDleft).target ∪
        (restrictLeftInter S hDleft).clean ⊆
      S.target ∪ S.clean := by
  rintro p (hpTarget | hpClean)
  · exact Or.inl (target_subset S hDleft hpTarget)
  · exact Or.inr (clean_subset S hDleft hpClean)

theorem cleanIntervals
    {kappa : Cardinal.{u}} {L : G.KappaLadder kappa}
    {alpha beta : Ladder.Stage kappa}
    (h : SliceCandidate.HasStageIntervalSegments
      G L S.clean alpha beta) :
    SliceCandidate.HasStageIntervalSegments G L
      (restrictLeftInter S hDleft).clean alpha beta := by
  intro p hp
  exact h p (clean_subset S hDleft hp)

theorem cleanMavericks_subset
    {Y : Set G.DPath} :
    ControlledSlices.sliceMavericks G Y
        (restrictLeftInter S hDleft).clean ⊆
      ControlledSlices.sliceMavericks G Y S.clean := by
  intro p hp
  exact ⟨clean_subset S hDleft hp.1, hp.2⟩

theorem cleanMavericks_small
    {kappa : Cardinal.{u}} {Y : Set G.DPath}
    (hsmall : #(ControlledSlices.sliceMavericks G Y S.clean) < kappa) :
    #(ControlledSlices.sliceMavericks G Y
      (restrictLeftInter S hDleft).clean) < kappa :=
  (Cardinal.mk_subtype_mono
    (cleanMavericks_subset S hDleft)).trans_lt hsmall

theorem cleanMavericks_closed
    {Y : Set G.DPath} {Z : Set V}
    (hclosed : G.vertexSet
      (ControlledSlices.sliceMavericks G Y S.clean) ⊆ Z) :
    G.vertexSet (ControlledSlices.sliceMavericks G Y
      (restrictLeftInter S hDleft).clean) ⊆ Z := by
  rintro x ⟨p, hp, hxp⟩
  exact hclosed ⟨p, cleanMavericks_subset S hDleft hp, hxp⟩

theorem clean_links
    {M : Set V} (hlinks : LinksToTarget G S.clean M)
    (hM : M ⊆ D \ U) :
    LinksToTarget G (restrictLeftInter S hDleft).clean M := by
  intro a haM
  obtain ⟨p, hpClean, f, rfl, hfM, hsuffix⟩ := hlinks a haM
  have haSupport : a ∈ f.support := by
    have ha : a ∈ f.support ∩ M := by
      rw [hfM]
      exact Set.mem_singleton a
    exact ha.1
  have haLeft : a ∈ left := hDleft (hM haM).1
  have haInitial : f.start = a := by
    have ha : a ∈
        DirectedPath.Path.support (Sum.inl f : G.DPath) ∩ left :=
      ⟨haSupport, haLeft⟩
    have hpure := S.source_pure (Sum.inl f) (Or.inr hpClean)
    change DirectedPath.Path.support (Sum.inl f : G.DPath) ∩ left =
      {f.start} at hpure
    rw [hpure] at ha
    exact (Set.mem_singleton_iff.mp ha).symm
  refine ⟨Sum.inl f, ⟨hpClean, ?_⟩, f, rfl, hfM, hsuffix⟩
  change f.start ∈ D \ U
  simpa only [haInitial] using hM haM

end restrictLeftInter

/-- Lifting commutes with union of stage-web families. -/
theorem liftStageFamily_union
    {G : DWeb V} {kappa : Cardinal.{u}}
    (L : G.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (W T : Set (L.stageWeb alpha).DPath) :
    SliceSegmentCore.liftStageFamily L alpha (W ∪ T) =
      SliceSegmentCore.liftStageFamily L alpha W ∪
        SliceSegmentCore.liftStageFamily L alpha T := by
  ext p
  constructor
  · rintro ⟨q, hqW | hqT, rfl⟩
    · exact Or.inl ⟨q, hqW, rfl⟩
    · exact Or.inr ⟨q, hqT, rfl⟩
  · rintro (⟨q, hqW, rfl⟩ | ⟨q, hqT, rfl⟩)
    · exact ⟨q, Or.inl hqW, rfl⟩
    · exact ⟨q, Or.inr hqT, rfl⟩

/-- Ambient lifting preserves the literal vertex carrier of a stage family. -/
theorem vertexSet_liftStageFamily
    {G : DWeb V} {kappa : Cardinal.{u}}
    (L : G.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (W : Set (L.stageWeb alpha).DPath) :
    G.vertexSet (SliceSegmentCore.liftStageFamily L alpha W) =
      (L.stageWeb alpha).vertexSet W := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, hqW, rfl⟩, hx⟩
    exact ⟨q, hqW, by
      simpa only [L.support_liftStagePath alpha q] using hx⟩
  · rintro ⟨q, hqW, hx⟩
    refine ⟨L.liftStagePath alpha q, ⟨q, hqW, rfl⟩, ?_⟩
    simpa only [L.support_liftStagePath alpha q] using hx

/-- Lift both tracks of a stage-web clean target slice to the ambient web.
All endpoint sets are unchanged because stage-path lifting preserves paths,
supports, initials, and terminals literally. -/
def liftStageSlice
    {G : DWeb V} {kappa : Cardinal.{u}}
    (L : G.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    {left right U : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice
      (L.stageWeb alpha) left right U) :
    RegularCompletedPendingSplice.CleanTargetSlice G left right U where
  target := SliceSegmentCore.liftStageFamily L alpha S.target
  clean := SliceSegmentCore.liftStageFamily L alpha S.clean
  union_warp := by
    rw [← liftStageFamily_union]
    exact SliceSegmentCore.liftStageFamily_isWarp L alpha S.union_warp
  finiteCharacter := by
    rw [← liftStageFamily_union]
    exact SliceSegmentCore.liftStageFamily_finiteCharacter L alpha
      S.finiteCharacter
  target_initial := by
    rw [SliceSegmentCore.initialSet_liftStageFamily]
    exact S.target_initial
  clean_initial := by
    rw [SliceSegmentCore.initialSet_liftStageFamily]
    exact S.clean_initial
  initial_cover := S.initial_cover
  target_links :=
    SliceSegmentCore.linksToTarget_liftStageFamily L alpha S.target_links
  clean_terminal := by
    rw [SliceSegmentCore.terminalFrontier_liftStageFamily]
    exact S.clean_terminal
  clean_terminal_only :=
    SliceDeltaLift.meetsOnlyAtTerminal_liftStageFamily
      S.clean_terminal_only
  source_pure := by
    rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · simpa only [L.support_liftStagePath alpha p,
        SliceSegmentCore.liftStagePath_initial] using
          S.source_pure p (Or.inl hp)
    · simpa only [L.support_liftStagePath alpha p,
        SliceSegmentCore.liftStagePath_initial] using
          S.source_pure p (Or.inr hp)

namespace liftStageSlice

variable {G : DWeb V} {kappa : Cardinal.{u}}
  {L : G.KappaLadder kappa} {alpha : Ladder.Stage kappa}
  {left right U : Set V}
  (S : RegularCompletedPendingSplice.CleanTargetSlice
    (L.stageWeb alpha) left right U)

@[simp] theorem target :
    (liftStageSlice L alpha S).target =
      SliceSegmentCore.liftStageFamily L alpha S.target :=
  rfl

@[simp] theorem clean :
    (liftStageSlice L alpha S).clean =
      SliceSegmentCore.liftStageFamily L alpha S.clean :=
  rfl

@[simp] theorem union :
    (liftStageSlice L alpha S).target ∪
        (liftStageSlice L alpha S).clean =
      SliceSegmentCore.liftStageFamily L alpha
        (S.target ∪ S.clean) := by
  exact (liftStageFamily_union L alpha S.target S.clean).symm

@[simp] theorem target_vertexSet :
    G.vertexSet (liftStageSlice L alpha S).target =
      (L.stageWeb alpha).vertexSet S.target := by
  exact vertexSet_liftStageFamily L alpha S.target

@[simp] theorem clean_vertexSet :
    G.vertexSet (liftStageSlice L alpha S).clean =
      (L.stageWeb alpha).vertexSet S.clean := by
  exact vertexSet_liftStageFamily L alpha S.clean

@[simp] theorem union_vertexSet :
    G.vertexSet
        ((liftStageSlice L alpha S).target ∪
          (liftStageSlice L alpha S).clean) =
      (L.stageWeb alpha).vertexSet (S.target ∪ S.clean) := by
  rw [union, vertexSet_liftStageFamily]

end liftStageSlice

end RegularLiftCleanTargetSlice
end CardinalInduction
end Erdos599
