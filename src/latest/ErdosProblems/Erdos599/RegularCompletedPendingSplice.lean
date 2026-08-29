/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularCompletedPendingMerge
import ErdosProblems.Erdos599.LadderSliceGeometry
import ErdosProblems.Erdos599.SliceSpliceConstructor

/-!
# Completed/pending splices at a regular cardinal

A target path cannot in general be used as the clean annular path at a later
ladder frontier.  In particular, if its initial vertex persists on that
frontier but is not itself a target vertex, `MeetsOnlyAtTerminal` is false.

This file gives the regular splice the same two-track interface as the
singular construction.  Completed components are frozen.  Only the canonical
`pendingPart` is starred with the next clean/target slice.  The cross-disjoint
condition in `IsCleanTargetStep` is intentional: a later suffix can otherwise
meet an already frozen target suffix beyond the current frontier, and a warp
on the current frontier alone does not rule this out.

The final chain consumer is independent of the annular implementation.  Once
every scheduled source occurs in a completed component, the thread limit is a
linkage to the original target.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCompletedPendingSplice

open SingularContinuation SingularExtension
open SliceSpliceSource

universe u v

variable {V : Type u}

/-- The old completed components together with the star of the still-pending
components.  Notice that completed components are not arguments of `star`. -/
def freezeCompletedStar (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) : Set G.DPath :=
  completedPart G W ∪ G.star hcompat

theorem completedPart_subset_freezeCompletedStar
    (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) :
    completedPart G W ⊆ freezeCompletedStar G W T hcompat :=
  Set.subset_union_left

/-- Old target components remain literally present and completed in the new
row.  This is the frozen-track invariant used by recursive validity. -/
theorem completedPart_subset_completedPart_freezeCompletedStar
    (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) :
    completedPart G W ⊆
      completedPart G (freezeCompletedStar G W T hcompat) := by
  intro p hp
  exact ⟨Or.inl hp, hp.2⟩

theorem star_pending_subset_freezeCompletedStar
    (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) :
    G.star hcompat ⊆ freezeCompletedStar G W T hcompat :=
  Set.subset_union_right

/-- A member which is still pending after freezing and starring must belong
to the starred pending family.  It cannot come from the frozen completed
half, since that same target witness would complete it in the union. -/
theorem pendingPart_freezeCompletedStar_subset_star
    (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) :
    pendingPart G (freezeCompletedStar G W T hcompat) ⊆
      G.star hcompat := by
  intro p hpPending
  rcases hpPending.1 with hpCompleted | hpStar
  · exact (hpPending.2 ⟨Or.inl hpCompleted, hpCompleted.2⟩).elim
  · exact hpStar

/-- Freezing the completed half and extending the pending half is a forward
extension of the whole old row.  No geometric hypothesis beyond the star
compatibility is needed for this bookkeeping fact. -/
theorem forwardExtension_freezeCompletedStar
    (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) :
    G.ForwardExtension W (freezeCompletedStar G W T hcompat) := by
  have hstar : G.ForwardExtension (pendingPart G W) (G.star hcompat) :=
    G.forwardExtension_star hcompat
  constructor
  · intro p hpW
    rw [← completedPart_union_pendingPart G W] at hpW
    rcases hpW with hpDone | hpPending
    · exact ⟨p, Or.inl hpDone, G.extends_refl p⟩
    · obtain ⟨q, hq, hpq⟩ := hstar.1 p hpPending
      exact ⟨q, Or.inr hq, hpq⟩
  · intro q hq
    rcases hq with hqDone | hqStar
    · exact ⟨q, hqDone.1, G.extends_refl q⟩
    · obtain ⟨p, hp, hpq⟩ := hstar.2 q hqStar
      exact ⟨p, hp.1, hpq⟩

theorem initialSet_freezeCompletedStar
    (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) :
    G.initialSet (freezeCompletedStar G W T hcompat) = G.initialSet W := by
  exact (G.initialSet_eq_of_forwardExtension
    (forwardExtension_freezeCompletedStar G W T hcompat)).symm

/-- The exact soundness obligations for a completed/pending successor.

`pending_warp` and `slice_warp` make the starred pending row a warp.  The
separate `cross_disjoint` field is the missing obligation in a stage-only
annular candidate: it protects every target component frozen at an earlier
step from the newly chosen suffixes. -/
structure IsCleanTargetStep
    (G : DWeb V) (W T : Set G.DPath)
    (hcompat : G.StarCompatible (pendingPart G W) T) : Prop where
  old_warp : G.IsWarp W
  pending_warp : G.IsWarp (pendingPart G W)
  slice_warp : G.IsWarp T
  cross_disjoint : Disjoint (G.vertexSet (completedPart G W))
    (G.vertexSet (G.star hcompat))

/-- The simpler provider-side avoidance condition is enough: the old warp
already separates its completed and pending components, while every vertex
of the pending star comes from the old pending row or the new slice. -/
theorem IsCleanTargetStep.of_disjoint_slice
    {G : DWeb V} {W T : Set G.DPath}
    {hcompat : G.StarCompatible (pendingPart G W) T}
    (hW : G.IsWarp W) (hT : G.IsWarp T)
    (hcross : Disjoint (G.vertexSet (completedPart G W))
      (G.vertexSet T)) :
    IsCleanTargetStep G W T hcompat := by
  have hPendingWarp : G.IsWarp (pendingPart G W) := by
    intro p hp q hq hpq
    exact hW hp.1 hq.1 hpq
  have hDonePending : Disjoint (G.vertexSet (completedPart G W))
      (G.vertexSet (pendingPart G W)) := by
    apply Set.disjoint_left.2
    intro x hxDone hxPending
    obtain ⟨p, hpDone, hxp⟩ := hxDone
    obtain ⟨q, hqPending, hxq⟩ := hxPending
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hqPending.2 hpDone
    exact Set.disjoint_left.1 (hW hpDone.1 hqPending.1 hpq) hxp hxq
  refine
    { old_warp := hW
      pending_warp := hPendingWarp
      slice_warp := hT
      cross_disjoint := ?_ }
  apply Set.disjoint_left.2
  intro x hxDone hxStar
  rcases SliceSpliceSource.vertexSet_star_subset_union hcompat hxStar with
      hxPending | hxT
  · exact Set.disjoint_left.1 hDonePending hxDone hxPending
  · exact Set.disjoint_left.1 hcross hxDone hxT

theorem IsCleanTargetStep.result_isWarp
    {G : DWeb V} {W T : Set G.DPath}
    {hcompat : G.StarCompatible (pendingPart G W) T}
    (h : IsCleanTargetStep G W T hcompat) :
    G.IsWarp (freezeCompletedStar G W T hcompat) := by
  apply SingularContinuation.isWarp_union_of_disjoint_vertexSet G
  · intro p hp q hq hpq
    exact h.old_warp hp.1 hq.1 hpq
  · exact G.isWarp_star h.pending_warp h.slice_warp hcompat
  · exact h.cross_disjoint

theorem IsCleanTargetStep.result_forwardExtension
    {G : DWeb V} {W T : Set G.DPath}
    {hcompat : G.StarCompatible (pendingPart G W) T}
    (_h : IsCleanTargetStep G W T hcompat) :
    G.ForwardExtension W (freezeCompletedStar G W T hcompat) :=
  forwardExtension_freezeCompletedStar G W T hcompat

theorem IsCleanTargetStep.result_initialSet
    {G : DWeb V} {W T : Set G.DPath}
    {hcompat : G.StarCompatible (pendingPart G W) T}
    (_h : IsCleanTargetStep G W T hcompat) :
    G.initialSet (freezeCompletedStar G W T hcompat) = G.initialSet W :=
  initialSet_freezeCompletedStar G W T hcompat

/-- If both tracks have finite character, so does the frozen/starred row. -/
theorem IsCleanTargetStep.result_finiteCharacter
    {G : DWeb V} {W T : Set G.DPath}
    {hcompat : G.StarCompatible (pendingPart G W) T}
    (_h : IsCleanTargetStep G W T hcompat)
    (hWfinite : G.HasFiniteCharacter W)
    (hstarFinite : G.HasFiniteCharacter (G.star hcompat)) :
    G.HasFiniteCharacter (freezeCompletedStar G W T hcompat) := by
  apply SingularContinuation.finiteCharacter_union G
  · intro p hp
    exact hWfinite hp.1
  · exact hstarFinite

/-- A requested old pending component is completed by the new row as soon
as its starred image reaches the target. -/
theorem requested_pending_mem_completedPart
    {G : DWeb V} {W T : Set G.DPath}
    {hcompat : G.StarCompatible (pendingPart G W) T}
    {p q : G.DPath} (hq : q ∈ G.star hcompat)
    (_hpq : G.Extends p q) (hqTarget :
      SliceSpliceConstructor.ReachesTarget G q) :
    q ∈ completedPart G (freezeCompletedStar G W T hcompat) := by
  exact ⟨Or.inr hq, hqTarget⟩

/-- A provider-facing split slice.  `target` completes precisely the selected
frontier sources, while `clean` is the terminal-clean annular continuation of
the complement.  `source_pure` is the common compatibility condition needed
to star either track onto a row ending at `left`.

The slice itself deliberately contains no claim that `target` meets `right`
only at its terminal; that claim is generally false and was the defect in the
old single-track candidate. -/
structure CleanTargetSlice (G : DWeb V) (left right U : Set V) where
  target : Set G.DPath
  clean : Set G.DPath
  union_warp : G.IsWarp (target ∪ clean)
  finiteCharacter : G.HasFiniteCharacter (target ∪ clean)
  target_initial : G.initialSet target = U
  clean_initial : G.initialSet clean = left \ U
  initial_cover : U ⊆ left
  target_links : LinksToTarget G target U
  clean_terminal : G.terminalFrontier clean ⊆ right
  clean_terminal_only : MeetsOnlyAtTerminal G clean right
  source_pure : ∀ p ∈ target ∪ clean,
    p.support ∩ left = {p.initial}

theorem CleanTargetSlice.initialSet_union
    {G : DWeb V} {left right U : Set V}
    (S : CleanTargetSlice G left right U) :
    G.initialSet (S.target ∪ S.clean) = left := by
  rw [G.initialSet_union, S.target_initial, S.clean_initial]
  exact Set.union_sdiff_cancel S.initial_cover

theorem CleanTargetSlice.target_subset
    {G : DWeb V} {left right U : Set V}
    (S : CleanTargetSlice G left right U) :
    S.target ⊆ S.target ∪ S.clean :=
  Set.subset_union_left

theorem CleanTargetSlice.clean_subset
    {G : DWeb V} {left right U : Set V}
    (S : CleanTargetSlice G left right U) :
    S.clean ⊆ S.target ∪ S.clean :=
  Set.subset_union_right

/-- In a normalized web every member of the target track really is a
completed path.  `LinksToTarget` gives a completed member for each selected
initial coordinate; the warp property and the exact initial-set equation
identify that witness with the given target-track member. -/
theorem CleanTargetSlice.target_subset_completedPart
    {G : DWeb V} (hNorm : G.IsNormalized)
    {left right U : Set V} (S : CleanTargetSlice G left right U) :
    S.target ⊆ completedPart G S.target := by
  intro p hpTarget
  have hpInitialU : p.initial ∈ U := by
    rw [← S.target_initial]
    exact ⟨p, hpTarget, rfl⟩
  have hlinksCompleted : LinksToTarget G (completedPart G S.target) U :=
    linksToTarget_completedPart hNorm S.target_links
  obtain ⟨q, hqCompleted, f, hqf, hfPure, _hSuffix⟩ :=
    hlinksCompleted p.initial hpInitialU
  have hqTarget : q ∈ S.target := hqCompleted.1
  have hqInitialU : q.initial ∈ U := by
    rw [← S.target_initial]
    exact ⟨q, hqTarget, rfl⟩
  have hqInitial : q.initial = p.initial := by
    subst q
    have hmem : f.start ∈ f.support ∩ U :=
      ⟨f.start_mem_support, hqInitialU⟩
    rw [hfPure] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have hpq : p = q := by
    apply DWeb.IsWarp.eq_of_initial_eq G S.union_warp
      (Or.inl hpTarget) (Or.inl hqTarget)
    exact hqInitial.symm
  rwa [hpq]

/-- Every still-pending starred component used the clean track.  More
precisely, its terminal is the terminal of a member of `clean`.  A target
track continuation would complete the starred component, contradicting its
membership in the pending part. -/
theorem CleanTargetSlice.exists_clean_tail_of_pendingStar
    {G : DWeb V} (hNorm : G.IsNormalized)
    {right U : Set V} {W : Set G.DPath}
    (S : CleanTargetSlice G (G.terminalFrontier (pendingPart G W)) right U)
    (hWfinite : G.HasFiniteCharacter (pendingPart G W))
    (hcompat : G.StarCompatible (pendingPart G W) (S.target ∪ S.clean))
    {r : G.DPath}
    (hr : r ∈ pendingPart G
      (freezeCompletedStar G W (S.target ∪ S.clean) hcompat)) :
    ∃ q ∈ S.clean, G.terminal? r = G.terminal? q := by
  have hrStar : r ∈ G.star hcompat :=
    pendingPart_freezeCompletedStar_subset_star
      G W (S.target ∪ S.clean) hcompat hr
  obtain ⟨old, rfl⟩ := hrStar
  rcases old with ⟨p, hpPending⟩
  obtain ⟨f, rfl⟩ := hWfinite hpPending
  have hfinishLeft : f.finish ∈
      G.terminalFrontier (pendingPart G W) :=
    ⟨Sum.inl f, hpPending, rfl⟩
  have hfinishInitial : f.finish ∈
      G.initialSet (S.target ∪ S.clean) := by
    rw [S.initialSet_union]
    exact hfinishLeft
  obtain ⟨q, hqUnion, hqInitial⟩ := hfinishInitial
  have hmatch : ∃ q ∈ S.target ∪ S.clean,
      q.initial = f.finish :=
    ⟨q, hqUnion, hqInitial⟩
  let chosen : G.DPath := Classical.choose hmatch
  have hchosenUnion : chosen ∈ S.target ∪ S.clean :=
    (Classical.choose_spec hmatch).1
  have hchosenInitial : chosen.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hchosenNotTarget : chosen ∉ S.target := by
    intro hchosenTarget
    have hchosenCompleted : chosen ∈ completedPart G S.target :=
      S.target_subset_completedPart hNorm hchosenTarget
    apply hr.2
    refine ⟨hr.1, ?_⟩
    obtain ⟨b, hbTarget, hchosenTerminal⟩ := hchosenCompleted.2
    refine ⟨b, hbTarget, ?_⟩
    simp only [DWeb.starPath]
    rw [dif_pos hmatch]
    exact (DirectedPath.Path.terminal?_appendFinite f chosen
      hchosenInitial _).trans hchosenTerminal
  have hchosenClean : chosen ∈ S.clean :=
    hchosenUnion.resolve_left hchosenNotTarget
  refine ⟨chosen, hchosenClean, ?_⟩
  simp only [DWeb.starPath]
  rw [dif_pos hmatch]
  exact DirectedPath.Path.terminal?_appendFinite f chosen
    hchosenInitial _

/-- The exposed terminals of the new pending row all come from the clean
track; target-track terminals disappear into the completed half. -/
theorem CleanTargetSlice.terminalFrontier_pendingPart_freezeCompletedStar_subset
    {G : DWeb V} (hNorm : G.IsNormalized)
    {right U : Set V} {W : Set G.DPath}
    (S : CleanTargetSlice G (G.terminalFrontier (pendingPart G W)) right U)
    (hWfinite : G.HasFiniteCharacter (pendingPart G W))
    (hcompat : G.StarCompatible (pendingPart G W) (S.target ∪ S.clean)) :
    G.terminalFrontier (pendingPart G
      (freezeCompletedStar G W (S.target ∪ S.clean) hcompat)) ⊆
        G.terminalFrontier S.clean := by
  rintro z ⟨r, hrPending, hrz⟩
  obtain ⟨q, hqClean, hrq⟩ :=
    S.exists_clean_tail_of_pendingStar hNorm hWfinite hcompat hrPending
  exact ⟨q, hqClean, hrq.symm.trans hrz⟩

/-- If the old pending row is already terminal-clean at the new right-hand
boundary, then its still-pending starred image remains terminal-clean there.
The only extra support is supplied by the clean track; a target-track tail
would have moved the component to the completed part. -/
theorem CleanTargetSlice.pendingPart_freezeCompletedStar_meetsOnlyAtTerminal
    {G : DWeb V} (hNorm : G.IsNormalized)
    {right U : Set V} {W : Set G.DPath}
    (S : CleanTargetSlice G (G.terminalFrontier (pendingPart G W)) right U)
    (hWfinite : G.HasFiniteCharacter (pendingPart G W))
    (hOldBoundary : MeetsOnlyAtTerminal G (pendingPart G W) right)
    (hcompat : G.StarCompatible (pendingPart G W) (S.target ∪ S.clean)) :
    MeetsOnlyAtTerminal G
      (pendingPart G
        (freezeCompletedStar G W (S.target ∪ S.clean) hcompat)) right := by
  intro r hrPending x hxr hxRight
  have hrStar : r ∈ G.star hcompat :=
    pendingPart_freezeCompletedStar_subset_star
      G W (S.target ∪ S.clean) hcompat hrPending
  obtain ⟨old, rfl⟩ := hrStar
  rcases old with ⟨p, hpPending⟩
  obtain ⟨f, rfl⟩ := hWfinite hpPending
  have hfinishLeft : f.finish ∈
      G.terminalFrontier (pendingPart G W) :=
    ⟨Sum.inl f, hpPending, rfl⟩
  have hfinishInitial : f.finish ∈
      G.initialSet (S.target ∪ S.clean) := by
    rw [S.initialSet_union]
    exact hfinishLeft
  obtain ⟨q, hqUnion, hqInitial⟩ := hfinishInitial
  have hmatch : ∃ q ∈ S.target ∪ S.clean,
      q.initial = f.finish :=
    ⟨q, hqUnion, hqInitial⟩
  let chosen : G.DPath := Classical.choose hmatch
  have hchosenUnion : chosen ∈ S.target ∪ S.clean :=
    (Classical.choose_spec hmatch).1
  have hchosenInitial : chosen.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hchosenNotTarget : chosen ∉ S.target := by
    intro hchosenTarget
    have hchosenCompleted : chosen ∈ completedPart G S.target :=
      S.target_subset_completedPart hNorm hchosenTarget
    apply hrPending.2
    refine ⟨hrPending.1, ?_⟩
    obtain ⟨b, hbTarget, hchosenTerminal⟩ := hchosenCompleted.2
    refine ⟨b, hbTarget, ?_⟩
    simp only [DWeb.starPath]
    rw [dif_pos hmatch]
    exact (DirectedPath.Path.terminal?_appendFinite f chosen
      hchosenInitial _).trans hchosenTerminal
  have hchosenClean : chosen ∈ S.clean :=
    hchosenUnion.resolve_left hchosenNotTarget
  simp only [DWeb.starPath] at hxr ⊢
  rw [dif_pos hmatch] at hxr ⊢
  have hinter : f.support ∩ chosen.support ⊆ {f.finish} := by
    intro y hy
    have hy' := hcompat (.inl f) hpPending chosen hchosenUnion
      y hy.1 hy.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
  rw [DirectedPath.Path.support_appendFinite f chosen
    hchosenInitial hinter] at hxr
  have hchosenTerminal : G.terminal? chosen = some x := by
    rcases hxr with hxf | hxc
    · have hfx : (some f.finish : Option V) = some x :=
        hOldBoundary (Sum.inl f) hpPending x hxf hxRight
      have hchosenStartX : chosen.initial = x :=
        hchosenInitial.trans (Option.some.inj hfx)
      exact S.clean_terminal_only chosen hchosenClean x
        (hchosenStartX ▸ chosen.initial_mem_support) hxRight
    · exact S.clean_terminal_only chosen hchosenClean x hxc hxRight
  exact (DirectedPath.Path.terminal?_appendFinite f chosen
    hchosenInitial hinter).trans hchosenTerminal

/-- Structural constructor for the next pending linkage.  Once the old
pending row is clean at the chosen later boundary, all the remaining
linkage fields follow from the split slice and the ordinary clean-step
facts.  In particular, no separate terminal-frontier or endpoint-purity
certificate for the new pending row is needed from a provider. -/
theorem CleanTargetSlice.pendingPart_freezeCompletedStar_tightLinkageBetween
    {G : DWeb V} (hNorm : G.IsNormalized)
    {right U : Set V} {W : Set G.DPath}
    (S : CleanTargetSlice G (G.terminalFrontier (pendingPart G W)) right U)
    (hInitialSource : G.initialSet W ⊆ G.source)
    (hWfinite : G.HasFiniteCharacter W)
    (hOldBoundary : MeetsOnlyAtTerminal G (pendingPart G W) right)
    (hcompat : G.StarCompatible (pendingPart G W) (S.target ∪ S.clean))
    (hstep : IsCleanTargetStep G W (S.target ∪ S.clean) hcompat)
    (hstarFinite : G.HasFiniteCharacter (G.star hcompat)) :
    TightLinkageBetween G
      (G.initialSet (pendingPart G
        (freezeCompletedStar G W (S.target ∪ S.clean) hcompat))) right
      (pendingPart G
        (freezeCompletedStar G W (S.target ∪ S.clean) hcompat)) := by
  let result := freezeCompletedStar G W (S.target ∪ S.clean) hcompat
  have hResultWarp : G.IsWarp result := hstep.result_isWarp
  have hResultFinite : G.HasFiniteCharacter result :=
    hstep.result_finiteCharacter hWfinite hstarFinite
  have hPendingWarp : G.IsWarp (pendingPart G result) := by
    intro p hp q hq hpq
    exact hResultWarp hp.1 hq.1 hpq
  have hPendingFinite : G.HasFiniteCharacter (pendingPart G result) := by
    intro p hp
    exact hResultFinite hp.1
  have hOldPendingFinite : G.HasFiniteCharacter (pendingPart G W) := by
    intro p hp
    exact hWfinite hp.1
  have hPendingInitialSource :
      G.initialSet (pendingPart G result) ⊆ G.source := by
    rintro x ⟨p, hp, rfl⟩
    apply hInitialSource
    rw [← hstep.result_initialSet]
    exact ⟨p, hp.1, rfl⟩
  apply tightLinkageBetween_of_structural hNorm hPendingInitialSource
    hPendingWarp hPendingFinite rfl
  · exact (S.terminalFrontier_pendingPart_freezeCompletedStar_subset
      hNorm hOldPendingFinite hcompat).trans S.clean_terminal
  · exact S.pendingPart_freezeCompletedStar_meetsOnlyAtTerminal
      hNorm hOldPendingFinite hOldBoundary hcompat

/-- Stage-relative classification for a single old prefix.  If its starred
image is still pending, the selected continuation is necessarily in the
clean track.  An ordinary clean member realizes the next exact ladder
prefix; a nonordinary one contributes its terminal to the stage-relative
maverick request. -/
theorem CleanTargetSlice.pendingStarPath_stagePrefix_or_maverickTerminal
    {G : DWeb V} (hNorm : G.IsNormalized)
    {kappa : Cardinal.{u}} {L : G.KappaLadder kappa}
    {alpha beta : Ladder.Stage kappa} {right U : Set V}
    {W : Set G.DPath}
    (S : CleanTargetSlice G (G.terminalFrontier (pendingPart G W)) right U)
    (hL : L.SliceGeometry)
    (hinterval : SliceCandidate.HasStageIntervalSegments
      G L S.clean alpha beta)
    (hcompat : G.StarCompatible (pendingPart G W) (S.target ∪ S.clean))
    (p : pendingPart G W)
    (hpPrefix : SliceSpliceConstructor.IsStagePrefix G L alpha p.1)
    (hpPending : G.starPath hcompat p ∈ pendingPart G
      (freezeCompletedStar G W (S.target ∪ S.clean) hcompat)) :
    SliceSpliceConstructor.IsStagePrefix G L beta (G.starPath hcompat p) ∨
      ∃ x ∈ G.terminalFrontier
          (ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean),
        G.terminal? (G.starPath hcompat p) = some x := by
  obtain ⟨fp, hpfp, hfpEssential, hfpFrontier⟩ := hpPrefix
  have hpW : (Sum.inl fp : G.DPath) ∈ pendingPart G W := hpfp ▸ p.2
  have peq : p = ⟨Sum.inl fp, hpW⟩ := Subtype.ext hpfp
  subst p
  have hfinishInitial : fp.finish ∈
      G.initialSet (S.target ∪ S.clean) := by
    rw [S.initialSet_union]
    exact ⟨Sum.inl fp, hpW, rfl⟩
  obtain ⟨q₀, hq₀Union, hq₀Initial⟩ := hfinishInitial
  have hmatch : ∃ q ∈ S.target ∪ S.clean,
      q.initial = fp.finish :=
    ⟨q₀, hq₀Union, hq₀Initial⟩
  let q : G.DPath := Classical.choose hmatch
  have hqUnion : q ∈ S.target ∪ S.clean :=
    (Classical.choose_spec hmatch).1
  have hqstart : q.initial = fp.finish :=
    (Classical.choose_spec hmatch).2
  have hqNotTarget : q ∉ S.target := by
    intro hqTarget
    have hqCompleted : q ∈ completedPart G S.target :=
      S.target_subset_completedPart hNorm hqTarget
    apply hpPending.2
    refine ⟨hpPending.1, ?_⟩
    obtain ⟨b, hbTarget, hqTerminal⟩ := hqCompleted.2
    refine ⟨b, hbTarget, ?_⟩
    simp only [DWeb.starPath]
    rw [dif_pos hmatch]
    exact (DirectedPath.Path.terminal?_appendFinite fp q hqstart _).trans
      hqTerminal
  have hqClean : q ∈ S.clean := hqUnion.resolve_left hqNotTarget
  have hinter : fp.support ∩ q.support ⊆ {fp.finish} := by
    intro x hx
    have hx' := hcompat (.inl fp) hpW q hqUnion x hx.1 hx.2
    exact Set.mem_singleton_iff.mpr (Option.some.inj hx'.1).symm
  have hstar :
      G.starPath hcompat (⟨Sum.inl fp, hpW⟩ : pendingPart G W) =
        DirectedPath.Path.appendFinite fp q hqstart hinter := by
    dsimp only [DWeb.starPath]
    split
    next hex =>
      let q' := Classical.choose hex
      have hq'Union : q' ∈ S.target ∪ S.clean :=
        (Classical.choose_spec hex).1
      have hq'start : q'.initial = fp.finish :=
        (Classical.choose_spec hex).2
      have hq'eq : q' = q :=
        DWeb.IsWarp.eq_of_initial_eq G S.union_warp hq'Union hqUnion
          (hq'start.trans hqstart.symm)
      dsimp only [q'] at hq'eq ⊢
    next hnone => exact (hnone hmatch).elim
  by_cases hqOrdinary :
      ControlledSlices.IsLadderFragment G (L.warpAt beta) q
  · obtain ⟨left, rightPrefix, segment, hqsegment, hleftEssential,
        hrightEssential, hleftFrontier, hrightFrontier,
        hsegmentStart, _hsegmentInter, _hinterEq, happend⟩ :=
      hinterval q hqClean hqOrdinary
    have hfinish : fp.finish = left.finish :=
      hqstart.symm.trans (hqsegment ▸ hsegmentStart)
    have hfpLeftPath :
        (Sum.inl fp : G.DPath) = Sum.inl left := by
      exact DWeb.IsWarp.eq_of_terminal_eq G
        (hL.warpStages (Ladder.Stage.toExtended alpha)).essentialWarpPart
        hfpEssential hleftEssential rfl (congrArg some hfinish.symm)
    have hfpLeft : fp = left := Sum.inl.inj hfpLeftPath
    left
    refine ⟨rightPrefix, ?_, hrightEssential, hrightFrontier⟩
    rw [hstar]
    subst left
    simpa only [hqsegment] using happend
  · right
    have hqMaverick : q ∈
        ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean :=
      ⟨hqClean, hqOrdinary⟩
    obtain ⟨fq, hqfinite⟩ := S.finiteCharacter (Or.inr hqClean)
    have hqMaverick' : (Sum.inl fq : G.DPath) ∈
        ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean := by
      simpa only [hqfinite] using hqMaverick
    refine ⟨fq.finish, ⟨Sum.inl fq, hqMaverick', rfl⟩, ?_⟩
    rw [hstar]
    calc
      G.terminal? (DirectedPath.Path.appendFinite fp q hqstart hinter) =
          G.terminal? q :=
        DirectedPath.Path.terminal?_appendFinite fp q hqstart hinter
      _ = some fq.finish := by rw [hqfinite]; rfl

/-- Aggregate status transport for the pending row.  Every old exception
whose terminal lies in the selected set `U` is completed by the target
track.  Thus a component which remains pending came from an old exact stage
prefix, and the preceding classification advances it either to the new
stage prefix or to the clean maverick request. -/
theorem CleanTargetSlice.pendingPart_freezeCompletedStar_status
    {G : DWeb V} (hNorm : G.IsNormalized)
    {kappa : Cardinal.{u}} {L : G.KappaLadder kappa}
    {alpha beta : Ladder.Stage kappa} {right U : Set V}
    {W : Set G.DPath}
    (S : CleanTargetSlice G (G.terminalFrontier (pendingPart G W)) right U)
    (hL : L.SliceGeometry)
    (hinterval : SliceCandidate.HasStageIntervalSegments
      G L S.clean alpha beta)
    (hcompat : G.StarCompatible (pendingPart G W) (S.target ∪ S.clean))
    (hOldStatus : ∀ p ∈ pendingPart G W,
      SliceSpliceConstructor.IsStagePrefix G L alpha p ∨
        ∃ x ∈ U, G.terminal? p = some x) :
    ∀ r ∈ pendingPart G
        (freezeCompletedStar G W (S.target ∪ S.clean) hcompat),
      SliceSpliceConstructor.IsStagePrefix G L beta r ∨
        ∃ x ∈ G.terminalFrontier
            (ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean),
          G.terminal? r = some x := by
  intro r hrPending
  have hrStar : r ∈ G.star hcompat :=
    pendingPart_freezeCompletedStar_subset_star
      G W (S.target ∪ S.clean) hcompat hrPending
  obtain ⟨old, rfl⟩ := hrStar
  rcases hOldStatus old.1 old.2 with hpPrefix | hpSelected
  · exact S.pendingStarPath_stagePrefix_or_maverickTerminal
      hNorm hL hinterval hcompat old hpPrefix hrPending
  · obtain ⟨x, hxU, hpTerminal⟩ := hpSelected
    exfalso
    apply hrPending.2
    refine ⟨hrPending.1, ?_⟩
    rcases old with ⟨p, hpW⟩
    rcases p with fp | ray
    · change some fp.finish = some x at hpTerminal
      have hfinish : fp.finish = x := Option.some.inj hpTerminal
      have hfinishTargetInitial : fp.finish ∈ G.initialSet S.target := by
        rw [S.target_initial, hfinish]
        exact hxU
      obtain ⟨q, hqTarget, hqStart⟩ := hfinishTargetInitial
      have hmatch : ∃ q ∈ S.target ∪ S.clean,
          q.initial = fp.finish :=
        ⟨q, Or.inl hqTarget, hqStart⟩
      let chosen : G.DPath := Classical.choose hmatch
      have hchosenUnion : chosen ∈ S.target ∪ S.clean :=
        (Classical.choose_spec hmatch).1
      have hchosenStart : chosen.initial = fp.finish :=
        (Classical.choose_spec hmatch).2
      have hchosenEq : chosen = q := by
        apply DWeb.IsWarp.eq_of_initial_eq G S.union_warp
          hchosenUnion (Or.inl hqTarget)
        exact hchosenStart.trans hqStart.symm
      have hchosenCompleted : chosen ∈ completedPart G S.target := by
        rw [hchosenEq]
        exact S.target_subset_completedPart hNorm hqTarget
      obtain ⟨b, hbTarget, hchosenTerminal⟩ := hchosenCompleted.2
      refine ⟨b, hbTarget, ?_⟩
      simp only [DWeb.starPath]
      rw [dif_pos hmatch]
      exact (DirectedPath.Path.terminal?_appendFinite fp chosen
        hchosenStart _).trans hchosenTerminal
    · simp at hpTerminal

/-- A selected target coordinate of a `CleanTargetSlice` completes the old
pending component which ends there.  This is the source-faithful replacement
for taking `resolves_pending` as an abstract stage-provider fact. -/
theorem CleanTargetSlice.exists_completed_starPath
    {G : DWeb V} (hNorm : G.IsNormalized)
    {left right U : Set V} (S : CleanTargetSlice G left right U)
    {old : Set G.DPath}
    (hcompat : G.StarCompatible old (S.target ∪ S.clean))
    {p : G.DPath} (hp : p ∈ old) {a : V}
    (hpa : G.terminal? p = some a) (ha : a ∈ U) :
    ∃ q ∈ G.star hcompat,
      q.initial = p.initial ∧
        SliceSpliceConstructor.ReachesTarget G q := by
  obtain ⟨t, htTarget, f, rfl, hfPure, _before, _after, hsupport,
      b, hbTarget, hbAfter⟩ := S.target_links a ha
  have haSupport : a ∈ f.support := by
    have haInter : a ∈ f.support ∩ U := by
      rw [hfPure]
      exact Set.mem_singleton a
    exact haInter.1
  have hfInitialU : f.start ∈ U := by
    rw [← S.target_initial]
    exact ⟨Sum.inl f, htTarget, rfl⟩
  have hfStart : f.start = a := by
    have hstartInter : f.start ∈ f.support ∩ U :=
      ⟨f.start_mem_support, hfInitialU⟩
    rw [hfPure] at hstartInter
    exact Set.mem_singleton_iff.mp hstartInter
  have hbSupport : b ∈ f.support := by
    change b ∈ f.walk.support
    rw [hsupport]
    exact List.mem_append_right _ hbAfter
  have hbFinish : b = f.finish :=
    hNorm.eq_finish_of_mem_walk f.walk hbSupport hbTarget
  rcases p with g | ray
  · change some g.finish = some a at hpa
    have hgFinish : g.finish = a := Option.some.inj hpa
    let oldPath : old := ⟨Sum.inl g, hp⟩
    let targetPath : G.DPath := Sum.inl f
    have htargetUnion : targetPath ∈ S.target ∪ S.clean :=
      Or.inl htTarget
    have hmatch : ∃ q ∈ S.target ∪ S.clean,
        q.initial = g.finish :=
      ⟨targetPath, htargetUnion, hfStart.trans hgFinish.symm⟩
    let chosen : G.DPath := Classical.choose hmatch
    have hchosenMem : chosen ∈ S.target ∪ S.clean :=
      (Classical.choose_spec hmatch).1
    have hchosenInitial : chosen.initial = g.finish :=
      (Classical.choose_spec hmatch).2
    have hchosenEq : chosen = targetPath := by
      apply DWeb.IsWarp.eq_of_initial_eq G S.union_warp
        hchosenMem htargetUnion
      exact hchosenInitial.trans (hfStart.trans hgFinish.symm).symm
    let q := G.starPath hcompat oldPath
    have hqMem : q ∈ G.star hcompat := ⟨oldPath, rfl⟩
    have hqInitial : q.initial = g.start :=
      G.initial_starPath hcompat oldPath
    refine ⟨q, hqMem, hqInitial, b, hbTarget, ?_⟩
    dsimp only [q, oldPath]
    simp only [DWeb.starPath]
    rw [dif_pos hmatch]
    calc
      G.terminal? (DirectedPath.Path.appendFinite g
          (Classical.choose hmatch) _ _) =
          (Classical.choose hmatch).terminal? :=
        DirectedPath.Path.terminal?_appendFinite g
          (Classical.choose hmatch) _ _
      _ = some b := by
        change chosen.terminal? = some b
        rw [hchosenEq]
        exact congrArg some hbFinish.symm
  · simp at hpa

/-- Equality-transported form of `exists_completed_starPath`.  A global
provider normally names the family it installs independently of the
target/clean decomposition.  This lemma keeps the resulting `star` in the
provider's original compatibility proof, so no proof-dependent cast escapes
into the recursive payload. -/
theorem CleanTargetSlice.exists_completed_starPath_of_installed_eq
    {G : DWeb V} (hNorm : G.IsNormalized)
    {left right U : Set V} (S : CleanTargetSlice G left right U)
    {old T : Set G.DPath}
    (hT : T = S.target ∪ S.clean)
    (hcompat : G.StarCompatible old T)
    {p : G.DPath} (hp : p ∈ old) {a : V}
    (hpa : G.terminal? p = some a) (ha : a ∈ U) :
    ∃ q ∈ G.star hcompat,
      q.initial = p.initial ∧
        SliceSpliceConstructor.ReachesTarget G q := by
  subst T
  exact S.exists_completed_starPath hNorm hcompat hp hpa ha

/-! ## Future-safe completed components -/

/-- Safety of a target path chosen in a vertex-deleted residual web
transports to deletion of its ambient lift together with the already frozen
carrier.  This is the elementary successor step behind the
`completed_safe` invariant below. -/
theorem isUnhindered_delete_union_liftDeletePath
    (G : DWeb V) (Q : Set V)
    (p : DirectedPath.FinitePath (G.delete Q).graph)
    (hp : ((G.delete Q).delete p.support).IsUnhindered) :
    (G.delete (Q ∪ (G.liftDeletePath Q (Sum.inl p)).support)).IsUnhindered := by
  rw [G.support_liftDeletePath]
  change (G.delete (Q ∪ p.support)).IsUnhindered
  simpa only [G.delete_delete] using hp

/-- The accumulated chain contract needed by the final regular splice.  Its
stages may contain both frozen completed components and clean pending ones;
there is no false assertion that a completed component ends on every later
ladder frontier. -/
structure IsCompletedPendingSplice
    {I : Type v} [LinearOrder I]
    (G : DWeb V) (A Z : Set V) (C : G.GrowingWarpChain I) : Prop where
  initialUnion_eq : C.initialUnion = A
  vertices_closed : ∀ i, G.vertexSet (C.stage i) ⊆ Z
  eventually_completed : ∀ a : A, ∃ i p,
    p ∈ C.stage i ∧ p.initial = a.1 ∧
      SliceSpliceConstructor.ReachesTarget G p

/-- Final consumer for the two-track regular splice.  A completed member is
terminal-cofinal in its source thread, hence the thread limit gives the
required target linkage. -/
theorem IsCompletedPendingSplice.exists_internal_linkage
    {I : Type v} [LinearOrder I]
    {G : DWeb V} {A Z : Set V} {C : G.GrowingWarpChain I}
    (h : IsCompletedPendingSplice G A Z C)
    (hNorm : G.IsNormalized) (hA : A ⊆ G.source) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G A G.target P ∧ G.vertexSet P ⊆ Z := by
  have hterminal : ∀ a : C.initialUnion,
      ∃ b ∈ G.target,
        DirectedPath.Path.TerminalCofinal (C.thread G a.1) b := by
    intro a
    have haA : a.1 ∈ A := h.initialUnion_eq ▸ a.2
    obtain ⟨i, p, hp, hpinitial, b, hbTarget, hpterm⟩ :=
      h.eventually_completed ⟨a.1, haA⟩
    exact ⟨b, hbTarget,
      SliceSpliceConstructor.terminalCofinal_of_thread_member_target
        hNorm C a hp hpinitial hbTarget hpterm⟩
  have hboundary : ∀ i,
      MeetsOnlyAtTerminal G (C.stage i) G.target := by
    intro i p hp b hbp hbTarget
    exact hNorm.terminal?_eq_of_mem_path p hbp hbTarget
  have htight : TightLinkageBetween G A G.target (C.limitPaths G) :=
    tightLinkageBetween_limitPaths_of_terminalCofinal C hNorm hA
      h.initialUnion_eq hterminal hboundary
  refine ⟨C.limitPaths G, htight.1, ?_⟩
  exact vertexSet_limitPaths_subset_of_stages h.vertices_closed

/-! ## A minimal recursive consumer

The provider may need the whole earlier history in order to construct the
clean state at a limit and to avoid all frozen target components.  Encoding
that dependence explicitly is both weaker and sounder than a stage-only
candidate table.  The following interface is the regular replacement for
`HasTrackedTightAnnularControlledSlices`: the provider returns a full
completed/pending row, proves that it extends every earlier row, and realizes
the one source scheduled at the current recursion index.
-/

structure RecursivePayload
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  row : Set G.DPath
  isWarp : G.IsWarp row
  finiteCharacter : G.HasFiniteCharacter row
  initialSet_eq : G.initialSet row = A
  vertices_closed : G.vertexSet row ⊆ Z
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G row)) (L.frontier stageIndex)
      (pendingPart G row)
  pending_below_roof : G.vertexSet (pendingPart G row) ⊆
    G.roof (L.frontier stageIndex)
  pendingRequest : Set V
  pendingRequest_subset : pendingRequest ⊆ L.frontier stageIndex ∩ Z
  pendingRequest_small : #pendingRequest < kappa
  pending_status : ∀ p ∈ pendingPart G row,
    SliceSpliceConstructor.IsStagePrefix G L stageIndex p ∨
      ∃ x ∈ pendingRequest, G.terminal? p = some x

namespace RecursivePayload

/-- A payload's pending row is terminal-clean at every strictly later
ladder frontier.  The payload already lies below and is tight at its own
frontier; legal-ladder strict chronology supplies the only new fact. -/
theorem pending_meetsOnlyAtTerminal_later
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (S : RecursivePayload G L Sigma Z A)
    (hL : L.SliceGeometry) {beta : Ladder.Stage kappa}
    (hbeta : S.stageIndex < beta) :
    MeetsOnlyAtTerminal G (pendingPart G S.row) (L.frontier beta) := by
  exact meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
    (hL.frontiersEssential S.stageIndex) S.pending_below_roof
      S.pending_tight.2 (hL.strictFrontierChronology hbeta)

end RecursivePayload

structure IsValidRecursiveStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RecursivePayload G L Sigma Z A)
    (current : RecursivePayload G L Sigma Z A) : Prop where
  index_strict : ∀ j (hji : j < i),
    (previous j hji).stageIndex < current.stageIndex
  extends_previous : ∀ j (hji : j < i),
    G.ForwardExtension (previous j hji).row current.row
  freezes_completed : ∀ j (hji : j < i),
    completedPart G (previous j hji).row ⊆ completedPart G current.row
  resolves_pending : ∀ j (hji : j < i) p,
    p ∈ pendingPart G (previous j hji).row →
    (∃ x ∈ (previous j hji).pendingRequest,
      G.terminal? p = some x) →
      ∃ q ∈ completedPart G current.row, q.initial = p.initial
  realizes_request : ∀ a : A, request i = some a →
    ∃ p ∈ completedPart G current.row, p.initial = a.1

/-- A history-sensitive clean/target provider.  At a limit index the
`previous` argument exposes all frozen components, so the provider can prove
the cross-disjointness required by `IsCleanTargetStep`. -/
def HasCleanTargetStepProvider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        RecursivePayload G L Sigma Z A),
    (∀ j (hji : j < i),
      IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      ∃ current : RecursivePayload G L Sigma Z A,
        IsValidRecursiveStage request i previous current

structure RecursiveSpliceOperation
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A) where
  build : ∀ i : Ladder.Stage kappa,
    (∀ j : Ladder.Stage kappa, j < i →
      RecursivePayload G L Sigma Z A) →
      RecursivePayload G L Sigma Z A
  valid : ∀ i previous,
    (∀ j (hji : j < i),
      IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      IsValidRecursiveStage request i previous (build i previous)

/-- Choice totalizes a history-sensitive provider.  `fallback` is observed
only on invalid hypothetical histories; recursion along the actual history
always takes the certified branch. -/
theorem exists_recursiveSpliceOperation
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (fallback : RecursivePayload G L Sigma Z A)
    (hprovider : HasCleanTargetStepProvider G L Sigma Z A request) :
    ∃ _R : RecursiveSpliceOperation G L Sigma Z A request, True := by
  let build : ∀ i : Ladder.Stage kappa,
      (∀ j : Ladder.Stage kappa, j < i →
        RecursivePayload G L Sigma Z A) →
        RecursivePayload G L Sigma Z A :=
    fun i previous ↦ by
      classical
      exact if h : ∃ current,
          IsValidRecursiveStage request i previous current then
        Classical.choose h
      else fallback
  let R : RecursiveSpliceOperation G L Sigma Z A request :=
    { build := build
      valid := by
        intro i previous hprevious
        have hexists := hprovider i previous hprevious
        dsimp only [build]
        rw [dif_pos hexists]
        exact Classical.choose_spec hexists }
  exact ⟨R, trivial⟩

namespace RecursiveSpliceOperation

variable {kappa : Cardinal.{u}} {G : DWeb V}
variable {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
variable {Z A : Set V}
variable {request : Ladder.Stage kappa → Option A}

noncomputable def payload
    (R : RecursiveSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) : RecursivePayload G L Sigma Z A :=
  WellFounded.fix wellFounded_lt
    (fun i previous ↦ R.build i previous) i

theorem payload_eq
    (R : RecursiveSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    R.payload i = R.build i (fun j _hji ↦ R.payload j) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun i previous ↦ R.build i previous) i

theorem payload_valid
    (R : RecursiveSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    IsValidRecursiveStage request i (fun j _hji ↦ R.payload j)
      (R.payload i) := by
  rw [R.payload_eq i]
  apply R.valid
  intro j hji
  simpa only using R.payload_valid j
termination_by i.1
decreasing_by exact hji

noncomputable def growingChain
    (R : RecursiveSpliceOperation G L Sigma Z A request) :
    G.GrowingWarpChain (Ladder.Stage kappa) where
  stage i := (R.payload i).row
  isWarp i := (R.payload i).isWarp
  grows := by
    intro i j hij p hp
    rcases hij.lt_or_eq with hij | rfl
    · exact (R.payload_valid j).extends_previous i hij |>.1 p hp
    · exact ⟨p, hp, G.extends_refl p⟩

@[simp]
theorem growingChain_stage
    (R : RecursiveSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    R.growingChain.stage i = (R.payload i).row := rfl

theorem initialUnion_growingChain
    (R : RecursiveSpliceOperation G L Sigma Z A request)
    (i0 : Ladder.Stage kappa) :
    R.growingChain.initialUnion = A := by
  apply Set.Subset.antisymm
  · rintro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    change x ∈ G.initialSet (R.payload i).row at hxi
    rw [(R.payload i).initialSet_eq] at hxi
    exact hxi
  · intro x hx
    exact Set.mem_iUnion.2 ⟨i0,
      (R.payload i0).initialSet_eq.symm ▸ hx⟩

theorem isCompletedPendingSplice
    (R : RecursiveSpliceOperation G L Sigma Z A request)
    (i0 : Ladder.Stage kappa)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    IsCompletedPendingSplice G A Z R.growingChain := by
  refine
    { initialUnion_eq := R.initialUnion_growingChain i0
      vertices_closed := ?_
      eventually_completed := ?_ }
  · intro i
    exact (R.payload i).vertices_closed
  · intro a
    obtain ⟨i, hi⟩ := hrequest a
    obtain ⟨p, hp, hpinitial⟩ :=
      (R.payload_valid i).realizes_request a hi
    exact ⟨i, p, hp.1, hpinitial, hp.2⟩

theorem exists_internal_linkage
    (R : RecursiveSpliceOperation G L Sigma Z A request)
    (hNorm : G.IsNormalized) (hA : A ⊆ G.source)
    (i0 : Ladder.Stage kappa)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G A G.target P ∧ G.vertexSet P ⊆ Z := by
  exact (R.isCompletedPendingSplice i0 hrequest).exists_internal_linkage
    hNorm hA

end RecursiveSpliceOperation

/-- Public assembly theorem for the revised regular provider.  It has the
same linkage conclusion as the old tracked-annular splice, but its provider
is history-sensitive and therefore can freeze target completions safely. -/
theorem exists_internal_linkage_of_cleanTargetStepProvider
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z : Set V}
    (hNorm : G.IsNormalized)
    (hAcard : #↑(G.source ∩ Z) ≤ kappa)
    (i0 : Ladder.Stage kappa)
    (hi0 : ∀ j : Ladder.Stage kappa, ¬ j < i0)
    (hprovider : ∀ request :
      Ladder.Stage kappa → Option ↑(G.source ∩ Z),
      HasCleanTargetStepProvider G L Sigma Z (G.source ∩ Z) request) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G (G.source ∩ Z) G.target P ∧
        G.vertexSet P ⊆ Z := by
  obtain ⟨request, hrequest⟩ :=
    SliceSpliceConstructor.exists_coveringSourceRequest hAcard
  let previous : ∀ j : Ladder.Stage kappa, j < i0 →
      RecursivePayload G L Sigma Z (G.source ∩ Z) :=
    fun j hji ↦ (hi0 j hji).elim
  have hprevious : ∀ j (hji : j < i0),
      IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji) := by
    intro j hji
    exact (hi0 j hji).elim
  obtain ⟨fallback, _hfallback⟩ :=
    hprovider request i0 previous hprevious
  obtain ⟨R, _⟩ := exists_recursiveSpliceOperation fallback
    (hprovider request)
  exact R.exists_internal_linkage hNorm Set.inter_subset_left
    i0 hrequest

end RegularCompletedPendingSplice
end CardinalInduction
end Erdos599
