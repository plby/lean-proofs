/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalAdmissibleProvider

/-!
# Non-circular canonical successor geometry

The global comparison-stage record stores the tight linkage and status of
the *resulting* pending row.  Those facts are conclusions of the source-9.15
successor argument, not independent provider data.  This file gives the raw
successor boundary: it retains the full comparison/shadow geometry and the
literal clean-track provenance, but asks only for boundary purity and status
of the old pending row.  The completed/pending split lemmas then derive the
two resulting invariants and package the existing `CanonicalStage`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCanonicalSuccessor

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- Restrict a full tracked frontier slice to the terminal coordinates of
the current pending row, splitting the selected coordinates from the clean
complement.  This is the literal two-track slice used in paragraph 9.15;
no completion or history-sensitive avoidance assertion is built into the
partition. -/
def cleanTargetSliceOfTracked
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    RegularCompletedPendingSplice.CleanTargetSlice
      G left (L.frontier beta) U where
  target := initialRestriction G T U
  clean := initialRestriction G T (left \ U)
  union_warp := by
    intro p hp q hq hpq
    apply hT.1.1.1.1.1.isWarp
    · exact hp.elim (fun h ↦ h.1) (fun h ↦ h.1)
    · exact hq.elim (fun h ↦ h.1) (fun h ↦ h.1)
    · exact hpq
  finiteCharacter := by
    intro p hp
    exact hT.1.1.1.1.1.finiteCharacter
      (hp.elim (fun h ↦ h.1) (fun h ↦ h.1))
  target_initial :=
    (isLinkageBetween_initialRestriction hT.1.1.1.1.1
      (hUleft.trans hleft)).initialSet_eq
  clean_initial :=
    (isLinkageBetween_initialRestriction hT.1.1.1.1.1
      (Set.sdiff_subset.trans hleft)).initialSet_eq
  initial_cover := hUleft
  target_links := by
    intro a ha
    obtain ⟨q, hqT, f, hqf, hpure, hsuffix⟩ := hT.1.1.1.1.2 a ha
    have haSupport : a ∈ f.support := by
      have haInter : a ∈ f.support ∩ U := by
        rw [hpure]
        exact Set.mem_singleton a
      exact haInter.1
    have haFrontier : a ∈ L.frontier alpha := hleft (hUleft ha)
    have hqInitial : q.initial = a := by
      exact SliceSpliceConstructor.slice_meets_frontier_only_at_initial
        hT.1.1.1.1 q hqT a (hqf ▸ haSupport) haFrontier
    exact ⟨q, ⟨hqT, hqInitial ▸ ha⟩, f, hqf, hpure, hsuffix⟩
  clean_terminal := by
    rintro x ⟨p, hp, hpx⟩
    exact hT.1.1.1.1.1.terminalFrontier_subset ⟨p, hp.1, hpx⟩
  clean_terminal_only := by
    intro p hp
    exact hT.1.1.2 p hp.1
  source_pure := by
    intro p hp
    have hpT : p ∈ T := hp.elim (fun h ↦ h.1) (fun h ↦ h.1)
    have hpLeft : p.initial ∈ left := by
      rcases hp with hp | hp
      · exact hUleft hp.2
      · exact hp.2.1
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxleft⟩
      apply Set.mem_singleton_iff.2
      exact (SliceSpliceConstructor.slice_meets_frontier_only_at_initial
        hT.1.1.1.1 p hpT x hxp (hleft hxleft)).symm
    · intro x hx
      subst x
      exact ⟨p.initial_mem_support, hpLeft⟩

@[simp] theorem cleanTargetSliceOfTracked_target
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    (cleanTargetSliceOfTracked hT hleft hUleft).target =
      initialRestriction G T U :=
  rfl

@[simp] theorem cleanTargetSliceOfTracked_clean
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    (cleanTargetSliceOfTracked hT hleft hUleft).clean =
      initialRestriction G T (left \ U) :=
  rfl

/-- The installed target/clean union is exactly the restriction of the full
9.15 comparison family to current pending coordinates. -/
theorem cleanTargetSliceOfTracked_union_eq
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    (cleanTargetSliceOfTracked hT hleft hUleft).target ∪
        (cleanTargetSliceOfTracked hT hleft hUleft).clean =
      initialRestriction G T left := by
  ext p
  simp only [cleanTargetSliceOfTracked_target,
    cleanTargetSliceOfTracked_clean, mem_initialRestriction,
    Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro (⟨hpT, hpU⟩ | ⟨hpT, hpLeft, _hpU⟩)
    · exact ⟨hpT, hUleft hpU⟩
    · exact ⟨hpT, hpLeft⟩
  · rintro ⟨hpT, hpLeft⟩
    by_cases hpU : p.initial ∈ U
    · exact Or.inl ⟨hpT, hpU⟩
    · exact Or.inr ⟨hpT, hpLeft, hpU⟩

theorem cleanTargetSliceOfTracked_installed_subset
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    (cleanTargetSliceOfTracked hT hleft hUleft).target ∪
        (cleanTargetSliceOfTracked hT hleft hUleft).clean ⊆ T := by
  rw [cleanTargetSliceOfTracked_union_eq hT hleft hUleft]
  exact fun _ hp ↦ hp.1

theorem cleanTargetSliceOfTracked_cleanIntervals
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    SliceCandidate.HasStageIntervalSegments G L
      (cleanTargetSliceOfTracked hT hleft hUleft).clean alpha beta := by
  intro p hp
  exact hT.2.1 p hp.1

theorem cleanTargetSliceOfTracked_cleanMavericks_small
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    #(ControlledSlices.sliceMavericks G (L.warpAt beta)
      (cleanTargetSliceOfTracked hT hleft hUleft).clean) < kappa := by
  apply (Cardinal.mk_subtype_mono ?_).trans_lt hT.2.2.1
  intro p hp
  exact ⟨hp.1.1, hp.2⟩

theorem cleanTargetSliceOfTracked_cleanMavericks_closed
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Z left U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : left ⊆ L.frontier alpha) (hUleft : U ⊆ left) :
    G.vertexSet (ControlledSlices.sliceMavericks G (L.warpAt beta)
      (cleanTargetSliceOfTracked hT hleft hUleft).clean) ⊆ Z := by
  rintro x ⟨p, hp, hxp⟩
  exact hT.2.2.2 ⟨p, ⟨hp.1.1, hp.2⟩, hxp⟩

/-- If the *whole* base row retains the source proof's tight/roofed
invariant, the full tracked 9.15 slice is already the required comparison
warp.  A completed base component has no point outside the old strict roof
except its terminal.  The full slice has a component rooted at that terminal,
and that component is not in the pending-terminal restriction. -/
theorem completedShadow_of_roofedTightBase
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Z A U : Set V} {alpha beta : Ladder.Stage kappa}
    {base T : Set G.DPath}
    (hbase : TightLinkageBetween G A (L.frontier alpha) base)
    (hbaseRoof : G.vertexSet base ⊆ G.roof (L.frontier alpha))
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T) :
    ∀ f ∈ completedPart G base,
      ∃ t ∈ T,
        t ∉ initialRestriction G T
          (G.terminalFrontier (pendingPart G base)) ∧
        f.support \ G.strictRoof (L.frontier alpha) ⊆ t.support := by
  intro f hf
  obtain ⟨b, hbTarget, hfb⟩ := hf.2
  have hbFrontier : b ∈ L.frontier alpha :=
    hbase.1.terminalFrontier_subset ⟨f, hf.1, hfb⟩
  have hbInitialT : b ∈ G.initialSet T :=
    hT.1.1.1.1.1.initialSet_eq.symm ▸ hbFrontier
  obtain ⟨t, htT, htInitial⟩ := hbInitialT
  have htNotUsed : t ∉ initialRestriction G T
      (G.terminalFrontier (pendingPart G base)) := by
    intro htUsed
    obtain ⟨p, hpPending, hpb⟩ := htInitial ▸ htUsed.2
    have hpf : p = f := by
      by_contra hne
      exact Set.disjoint_left.1 (hbase.1.isWarp hpPending.1 hf.1 hne)
        (G.terminal_mem_support hpb) (G.terminal_mem_support hfb)
    subst p
    exact hpPending.2 hf
  refine ⟨t, htT, htNotUsed, ?_⟩
  rintro x ⟨hxf, hxNotStrict⟩
  have hxRoof : x ∈ G.roof (L.frontier alpha) :=
    hbaseRoof ⟨f, hf.1, hxf⟩
  have hxEssential : x ∈ G.essential (L.frontier alpha) := by
    by_contra hx
    exact hxNotStrict ⟨hxRoof, hx⟩
  have hxFrontier : x ∈ L.frontier alpha := by
    rw [hL.frontiersEssential alpha] at hxEssential
    exact hxEssential
  have hfx : G.terminal? f = some x :=
    hbase.2 f hf.1 x hxf hxFrontier
  have hxb : x = b := Option.some.inj (hfx.symm.trans hfb)
  subst x
  rw [← htInitial]
  exact t.initial_mem_support

/-- The stronger source-specific invariant is preserved by an exact tracked
slice.  This is deliberately not claimed for an arbitrary
`TargetedComparisonStage`: it uses that both target and clean tracks are
restrictions of one full right-tight annular slice. -/
theorem freezeCompletedStar_roofedTight_of_cleanTarget
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hNorm : G.IsNormalized) (hL : L.IsSplitLegal)
    {Z A U : Set V} {alpha beta : Ladder.Stage kappa}
    {base T : Set G.DPath}
    (hA : A ⊆ G.source) (hab : alpha < beta)
    (hbase : TightLinkageBetween G A (L.frontier alpha) base)
    (hbaseRoof : G.vertexSet base ⊆ G.roof (L.frontier alpha))
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hleft : G.terminalFrontier (pendingPart G base) ⊆
      L.frontier alpha)
    (hU : U ⊆ G.terminalFrontier (pendingPart G base))
    (S : RegularCompletedPendingSplice.CleanTargetSlice G
      (G.terminalFrontier (pendingPart G base)) (L.frontier beta) U)
    (hS : S = cleanTargetSliceOfTracked hT hleft hU)
    (hcompat : G.StarCompatible (pendingPart G base)
      (S.target ∪ S.clean)) :
    TightLinkageBetween G A (L.frontier beta)
        (RegularCompletedPendingSplice.freezeCompletedStar G base
          (S.target ∪ S.clean) hcompat) ∧
      G.vertexSet
        (RegularCompletedPendingSplice.freezeCompletedStar G base
          (S.target ∪ S.clean) hcompat) ⊆
        G.roof (L.frontier beta) := by
  subst S
  let S := cleanTargetSliceOfTracked hT hleft hU
  have hpendingRoof : G.vertexSet (pendingPart G base) ⊆
      G.roof (L.frontier alpha) := by
    rintro x ⟨p, hp, hxp⟩
    exact hbaseRoof ⟨p, hp.1, hxp⟩
  have hpendingBoundary : MeetsOnlyAtTerminal G (pendingPart G base)
      (L.frontier alpha) := fun p hp ↦ hbase.2 p hp.1
  have hST : S.target ∪ S.clean ⊆ T :=
    cleanTargetSliceOfTracked_installed_subset hT hleft hU
  have hcompatBase : G.StarCompatible base T :=
    SliceSpliceConstructor.starCompatible_of_annular
      (hL.frontiersEssential alpha)
      hbaseRoof hbase.2 hT.1.1.1
  have hcross : Disjoint (G.vertexSet (completedPart G base))
      (G.vertexSet (S.target ∪ S.clean)) := by
    apply Set.disjoint_left.2
    intro x hxDone hxInstalled
    obtain ⟨f, hfDone, hxf⟩ := hxDone
    obtain ⟨q, hqInstalled, hxq⟩ := hxInstalled
    have hinter := hcompatBase f hfDone.1 q (hST hqInstalled) x hxf hxq
    have hqLeft : q.initial ∈
        G.terminalFrontier (pendingPart G base) := by
      rw [← S.initialSet_union]
      exact ⟨q, hqInstalled, rfl⟩
    obtain ⟨p, hpPending, hpq⟩ := hqLeft
    have hpx : G.terminal? p = some x :=
      hpq.trans (congrArg some hinter.2)
    have hpf : p = f := by
      by_contra hne
      exact Set.disjoint_left.1 (hbase.1.isWarp hpPending.1 hfDone.1 hne)
        (G.terminal_mem_support hpx) hxf
    subst p
    exact hpPending.2 hfDone
  have hstep : RegularCompletedPendingSplice.IsCleanTargetStep G base
      (S.target ∪ S.clean) hcompat :=
    RegularCompletedPendingSplice.IsCleanTargetStep.of_disjoint_slice
      hbase.1.isWarp S.union_warp hcross
  have hpendingFinite : G.HasFiniteCharacter (pendingPart G base) := by
    intro p hp
    exact hbase.1.finiteCharacter hp.1
  have hstarFinite : G.HasFiniteCharacter (G.star hcompat) :=
    hasFiniteCharacter_star hpendingFinite S.finiteCharacter hcompat
  let result := RegularCompletedPendingSplice.freezeCompletedStar G base
    (S.target ∪ S.clean) hcompat
  have hresultWarp : G.IsWarp result := hstep.result_isWarp
  have hresultFinite : G.HasFiniteCharacter result :=
    hstep.result_finiteCharacter hbase.1.finiteCharacter hstarFinite
  have hresultInitial : G.initialSet result = A :=
    hstep.result_initialSet.trans hbase.1.initialSet_eq
  have hcover : G.terminalFrontier (pendingPart G base) ⊆
      G.initialSet (S.target ∪ S.clean) := by
    rw [S.initialSet_union]
  have hinstalledTerminal : G.terminalFrontier (S.target ∪ S.clean) ⊆
      L.frontier beta := by
    rintro x ⟨p, hp, hpx⟩
    exact hT.1.1.1.1.1.terminalFrontier_subset ⟨p, hST hp, hpx⟩
  have hstarTerminal : G.terminalFrontier (G.star hcompat) ⊆
      L.frontier beta :=
    (terminalFrontier_star_subset hpendingFinite hcompat hcover).trans
      hinstalledTerminal
  have hcompletedTerminal : G.terminalFrontier (completedPart G base) ⊆
      L.frontier beta := by
    rintro b ⟨p, hp, hpb⟩
    obtain ⟨c, hcTarget, hpc⟩ := hp.2
    have hbc : b = c := Option.some.inj (hpb.symm.trans hpc)
    subst b
    have hcAlpha : c ∈ L.frontier alpha :=
      hbase.1.terminalFrontier_subset ⟨p, hp.1, hpc⟩
    exact SliceSpliceConstructor.target_mem_of_mem_roof hcTarget
      (hL.frontierChronology hab hcAlpha)
  have hresultTerminal : G.terminalFrontier result ⊆ L.frontier beta := by
    rintro x ⟨p, hp, hpx⟩
    rcases hp with hpDone | hpStar
    · exact hcompletedTerminal ⟨p, hpDone, hpx⟩
    · exact hstarTerminal ⟨p, hpStar, hpx⟩
  have holdLater : MeetsOnlyAtTerminal G base (L.frontier beta) :=
    meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      (hL.frontiersEssential alpha) hbaseRoof hbase.2
        (hL.strictFrontierChronology hab)
  have hpendingLater : MeetsOnlyAtTerminal G (pendingPart G base)
      (L.frontier beta) := fun p hp ↦ holdLater p hp.1
  have hinstalledLater : MeetsOnlyAtTerminal G (S.target ∪ S.clean)
      (L.frontier beta) := fun p hp ↦ hT.1.1.2 p (hST hp)
  have hstarLater : MeetsOnlyAtTerminal G (G.star hcompat)
      (L.frontier beta) :=
    meetsOnlyAtTerminal_star hpendingFinite hpendingLater
      hinstalledLater hcompat hcover
  have hresultLater : MeetsOnlyAtTerminal G result (L.frontier beta) := by
    intro p hp
    exact hp.elim (fun hpDone ↦ holdLater p hpDone.1)
      (fun hpStar ↦ hstarLater p hpStar)
  have hresultTight : TightLinkageBetween G A (L.frontier beta) result := by
    apply tightLinkageBetween_of_structural hNorm hA hresultWarp
      hresultFinite hresultInitial
    · exact hresultTerminal
    · exact hresultLater
  have hinstalledRoof : G.vertexSet (S.target ∪ S.clean) ⊆
      G.roof (L.frontier beta) := by
    rintro x ⟨p, hp, hxp⟩
    exact (hT.1.1.1.2 ⟨p, hST hp, hxp⟩).2
  have hstarRoof : G.vertexSet (G.star hcompat) ⊆
      G.roof (L.frontier beta) :=
    vertexSet_star_subset_roof hcompat (hL.frontierChronology hab)
      hpendingRoof hinstalledRoof
  refine ⟨hresultTight, ?_⟩
  rintro x ⟨p, hp, hxp⟩
  rcases hp with hpDone | hpStar
  · exact G.roof_cut (hL.frontierChronology hab)
      (hbaseRoof ⟨p, hpDone.1, hxp⟩)
  · exact hstarRoof ⟨p, hpStar, hxp⟩

/-- Existential form of the exact tracked-slice preservation theorem. -/
theorem freezeCompletedStar_roofedTight_of_tracked
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hNorm : G.IsNormalized) (hL : L.IsSplitLegal)
    {Z A U : Set V} {alpha beta : Ladder.Stage kappa}
    {base T : Set G.DPath}
    (hA : A ⊆ G.source) (hab : alpha < beta)
    (hbase : TightLinkageBetween G A (L.frontier alpha) base)
    (hbaseRoof : G.vertexSet base ⊆ G.roof (L.frontier alpha))
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      G L Z alpha beta U T)
    (hU : U ⊆ G.terminalFrontier (pendingPart G base)) :
    ∃ S : RegularCompletedPendingSplice.CleanTargetSlice G
        (G.terminalFrontier (pendingPart G base)) (L.frontier beta) U,
      ∃ hcompat : G.StarCompatible (pendingPart G base)
          (S.target ∪ S.clean),
        TightLinkageBetween G A (L.frontier beta)
            (RegularCompletedPendingSplice.freezeCompletedStar G base
              (S.target ∪ S.clean) hcompat) ∧
          G.vertexSet
            (RegularCompletedPendingSplice.freezeCompletedStar G base
              (S.target ∪ S.clean) hcompat) ⊆
            G.roof (L.frontier beta) := by
  have hleft : G.terminalFrontier (pendingPart G base) ⊆
      L.frontier alpha := by
    rintro x ⟨p, hp, hpx⟩
    exact hbase.1.terminalFrontier_subset ⟨p, hp.1, hpx⟩
  let S := cleanTargetSliceOfTracked hT hleft hU
  have hST : S.target ∪ S.clean ⊆ T :=
    cleanTargetSliceOfTracked_installed_subset hT hleft hU
  have hcompatBase : G.StarCompatible base T :=
    SliceSpliceConstructor.starCompatible_of_annular
      (hL.frontiersEssential alpha) hbaseRoof hbase.2 hT.1.1.1
  let hcompat : G.StarCompatible (pendingPart G base)
      (S.target ∪ S.clean) := fun p hp q hq ↦
    hcompatBase p hp.1 q (hST hq)
  exact ⟨S, hcompat,
    freezeCompletedStar_roofedTight_of_cleanTarget hNorm hL hA hab
      hbase hbaseRoof hT hleft hU S rfl hcompat⟩

/-- Raw source-9.15 successor geometry.  In contrast with
`InstalledComparisonGeometry`, neither the next pending tight linkage nor
its stage-prefix/maverick classification is a field: both are derived below
from the old row and the literal clean track. -/
structure Input
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
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous base)
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

  vertices_closed :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base (slice.target ∪ slice.clean) compatible) ⊆ Z
  pending_below_roof :
    G.vertexSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base (slice.target ∪ slice.clean) compatible)) ⊆
      G.roof (L.frontier stageIndex)

  old_pending_boundary :
    MeetsOnlyAtTerminal G (pendingPart G base) (L.frontier stageIndex)
  old_pending_status : ∀ p ∈ pendingPart G base,
    SliceSpliceConstructor.IsStagePrefix G L baseStage p ∨
      ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base,
        G.terminal? p = some x

  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean baseStage stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex) slice.clean) <
      kappa
  cleanMavericks_closed :
    G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt stageIndex) slice.clean) ⊆ Z

/-- Assemble the raw successor input from one actual tracked 9.15 slice and
one comparison warp containing its used restriction.  All local output
geometry (compatibility, finite character, closure, annular avoidance and
the next roof bound) is derived here.  The two comparison hypotheses are
exactly the history-sensitive global choice: the used restriction belongs
to the comparison warp, while every frozen completed component has an
unused suffix shadow in that warp. -/
def inputOfProtectedTrackedSlice
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hL : L.IsSplitLegal)
    {baseStage : Ladder.Stage kappa} {base : Set G.DPath}
    (hbaseWarp : G.IsWarp base) (hbaseFinite : G.HasFiniteCharacter base)
    (hbaseInitial : G.initialSet base = A)
    (hbaseClosed : G.vertexSet base ⊆ Z)
    (hbaseExtends : ∀ j (hji : j < i),
      G.ForwardExtension (previous j hji).row base)
    (hbaseFreezes : ∀ j (hji : j < i),
      completedPart G (previous j hji).row ⊆ completedPart G base)
    (hbasePendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G base)) (L.frontier baseStage)
        (pendingPart G base))
    (hbasePendingRoof : G.vertexSet (pendingPart G base) ⊆
      G.roof (L.frontier baseStage))
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z)
    (holdStatus : ∀ p ∈ pendingPart G base,
      SliceSpliceConstructor.IsStagePrefix G L baseStage p ∨
        ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
            G L Sigma Z A request i previous base,
          G.terminal? p = some x)
    {beta : Ladder.Stage kappa} (hbeta : beta ∈ Sigma)
    (hbaseBeta : baseStage < beta)
    (hindex : ∀ j (hji : j < i), (previous j hji).stageIndex < beta)
    {T comparison : Set G.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice G L Z
      baseStage beta
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous base) T)
    (hcomparison : G.IsWarp comparison)
    (hused : initialRestriction G T
        (G.terminalFrontier (pendingPart G base)) ⊆ comparison)
    (hshadow : ∀ f ∈ completedPart G base,
      ∃ t ∈ comparison,
        t ∉ initialRestriction G T
          (G.terminalFrontier (pendingPart G base)) ∧
        f.support \ G.strictRoof (L.frontier baseStage) ⊆ t.support) :
    Input G L Sigma Z A request i previous := by
  let U := RegularGlobalAdmissibleProvider.requiredPendingTerminals
    G L Sigma Z A request i previous base
  let left := G.terminalFrontier (pendingPart G base)
  have hleft : left ⊆ L.frontier baseStage :=
    hbasePendingTight.1.terminalFrontier_subset
  have hUleft : U ⊆ left :=
    RegularGlobalAdmissibleProvider.requiredPendingTerminals_subset_terminalFrontier
  let S := cleanTargetSliceOfTracked hT hleft hUleft
  have hST : S.target ∪ S.clean ⊆ T :=
    cleanTargetSliceOfTracked_installed_subset hT hleft hUleft
  have hSeq : S.target ∪ S.clean = initialRestriction G T left :=
    cleanTargetSliceOfTracked_union_eq hT hleft hUleft
  have hcompatFull : G.StarCompatible (pendingPart G base) T :=
    SliceSpliceConstructor.starCompatible_of_annular
      (hL.frontiersEssential baseStage) hbasePendingRoof
        hbasePendingTight.2 hT.1.1.1
  have hcompat : G.StarCompatible (pendingPart G base)
      (S.target ∪ S.clean) := by
    intro p hp q hq
    exact hcompatFull p hp q (hST hq)
  have hweak : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood G L)
      (ControlledSlices.sliceMavericks G L.limitWarp)
      (fun p : G.DPath ↦ p.support) Z baseStage beta U T :=
    ⟨hT.1.1.1.1, hT.1.2⟩
  have hleftZ : left ⊆ Z := by
    rintro x ⟨p, hp, hpx⟩
    exact hbaseClosed ⟨p, hp.1, G.terminal_mem_support hpx⟩
  have hinstalledClosed : G.vertexSet (S.target ∪ S.clean) ⊆ Z := by
    rw [hSeq]
    exact vertexSet_initialRestriction_subset_of_controlledSlice
      (L := L) (U := U) (alpha := baseStage) (beta := beta)
        (T := T) (A := left) (Gamma := G) hclosed hleftZ hweak
  have hstarClosed : G.vertexSet (G.star hcompat) ⊆ Z := by
    intro x hx
    rcases vertexSet_star_subset_union hcompat hx with hxOld | hxNew
    · obtain ⟨p, hp, hxp⟩ := hxOld
      exact hbaseClosed ⟨p, hp.1, hxp⟩
    · exact hinstalledClosed hxNew
  have hresultClosed : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (S.target ∪ S.clean) hcompat) ⊆ Z := by
    rintro x ⟨p, hp, hxp⟩
    rcases hp with hpDone | hpStar
    · exact hbaseClosed ⟨p, hpDone.1, hxp⟩
    · exact hstarClosed ⟨p, hpStar, hxp⟩
  have hinstalledRoof : G.vertexSet (S.target ∪ S.clean) ⊆
      G.roof (L.frontier beta) := by
    rintro x ⟨p, hp, hxp⟩
    exact (hT.1.1.1.2 ⟨p, hST hp, hxp⟩).2
  have hstarRoof : G.vertexSet (G.star hcompat) ⊆
      G.roof (L.frontier beta) :=
    vertexSet_star_subset_roof hcompat (hL.frontierChronology hbaseBeta)
      hbasePendingRoof hinstalledRoof
  have hpendingFinite : G.HasFiniteCharacter (pendingPart G base) := by
    intro p hp
    exact hbaseFinite hp.1
  refine
    { baseStage := baseStage
      base := base
      base_warp := hbaseWarp
      base_finite := hbaseFinite
      base_initial := hbaseInitial
      base_extends := hbaseExtends
      base_freezes := hbaseFreezes
      stageIndex := beta
      stageIndex_mem := hbeta
      index_strict := hindex
      comparison := comparison
      comparison_warp := hcomparison
      slice := S
      installed_subset := ?_
      installed_avoids_old_strictRoof := ?_
      completed_shadow := ?_
      compatible := hcompat
      installed_star_finite := hasFiniteCharacter_star
        hpendingFinite S.finiteCharacter hcompat
      vertices_closed := hresultClosed
      pending_below_roof := ?_
      old_pending_boundary := ?_
      old_pending_status := holdStatus
      cleanIntervals := cleanTargetSliceOfTracked_cleanIntervals
        hT hleft hUleft
      cleanMavericks_small :=
        cleanTargetSliceOfTracked_cleanMavericks_small hT hleft hUleft
      cleanMavericks_closed :=
        cleanTargetSliceOfTracked_cleanMavericks_closed hT hleft hUleft }
  · rw [hSeq]
    exact hused
  · rintro x ⟨p, hp, hxp⟩
    exact (hT.1.1.1.2 ⟨p, hST hp, hxp⟩).1
  · intro f hf
    obtain ⟨t, ht, htNot, hft⟩ := hshadow f hf
    exact ⟨t, ht, hSeq.symm ▸ htNot, hft⟩
  · rintro x ⟨p, hp, hxp⟩
    exact hstarRoof ⟨p,
      RegularCompletedPendingSplice.pendingPart_freezeCompletedStar_subset_star
        G base (S.target ∪ S.clean) hcompat hp, hxp⟩
  · exact meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      (hL.frontiersEssential baseStage) hbasePendingRoof
        hbasePendingTight.2 (hL.strictFrontierChronology hbaseBeta)

namespace Input

/-- The full comparison warp discharges the only cross-disjointness
obligation in the concrete clean step. -/
theorem cleanStep
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : Input G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.IsCleanTargetStep G S.base
      (S.slice.target ∪ S.slice.clean) S.compatible := by
  exact RegularEventualCompatibility.cleanTargetStep_of_used_suffixShadow
    G S.base_warp S.comparison_warp S.installed_subset
      S.installed_avoids_old_strictRoof S.completed_shadow S.compatible

/-- The clean-track maverick terminals lie on the new ladder frontier and
in the registered closing-up set. -/
theorem maverickTerminals_subset
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : Input G L Sigma Z A request i previous) :
    G.terminalFrontier
        (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
          S.slice.clean) ⊆
      L.frontier S.stageIndex ∩ Z := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨S.slice.clean_terminal ⟨p, hp.1, hpx⟩,
    S.cleanMavericks_closed ⟨p, hp, G.terminal_mem_support hpx⟩⟩

/-- The raw, non-circular datum canonically produces the exact stage record
consumed by the provenance recursion. -/
def canonicalStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : Input G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) (hL : L.IsSplitLegal) (hA : A ⊆ G.source)
    (hresultTight : TightLinkageBetween G A (L.frontier S.stageIndex)
      (RegularCompletedPendingSplice.freezeCompletedStar G S.base
        (S.slice.target ∪ S.slice.clean) S.compatible))
    (hresultRoof : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G S.base
        (S.slice.target ∪ S.slice.clean) S.compatible) ⊆
      G.roof (L.frontier S.stageIndex)) :
    RegularCanonicalAdmissibleProvider.CanonicalStage
      G L Sigma Z A request i previous where
  baseStage := S.baseStage
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
  installed_avoids_old_strictRoof := S.installed_avoids_old_strictRoof
  completed_shadow := S.completed_shadow
  compatible := S.compatible
  installed_star_finite := S.installed_star_finite
  vertices_closed := S.vertices_closed
  pending_tight := by
    apply S.slice.pendingPart_freezeCompletedStar_tightLinkageBetween
      hNorm
    · rw [S.base_initial]
      exact hA
    · exact S.base_finite
    · exact S.old_pending_boundary
    · exact S.cleanStep
    · exact S.installed_star_finite
  pending_below_roof := S.pending_below_roof
  pendingRequest := G.terminalFrontier
    (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
      S.slice.clean)
  pendingRequest_subset := S.maverickTerminals_subset
  pendingRequest_small :=
    (SliceSpliceConstructor.mk_terminalFrontier_le G
      (ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex)
        S.slice.clean)).trans_lt S.cleanMavericks_small
  pending_status := by
    exact S.slice.pendingPart_freezeCompletedStar_status hNorm hL
      S.cleanIntervals S.compatible S.old_pending_status
  slice := S.slice
  installed_eq := rfl
  cleanMavericks :=
    ControlledSlices.sliceMavericks G (L.warpAt S.stageIndex) S.slice.clean
  cleanMavericks_eq := rfl
  cleanIntervals := S.cleanIntervals
  cleanMavericks_small := S.cleanMavericks_small
  cleanMavericks_closed := S.cleanMavericks_closed
  pendingRequest_eq := rfl
  result_tight := hresultTight
  result_below_roof := hresultRoof

theorem nonempty_canonicalStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : Input G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) (hL : L.IsSplitLegal) (hA : A ⊆ G.source)
    (hresultTight : TightLinkageBetween G A (L.frontier S.stageIndex)
      (RegularCompletedPendingSplice.freezeCompletedStar G S.base
        (S.slice.target ∪ S.slice.clean) S.compatible))
    (hresultRoof : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G S.base
        (S.slice.target ∪ S.slice.clean) S.compatible) ⊆
      G.roof (L.frontier S.stageIndex)) :
    Nonempty (RegularCanonicalAdmissibleProvider.CanonicalStage
      G L Sigma Z A request i previous) :=
  ⟨S.canonicalStage hNorm hL hA hresultTight hresultRoof⟩

end Input

end RegularCanonicalSuccessor
end CardinalInduction
end Erdos599
