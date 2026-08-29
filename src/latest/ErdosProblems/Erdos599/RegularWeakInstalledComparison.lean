/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakSplitCandidate

/-!
# Assembling a weak comparison from its installed tracks

The persistent target track is not right-tight, so it cannot be folded into
the clean-track linkage by a tight-linkage constructor.  Nevertheless the
union stored by `CleanTargetSlice` is already a warp.  Once the target track
is known to have the ambient left/right endpoint purity, the same union is a
full weak linkage.  Its two target-link certificates combine because that
linkage is source-pure on the whole left boundary.

This is the local assembly used by the weak source-9.15 candidate table.  It
does not assert that independently chosen target and clean families are
disjoint.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakInstalledComparison

universe u

variable {V : Type u}

open RegularCompletedPendingSplice

/-- The installed union of a clean target slice is a linkage as soon as the
target track has the missing endpoint-purity information.  The clean-track
endpoint statement follows from `source_pure` and its right-terminal
condition. -/
theorem CleanTargetSlice.union_isLinkageBetween
    {G : DWeb V} {left right selected : Set V}
    (S : CleanTargetSlice G left right selected)
    (htargetTerminal : G.terminalFrontier S.target ⊆ right)
    (htargetPure : ∀ p ∈ S.target, IsPathBetween G left right p) :
    IsLinkageBetween G left right (S.target ∪ S.clean) := by
  refine ⟨S.union_warp, S.finiteCharacter, S.initialSet_union, ?_, ?_⟩
  · rw [G.terminalFrontier_union]
    exact Set.union_subset htargetTerminal S.clean_terminal
  · intro p hp
    rcases hp with hpTarget | hpClean
    · exact htargetPure p hpTarget
    · obtain ⟨f, rfl⟩ := S.finiteCharacter (Or.inr hpClean)
      have hsource : f.support ∩ left = {f.start} :=
        S.source_pure (Sum.inl f) (Or.inr hpClean)
      have hstartLeft : f.start ∈ left := by
        have hinitial : f.start ∈ G.initialSet S.clean :=
          ⟨Sum.inl f, hpClean, rfl⟩
        rw [S.clean_initial] at hinitial
        exact hinitial.1
      have hfinishRight : f.finish ∈ right := by
        apply S.clean_terminal
        exact ⟨Sum.inl f, hpClean, rfl⟩
      refine ⟨f, rfl, ?_, hsource⟩
      apply Set.Subset.antisymm
      · rintro x ⟨hxf, hxLeft | hxRight⟩
        · have hx : x ∈ ({f.start} : Set V) := by
            rw [← hsource]
            exact ⟨hxf, hxLeft⟩
          exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx))
        · have hterminal := S.clean_terminal_only
            (Sum.inl f) hpClean x hxf hxRight
          have hx : x = f.finish := (Option.some.inj hterminal).symm
          exact Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton_iff.mpr hx))
      · rintro x (hxStart | hxFinish)
        · subst x
          exact ⟨f.start_mem_support, Or.inl hstartLeft⟩
        · have hx : x = f.finish := Set.mem_singleton_iff.mp hxFinish
          subst x
          exact ⟨f.finish_mem_support, Or.inr hfinishRight⟩

/-- Two target-link certificates on a common source-pure linkage combine.
No ambient-source normalization is needed: purity relative to `left` is
already part of `IsLinkageBetween`. -/
theorem linksToTarget_union_of_linkage
    {G : DWeb V} {left right A B : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G left right W)
    (hA : A ⊆ left) (hB : B ⊆ left)
    (hlinksA : LinksToTarget G W A)
    (hlinksB : LinksToTarget G W B) :
    LinksToTarget G W (A ∪ B) := by
  intro a ha
  have upgrade {C : Set V} (hC : C ⊆ left)
      (haC : a ∈ C) (haUnion : a ∈ A ∪ B)
      (hlinks : LinksToTarget G W C) :
      ∃ p ∈ W, ∃ q : DirectedPath.FinitePath G.graph,
        p = Sum.inl q ∧ q.support ∩ (A ∪ B) = {a} ∧
          FinitePathSuffixMeets q a G.target := by
    obtain ⟨p, hpW, q, hpq, hpure, hsuffix⟩ := hlinks a haC
    have haSupport : a ∈ q.support := by
      have : a ∈ q.support ∩ C := by
        rw [hpure]
        exact Set.mem_singleton a
      exact this.1
    obtain ⟨f, hpf, _hends, hsource⟩ := hW.endpointPure p hpW
    have hfq : f = q := by
      apply Sum.inl.inj
      exact hpf.symm.trans hpq
    subst f
    have haStart : a = q.start := by
      have : a ∈ ({q.start} : Set V) := by
        rw [← hsource]
        exact ⟨haSupport, hC haC⟩
      exact Set.mem_singleton_iff.mp this
    refine ⟨p, hpW, q, hpq, ?_, hsuffix⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxUnion⟩
      have hxStart : x ∈ ({q.start} : Set V) := by
        rw [← hsource]
        exact ⟨hxq, hxUnion.elim (fun hx ↦ hA hx) (fun hx ↦ hB hx)⟩
      exact Set.mem_singleton_iff.mpr
        ((Set.mem_singleton_iff.mp hxStart).trans haStart.symm)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨haSupport, haUnion⟩
  rcases ha with haA | haB
  · exact upgrade hA haA (Or.inl haA) hlinksA
  · exact upgrade hB haB (Or.inr haB) hlinksB

/-- Package an arbitrary selected target track and its complementary clean
track as a weak split candidate.  Every persistent coordinate must be
selected, but further stop-over obstructions may be selected as well. -/
theorem isWeakSplitAnnularCandidate_of_selectedInstalledUnion
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa} {selected : Set V}
    (hpersistent : RegularWeakSplitCandidate.stagePersistent G
      (L.frontier beta) (request delta gamma) ⊆ selected)
    (S : CleanTargetSlice G (L.frontier delta) (L.frontier beta) selected)
    (hrequest : request delta gamma ⊆ L.frontier delta)
    (htargetTerminal : G.terminalFrontier S.target ⊆ L.frontier beta)
    (htargetPure : ∀ p ∈ S.target,
      IsPathBetween G (L.frontier delta) (L.frontier beta) p)
    (hcleanLinks : LinksToTarget G S.clean
      (request delta gamma \ selected))
    (htargetSmall : #S.target < kappa)
    (hregion : G.vertexSet (S.target ∪ S.clean) ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (hintervals : SliceCandidate.HasStageIntervalSegments G L S.clean
      delta beta)
    (hmavericks : #(ControlledSlices.sliceMavericks G (L.warpAt beta)
      S.clean) < kappa) :
    RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
      G L request delta beta gamma
        ⟨S.target, S.clean, S.target ∪ S.clean⟩ := by
  have hselectedLeft : selected ⊆ L.frontier delta :=
    S.initial_cover
  have hremainingLeft : request delta gamma \ selected ⊆
      L.frontier delta :=
    Set.sdiff_subset.trans hrequest
  have hlinkage : IsLinkageBetween G (L.frontier delta)
      (L.frontier beta) (S.target ∪ S.clean) :=
    CleanTargetSlice.union_isLinkageBetween S htargetTerminal htargetPure
  have htargetLinks : LinksToTarget G (S.target ∪ S.clean)
      selected :=
    SliceSegmentCore.linksToTarget_mono_family S.target_subset
      S.target_links
  have hcleanLinks' : LinksToTarget G (S.target ∪ S.clean)
      (request delta gamma \ selected) :=
    SliceSegmentCore.linksToTarget_mono_family S.clean_subset hcleanLinks
  have hallLinks : LinksToTarget G (S.target ∪ S.clean)
      (request delta gamma) := by
    have hparts : request delta gamma ⊆
        selected ∪ (request delta gamma \ selected) := by
      intro x hx
      by_cases hxSelected : x ∈ selected
      · exact Or.inl hxSelected
      · exact Or.inr ⟨hx, hxSelected⟩
    exact ControlledSlices.linksToTarget_mono G
      (S.target ∪ S.clean) hparts
        (linksToTarget_union_of_linkage hlinkage hselectedLeft
          hremainingLeft htargetLinks hcleanLinks')
  exact ⟨selected, hpersistent, S, rfl, rfl,
    ⟨⟨hlinkage, hcleanLinks'⟩, hregion⟩,
    Set.subset_union_right,
    (by
      rintro x ⟨p, hp, hxp⟩
      exact (hregion ⟨p, Or.inl hp, hxp⟩).2),
    htargetSmall, hcleanLinks, hintervals, hmavericks⟩

/-- Persistent-only specialization of the general selected installed-union
constructor. -/
theorem isWeakSplitAnnularCandidate_of_installedUnion
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (S : CleanTargetSlice G (L.frontier delta) (L.frontier beta)
      (RegularWeakSplitCandidate.stagePersistent G (L.frontier beta)
        (request delta gamma)))
    (hrequest : request delta gamma ⊆ L.frontier delta)
    (htargetTerminal : G.terminalFrontier S.target ⊆ L.frontier beta)
    (htargetPure : ∀ p ∈ S.target,
      IsPathBetween G (L.frontier delta) (L.frontier beta) p)
    (hcleanLinks : LinksToTarget G S.clean
      (RegularWeakSplitCandidate.stageMovable G (L.frontier beta)
        (request delta gamma)))
    (htargetSmall : #S.target < kappa)
    (hregion : G.vertexSet (S.target ∪ S.clean) ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (hintervals : SliceCandidate.HasStageIntervalSegments G L S.clean
      delta beta)
    (hmavericks : #(ControlledSlices.sliceMavericks G (L.warpAt beta)
      S.clean) < kappa) :
    RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
      G L request delta beta gamma
        ⟨S.target, S.clean, S.target ∪ S.clean⟩ := by
  apply isWeakSplitAnnularCandidate_of_selectedInstalledUnion
    (selected := RegularWeakSplitCandidate.stagePersistent G
      (L.frontier beta) (request delta gamma))
    Set.Subset.rfl
      S hrequest htargetTerminal htargetPure
  · simpa only [RegularWeakSplitCandidate.stageMovable] using hcleanLinks
  · exact htargetSmall
  · exact hregion
  · exact hintervals
  · exact hmavericks

end RegularWeakInstalledComparison
end CardinalInduction
end Erdos599
