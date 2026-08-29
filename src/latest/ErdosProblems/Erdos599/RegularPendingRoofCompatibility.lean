/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCompletedPendingSplice
import ErdosProblems.Erdos599.SliceSplice

/-!
# Compatibility using only the pending-roof invariant

Completed target paths can leave the roof of the current ladder frontier.
Consequently the regular recursion may retain roof containment only for its
pending subfamily.  This file records the two geometric facts which use
exactly that sound invariant.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularPendingRoofCompatibility

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A pending row below `roof C` is star-compatible with a new family which
avoids `strictRoof C` and meets `C` only at its initial vertices.  No claim
about the carrier of an already completed component is used. -/
theorem starCompatible_of_pendingRoof
    (G : DWeb V) {pending used : Set G.DPath} {C : Set V}
    (hessential : G.essential C = C)
    (hpendingRoof : G.vertexSet pending ⊆ G.roof C)
    (hpendingBoundary : MeetsOnlyAtTerminal G pending C)
    (husedAvoid : G.vertexSet used ⊆ (G.strictRoof C)ᶜ)
    (husedSource : ∀ q ∈ used, q.support ∩ C = {q.initial}) :
    G.StarCompatible pending used := by
  intro p hp q hq x hxp hxq
  have hxRoof : x ∈ G.roof C :=
    hpendingRoof ⟨p, hp, hxp⟩
  have hxNotStrict : x ∉ G.strictRoof C :=
    husedAvoid ⟨q, hq, hxq⟩
  have hxEssential : x ∈ G.essential C := by
    by_contra hxNotEssential
    exact hxNotStrict ⟨hxRoof, hxNotEssential⟩
  have hxC : x ∈ C := hessential ▸ hxEssential
  refine ⟨hpendingBoundary p hp x hxp hxC, ?_⟩
  have hx : x ∈ q.support ∩ C := ⟨hxq, hxC⟩
  rw [husedSource q hq] at hx
  exact (Set.mem_singleton_iff.mp hx).symm

/-- In particular a clean-target slice is compatible with the pending row
as soon as its installed carrier avoids the old strict roof. -/
theorem starCompatible_cleanTargetSlice_of_pendingRoof
    (G : DWeb V) {pending : Set G.DPath} {C right selected : Set V}
    (hessential : G.essential C = C)
    (hpendingRoof : G.vertexSet pending ⊆ G.roof C)
    (hpendingBoundary : MeetsOnlyAtTerminal G pending C)
    (S : RegularCompletedPendingSplice.CleanTargetSlice
      G C right selected)
    (husedAvoid : G.vertexSet (S.target ∪ S.clean) ⊆
      (G.strictRoof C)ᶜ) :
    G.StarCompatible pending (S.target ∪ S.clean) := by
  exact starCompatible_of_pendingRoof G hessential hpendingRoof
    hpendingBoundary husedAvoid S.source_pure

/-- A completed target ear which meets its left boundary only at its
initial vertex avoids the strict roof of that boundary.  Its initial vertex
is essential; every later support vertex has the suffix of the same target
path as a witness that it is outside the ordinary roof. -/
theorem target_vertexSet_subset_compl_strictRoof
    (G : DWeb V) (hNorm : G.IsNormalized)
    {left right U : Set V}
    (hessential : G.essential left = left)
    (S : RegularCompletedPendingSplice.CleanTargetSlice
      G left right U) :
    G.vertexSet S.target ⊆ (G.strictRoof left)ᶜ := by
  rintro x ⟨p, hpTarget, hxp⟩ hxStrict
  obtain ⟨f, rfl⟩ := S.finiteCharacter (Or.inl hpTarget)
  have hfCompleted : (Sum.inl f : G.DPath) ∈
      completedPart G S.target :=
    S.target_subset_completedPart hNorm hpTarget
  obtain ⟨b, hbTarget, hfTerminal⟩ := hfCompleted.2
  have hfinishTarget : f.finish ∈ G.target := by
    have hfinish : f.finish = b := Option.some.inj hfTerminal
    exact hfinish.symm ▸ hbTarget
  have hfTargetPath : G.IsTargetPathFrom f.start f :=
    ⟨rfl, hfinishTarget⟩
  have hstartU : f.start ∈ U := by
    rw [← S.target_initial]
    exact ⟨Sum.inl f, hpTarget, rfl⟩
  have hstartLeft : f.start ∈ left := S.initial_cover hstartU
  by_cases hxStart : x = f.start
  · apply hxStrict.2
    rw [hessential]
    exact hxStart ▸ hstartLeft
  · have hAvoid : RelationalRoof.Avoids G.graph.Adj f
        (left \ {f.start}) := by
      intro y hyf hyLeft
      have hyInter : y ∈ f.support ∩ left := ⟨hyf, hyLeft.1⟩
      have hpPure := S.source_pure (Sum.inl f) (Or.inl hpTarget)
      change f.support ∩ left = {f.start} at hpPure
      rw [hpPure] at hyInter
      exact hyLeft.2 (Set.mem_singleton_iff.1 hyInter)
    exact (RelationalRoof.not_mem_roof_of_later_mem_targetPath
      G.graph.Adj G.target f hfTargetPath hAvoid hxp hxStart) hxStrict.1

/-- Roof containment propagates to the *new pending part* without any roof
hypothesis on frozen completed components. -/
theorem pendingPart_freezeCompletedStar_vertexSet_subset_roof
    (G : DWeb V) {old used : Set G.DPath} {C R : Set V}
    (hcompat : G.StarCompatible (pendingPart G old) used)
    (hchron : C ⊆ G.roof R)
    (hpendingRoof : G.vertexSet (pendingPart G old) ⊆ G.roof C)
    (husedRoof : G.vertexSet used ⊆ G.roof R) :
    G.vertexSet
        (pendingPart G
          (RegularCompletedPendingSplice.freezeCompletedStar
            G old used hcompat)) ⊆
      G.roof R := by
  intro x hx
  have hxStar : x ∈ G.vertexSet (G.star hcompat) := by
    obtain ⟨p, hp, hxp⟩ := hx
    exact ⟨p,
      RegularCompletedPendingSplice.pendingPart_freezeCompletedStar_subset_star
        G old used hcompat hp,
      hxp⟩
  exact vertexSet_star_subset_roof hcompat hchron hpendingRoof
    husedRoof hxStar

/-- The sharper propagation statement used when completed target ears are
not themselves below the new roof.  A path which remains pending cannot
have selected a target-track continuation, so its support is contained in
the old pending component together with one clean component. -/
theorem pendingPart_freezeCompletedStar_vertexSet_subset_roof_clean
    (G : DWeb V) (hNorm : G.IsNormalized)
    {old : Set G.DPath} {C R U : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice G
      (G.terminalFrontier (pendingPart G old)) R U)
    (hOldFinite : G.HasFiniteCharacter (pendingPart G old))
    (hcompat : G.StarCompatible (pendingPart G old)
      (S.target ∪ S.clean))
    (hchron : C ⊆ G.roof R)
    (hpendingRoof : G.vertexSet (pendingPart G old) ⊆ G.roof C)
    (hcleanRoof : G.vertexSet S.clean ⊆ G.roof R) :
    G.vertexSet
        (pendingPart G
          (RegularCompletedPendingSplice.freezeCompletedStar
            G old (S.target ∪ S.clean) hcompat)) ⊆
      G.roof R := by
  rintro x ⟨r, hrPending, hxr⟩
  have hrStar : r ∈ G.star hcompat :=
    RegularCompletedPendingSplice.pendingPart_freezeCompletedStar_subset_star
      G old (S.target ∪ S.clean) hcompat hrPending
  obtain ⟨oldPath, rfl⟩ := hrStar
  rcases oldPath with ⟨p, hpPending⟩
  obtain ⟨f, rfl⟩ := hOldFinite hpPending
  have hfinishLeft : f.finish ∈
      G.terminalFrontier (pendingPart G old) :=
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
  have hinter : f.support ∩ chosen.support ⊆ {f.finish} := by
    intro y hy
    have hy' := hcompat (.inl f) hpPending chosen hchosenUnion
      y hy.1 hy.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
  simp only [DWeb.starPath] at hxr
  rw [dif_pos hmatch] at hxr
  rw [DirectedPath.Path.support_appendFinite f chosen
    hchosenInitial hinter] at hxr
  rcases hxr with hxf | hxChosen
  · exact G.roof_cut hchron
      (hpendingRoof ⟨Sum.inl f, hpPending, hxf⟩)
  · exact hcleanRoof ⟨chosen, hchosenClean, hxChosen⟩

end RegularPendingRoofCompatibility
end CardinalInduction
end Erdos599
