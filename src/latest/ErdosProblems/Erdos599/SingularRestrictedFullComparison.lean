/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularTargetLinkTransfer

/-!
# Comparing restricted and unrestricted singular continuations

The future-safe re-entry row restricts quotient components to starts outside
the new stop-over.  The target row uses the full quotient linkage.  This
module proves that the safe row is componentwise a forward prefix of the
target row.  Consequently the two rows can be combined by
`completedPendingMerge`.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularRestrictedFullComparison

open SingularContinuation SingularQuotientReentry

universe u

variable {V : Type u}

/-- Enlarging the right-hand warp does not change a source-star component
when the smaller warp already contains a matching component. -/
private theorem starPath_eq_of_subset_of_match
    {G : DWeb V} {W₁ W₂ L R : Set G.DPath}
    (hRwarp : G.IsWarp R) (hLR : L ⊆ R)
    (hLcompat : G.StarCompatible W₁ L)
    (hRcompat : G.StarCompatible W₂ R)
    (f : DirectedPath.FinitePath G.graph)
    (hfW₁ : (Sum.inl f : G.DPath) ∈ W₁)
    (hfW₂ : (Sum.inl f : G.DPath) ∈ W₂)
    (hmatch : ∃ q ∈ L, q.initial = f.finish) :
    G.starPath hLcompat ⟨.inl f, hfW₁⟩ =
      G.starPath hRcompat ⟨.inl f, hfW₂⟩ := by
  simp only [DWeb.starPath]
  rw [dif_pos hmatch]
  have hmatchR : ∃ q ∈ R, q.initial = f.finish := by
    obtain ⟨q, hqL, hqInitial⟩ := hmatch
    exact ⟨q, hLR hqL, hqInitial⟩
  rw [dif_pos hmatchR]
  let qL : G.DPath := Classical.choose hmatch
  let qR : G.DPath := Classical.choose hmatchR
  have hqL_mem : qL ∈ R := hLR (Classical.choose_spec hmatch).1
  have hqR_mem : qR ∈ R := (Classical.choose_spec hmatchR).1
  have hqL_initial : qL.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hqR_initial : qR.initial = f.finish :=
    (Classical.choose_spec hmatchR).2
  have hqeq : qL = qR := by
    by_contra hne
    exact Set.disjoint_left.1 (hRwarp hqL_mem hqR_mem hne)
      (hqL_initial.symm ▸ qL.initial_mem_support)
      (hqR_initial.symm ▸ qR.initial_mem_support)
  congr 1

/-- The restricted clean continuation is a forward prefix of the
unrestricted continuation using the same quotient linkage. -/
theorem forwardExtension_frozenRestrictedContinuation_continuation
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    G.ForwardExtension
      (frozenRestrictedContinuation G hD hclean hE)
      (continuation G hD.linkage hD.separator hD.stopover.minimal
        hclean U hE.linkage.initialSet_eq) := by
  let F := frozenAt G W E
  let P := pendingAt G W E
  let R := quotientPending G D E U
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    linkage_vertexSet_subset_roof G hD.linkage hD.separator hclean
  have hProof : G.vertexSet P ⊆ G.roof D := by
    rintro x ⟨p, hp, hxp⟩
    exact hWroof ⟨p, hp.1, hxp⟩
  have hPclean : TerminalCleanAt G P D :=
    fun p hp ↦ hclean p hp.1
  have hRstart : (G.quotient D).initialSet R ⊆ D := by
    rintro x ⟨q, hqR, hqx⟩
    have hxU : x ∈ (G.quotient D).initialSet U := ⟨q, hqR.1, hqx⟩
    rw [hE.linkage.initialSet_eq, hD.quotient_source_eq] at hxU
    exact hxU
  let LR := liftedQuotientFamily G D R
  let LU := liftedQuotientFamily G D U
  have hLRU : LR ⊆ LU := by
    rintro q ⟨q₀, hq₀R, rfl⟩
    exact ⟨q₀, hq₀R.1, rfl⟩
  have hLUwarp : G.IsWarp LU :=
    DWeb.IsWarp.liftQuotientFamily G hE.linkage.isWarp
  let hcR : G.StarCompatible P LR :=
    starCompatible_liftQuotientFamily_of_roof
      G hProof hD.stopover.minimal hPclean hRstart
  let hcU : G.StarCompatible W LU :=
    starCompatible_liftQuotientFamily_of_linkage
      G hD.linkage hD.separator hD.stopover.minimal
        hclean hE.linkage.initialSet_eq
  have matchingRestricted
      (f : DirectedPath.FinitePath G.graph)
      (hfW : (Sum.inl f : G.DPath) ∈ W)
      (hfNotE : f.finish ∉ E) :
      ∃ q ∈ LR, q.initial = f.finish := by
    have hfD : f.finish ∈ D :=
      hD.linkage.terminalFrontier_subset ⟨.inl f, hfW, rfl⟩
    have hfSource : f.finish ∈ (G.quotient D).source := by
      rw [hD.quotient_source_eq]
      exact hfD
    have hfInitial : f.finish ∈ (G.quotient D).initialSet U := by
      rw [hE.linkage.initialSet_eq]
      exact hfSource
    obtain ⟨q, hqU, hqInitial⟩ := hfInitial
    let qLift : G.DPath := G.liftQuotientPath D q
    refine ⟨qLift, ?_, ?_⟩
    · refine ⟨q, ⟨hqU, ?_⟩, rfl⟩
      exact hqInitial ▸ hfNotE
    · simpa only [qLift, G.initial_liftQuotientPath] using hqInitial
  constructor
  · intro p hp
    change p ∈ F ∪ G.star hcR at hp
    rcases hp with hpF | hpStar
    · let q := G.starPath hcU ⟨p, hpF.1⟩
      refine ⟨q, ⟨⟨p, hpF.1⟩, rfl⟩, ?_⟩
      exact G.extends_starPath hcU ⟨p, hpF.1⟩
    · obtain ⟨old, rfl⟩ := hpStar
      rcases old with ⟨old, holdP⟩
      obtain ⟨f, rfl⟩ := hD.linkage.finiteCharacter holdP.1
      have hfNotE : f.finish ∉ E := by
        intro hfE
        exact holdP.2 ⟨holdP.1, f.finish, hfE, rfl⟩
      have hmatch := matchingRestricted f holdP.1 hfNotE
      have heq := starPath_eq_of_subset_of_match
        hLUwarp hLRU hcR hcU f holdP holdP.1 hmatch
      refine ⟨G.starPath hcU ⟨.inl f, holdP.1⟩,
        ⟨⟨.inl f, holdP.1⟩, rfl⟩, ?_⟩
      rw [heq]
      exact G.extends_refl _
  · intro q hq
    obtain ⟨old, rfl⟩ := hq
    rcases old with ⟨old, holdW⟩
    obtain ⟨f, rfl⟩ := hD.linkage.finiteCharacter holdW
    by_cases hfE : f.finish ∈ E
    · refine ⟨.inl f, ?_, G.extends_starPath hcU ⟨.inl f, holdW⟩⟩
      change (Sum.inl f : G.DPath) ∈ F ∪ G.star hcR
      exact Or.inl ⟨holdW, f.finish, hfE, rfl⟩
    · have hfP : (Sum.inl f : G.DPath) ∈ P := by
        refine ⟨holdW, ?_⟩
        rintro ⟨_hfW, e, heE, hfterm⟩
        exact hfE (Option.some.inj hfterm ▸ heE)
      have hmatch := matchingRestricted f holdW hfE
      have heq := starPath_eq_of_subset_of_match
        hLUwarp hLRU hcR hcU f hfP holdW hmatch
      refine ⟨G.starPath hcR ⟨.inl f, hfP⟩, ?_, ?_⟩
      · change G.starPath hcR ⟨.inl f, hfP⟩ ∈ F ∪ G.star hcR
        exact Or.inr ⟨⟨.inl f, hfP⟩, rfl⟩
      · rw [heq]
        exact G.extends_refl _

/-- The unrestricted continuation has no terminal outside the new quotient
stop-over. -/
theorem terminalFrontier_continuation_subset_newStopover
    {G : DWeb V} {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    G.terminalFrontier
        (continuation G hD.linkage hD.separator hD.stopover.minimal
          hclean U hE.linkage.initialSet_eq) ⊆ E := by
  intro x hx
  apply hE.linkage.terminalFrontier_subset
  rw [← G.terminalFrontier_liftQuotientFamily D U]
  exact terminalFrontier_continuation_subset
    G hD.linkage hD.separator hD.stopover.minimal hclean
      hE.linkage.initialSet_eq hx

end SingularRestrictedFullComparison
end CardinalInduction
end Erdos599
