/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate

/-!
# Finite endpoint-colour repair by whole-component replacement

A mixed residual/designated augmentation need not preserve endpoint colours
path by path.  This file records the component operation which repairs the
designated colour.  Compare the new family with the old target linkage and
retain the old family on every alternating component containing a bad
(non-target-coloured) terminal.  On every remaining component the new
family may be retained.  Since components are closed under both path
families, every retained new terminal has the desired colour.

The first lemma removes an unnecessary normalization hypothesis from a
frequently used bridge: the two carrier-intersection equalities in
`IsCleanFiniteWarp` already imply endpoint purity.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteEndpointColorRepair

open DWeb
open SliceCandidate
open SliceSpliceSource

universe u

variable {V : Type u}

/-- Cleanliness is inherited by subfamilies of a clean warp. -/
theorem cleanFiniteWarp_mono
    {G : DWeb V} {W Y : Set G.DPath}
    (hW : G.IsCleanFiniteWarp W) (hYW : Y ⊆ W) :
    G.IsCleanFiniteWarp Y := by
  have hwarp : G.IsWarp Y := fun p hp q hq hpq ↦
    hW.1 (hYW hp) (hYW hq) hpq
  have hfinite : G.HasFiniteCharacter Y := fun {p} hp ↦
    hW.2.1 (hYW hp)
  refine ⟨hwarp, hfinite, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hxp⟩, hxSource⟩
      have hxInitialW : x ∈ G.initialSet W := by
        rw [← hW.2.2.1]
        exact ⟨⟨p, hYW hpY, hxp⟩, hxSource⟩
      obtain ⟨q, hqW, hqx⟩ := hxInitialW
      have hxpq : p = q := by
        by_contra hpq
        exact Set.disjoint_left.1
          (hW.1 (hYW hpY) hqW hpq) hxp
          (hqx ▸ q.initial_mem_support)
      subst q
      exact ⟨p, hpY, hqx⟩
    · rintro x ⟨p, hpY, hpx⟩
      exact ⟨⟨p, hpY, hpx ▸ p.initial_mem_support⟩,
        DWeb.IsCleanFiniteWarp.initialSet_subset_source G hW
          ⟨p, hYW hpY, hpx⟩⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hxp⟩, hxTarget⟩
      have hxFrontierW : x ∈ G.terminalFrontier W := by
        rw [← hW.2.2.2]
        exact ⟨⟨p, hYW hpY, hxp⟩, hxTarget⟩
      obtain ⟨q, hqW, hqx⟩ := hxFrontierW
      have hpq : p = q := by
        by_contra hpq
        exact Set.disjoint_left.1
          (hW.1 (hYW hpY) hqW hpq) hxp
          (G.terminal_mem_support hqx)
      subst q
      exact ⟨p, hpY, hqx⟩
    · rintro x ⟨p, hpY, hpx⟩
      exact ⟨⟨p, hpY, G.terminal_mem_support hpx⟩,
        DWeb.IsCleanFiniteWarp.terminalFrontier_subset_target G hW
          ⟨p, hYW hpY, hpx⟩⟩

/-- A clean finite warp is a linkage from its own initial set to the ambient
target.  No normalization of the ambient web is required: cleanliness and
warp disjointness identify the unique source and target endpoints on each
member. -/
theorem isLinkageBetween_of_cleanFiniteWarp
    {G : DWeb V} {W : Set G.DPath}
    (hW : G.IsCleanFiniteWarp W) :
    IsLinkageBetween G (G.initialSet W) G.target W := by
  refine ⟨hW.isWarp, hW.hasFiniteCharacter, rfl,
    hW.terminalFrontier_subset_target, ?_⟩
  intro p hpW
  obtain ⟨q, hpq⟩ := hW.2.1 hpW
  subst p
  have hsource : q.support ∩ G.initialSet W = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxInitial⟩
      obtain ⟨r, hrW, hrx⟩ := hxInitial
      have hxr : x ∈ r.support := hrx ▸ r.initial_mem_support
      have hrq : r = (.inl q : G.DPath) := by
        by_contra hrq
        exact Set.disjoint_left.1
          (hW.1 hrW hpW hrq) hxr hxq
      subst r
      exact Set.mem_singleton_iff.2 hrx.symm
    · rintro x hx
      have hxq : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.start_mem_support, ⟨.inl q, hpW, rfl⟩⟩
  have htarget : q.support ∩ G.target = {q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxTarget⟩
      have hxFrontier : x ∈ G.terminalFrontier W := by
        rw [← hW.2.2.2]
        exact ⟨⟨.inl q, hpW, hxq⟩, hxTarget⟩
      obtain ⟨r, hrW, hrx⟩ := hxFrontier
      have hxr : x ∈ r.support := G.terminal_mem_support hrx
      have hrq : r = (.inl q : G.DPath) := by
        by_contra hrq
        exact Set.disjoint_left.1
          (hW.1 hrW hpW hrq) hxr hxq
      subst r
      exact Set.mem_singleton_iff.2 (Option.some.inj hrx).symm
    · rintro x hx
      have hxq : x = q.finish := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨q.finish_mem_support, ?_⟩
      apply DWeb.IsCleanFiniteWarp.terminalFrontier_subset_target G hW
      exact ⟨(Sum.inl q : G.DPath), hpW, rfl⟩
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- Terminals of the new family outside the desired target colour. -/
def badTerminalColour (G : DWeb V) (Y : Set G.DPath)
    (B : Set V) : Set V :=
  G.terminalFrontier Y \ B

/-- Whole alternating components rooted at bad terminals are replaced by
the old target linkage.  The result has the old initial set and every
terminal has the desired old colour, even though the new linkage was only
known to end in a larger target set. -/
theorem componentMixedFamily_repairs_terminalColour
    (G : DWeb V) {W Y : Set G.DPath} {A B C : Set V}
    (hW : IsLinkageBetween G A B W)
    (hY : IsLinkageBetween G A C Y) (hBC : B ⊆ C) :
    IsLinkageBetween G A B
      (componentMixedFamily G W Y (badTerminalColour G Y B)) := by
  let E := badTerminalColour G Y B
  let D := exceptionalComponentVertices G W Y E
  let WL := initialPart G W D
  let YR := initialPart G Y Dᶜ
  have hED : E ⊆ D := by
    intro x hx
    exact mem_exceptionalComponentVertices_of_mem hx
  have hWLsupport : ∀ p ∈ WL, p.support ⊆ D := by
    intro p hp
    exact path_support_subset_exceptionalComponents_left
      hW.finiteCharacter hp.1 p.initial_mem_support hp.2
  have hYRsupport : ∀ p ∈ YR, Disjoint p.support D := by
    intro p hp
    rw [Set.disjoint_left]
    intro x hxp hxD
    exact hp.2 (path_support_subset_exceptionalComponents_right
      hY.finiteCharacter hp.1 hxp hxD p.initial_mem_support)
  have hYRterminal : G.terminalFrontier YR ⊆ B := by
    rintro x ⟨p, hpYR, hpx⟩
    by_contra hxB
    have hxE : x ∈ E := ⟨⟨p, hpYR.1, hpx⟩, hxB⟩
    exact Set.disjoint_left.1 (hYRsupport p hpYR)
      (G.terminal_mem_support hpx) (hED hxE)
  change IsLinkageBetween G A B (WL ∪ YR)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpWL | hpYR
    · rcases hq with hqWL | hqYR
      · exact hW.isWarp hpWL.1 hqWL.1 hpq
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hYRsupport q hqYR) hxq
          (hWLsupport p hpWL hxp)
    · rcases hq with hqWL | hqYR
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hYRsupport p hpYR) hxp
          (hWLsupport q hqWL hxq)
      · exact hY.isWarp hpYR.1 hqYR.1 hpq
  · intro p hp
    exact hp.elim
      (fun hpWL ↦ hW.finiteCharacter hpWL.1)
      (fun hpYR ↦ hY.finiteCharacter hpYR.1)
  · rw [G.initialSet_union, initialSet_initialPart,
      initialSet_initialPart, hW.initialSet_eq, hY.initialSet_eq]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  · rw [G.terminalFrontier_union]
    exact Set.union_subset
      (fun _ hx ↦ hW.terminalFrontier_subset
        ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩)
      hYRterminal
  · intro p hp
    rcases hp with hpWL | hpYR
    · exact hW.endpointPure p hpWL.1
    · obtain ⟨q, rfl, hends, hsource⟩ :=
        hY.endpointPure p hpYR.1
      have hfinishB : q.finish ∈ B := by
        apply hYRterminal
        exact ⟨.inl q, hpYR, rfl⟩
      refine ⟨q, rfl, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxB⟩
          · have hxOld : x ∈ q.support ∩ (A ∪ C) :=
              ⟨hxq, Or.inl hxA⟩
            exact hends ▸ hxOld
          · by_cases hxStart : x = q.start
            · exact Or.inl hxStart
            · have hxFinish : x = q.finish := by
                have hxOld : x ∈ q.support ∩ (A ∪ C) :=
                  ⟨hxq, Or.inr (hBC hxB)⟩
                rcases hends ▸ hxOld with hx | hx
                · exact False.elim (hxStart hx)
                · exact hx
              exact Or.inr hxFinish
        · rintro x (hxStart | hxFinish)
          · subst x
            refine ⟨q.start_mem_support, Or.inl ?_⟩
            rw [← hY.initialSet_eq]
            exact ⟨.inl q, hpYR.1, rfl⟩
          · subst x
            exact ⟨q.finish_mem_support, Or.inr hfinishB⟩
      · exact hsource

/-! ## Applying the repair to a retargeted augmentation -/

/-- In a normalized underlying web, a one-point augmentation remains clean
after retargeting at the original target together with a protected old
frontier.  The retargeted web itself need not be normalized.  An internal
protected-frontier vertex is already a terminal of the augmented warp, so
warp disjointness forces it to be the terminal of the member containing it.
-/
theorem onePointAugmentation_clean_of_protectedFrontier
    {G : DWeb V} (hNorm : G.IsNormalized) {S : Set V}
    {J Jplus : Set (G.retarget (G.target ∪ S)).DPath}
    (hJ : (G.retarget (G.target ∪ S)).IsCleanFiniteWarp J)
    (hS : S ⊆ (G.retarget (G.target ∪ S)).terminalFrontier J)
    (hplus : (G.retarget (G.target ∪ S)).IsOnePointAugmentation
      J Jplus) :
    (G.retarget (G.target ∪ S)).IsCleanFiniteWarp Jplus := by
  let K := G.retarget (G.target ∪ S)
  obtain ⟨a, ha, b, hb, hwarp, hfinite, hinit, hterminal⟩ := hplus
  have hinitSub : K.initialSet Jplus ⊆ K.source := by
    rw [hinit]
    exact Set.insert_subset ha.1 hJ.initialSet_subset_source
  have hsourceClean : ∀ p ∈ Jplus,
      p.support ∩ K.source ⊆ {p.initial} := by
    intro p hp x hx
    change x ∈ p.support ∩ G.source at hx
    exact Set.mem_singleton_iff.2
      (hNorm.eq_initial_of_mem_path p hx.1 hx.2)
  have hterminalSub : K.terminalFrontier Jplus ⊆ K.target := by
    rw [hterminal]
    exact Set.insert_subset hb.1 hJ.terminalFrontier_subset_target
  have hprotected : S ⊆ K.terminalFrontier Jplus := by
    intro x hxS
    rw [hterminal]
    exact Or.inr (hS hxS)
  have htargetClean : ∀ p ∈ Jplus, ∀ {x : V},
      x ∈ p.support → x ∈ K.target → K.terminal? p = some x := by
    intro p hp x hxp hxTarget
    change x ∈ G.target ∪ S at hxTarget
    rcases hxTarget with hxG | hxS
    · exact hNorm.terminal?_eq_of_mem_path p hxp hxG
    · exact K.fd_terminal_eq_of_mem_support_frontier
        hwarp hfinite hp hxp (hprotected hxS)
  apply K.fd_isCleanFiniteWarp_of_endpoint_clean
    hwarp hfinite hinitSub hsourceClean hterminalSub htargetClean

/-- Restrict a clean mixed augmentation to the designated initials and
repair all of its non-designated terminal colours by whole-component
replacement with the old designated linkage. -/
theorem exists_targetColouredComponentRepair_of_clean
    {K : DWeb V} {A B : Set V} {T Qplus : Set K.DPath}
    (hT : IsLinkageBetween K A B T)
    (hQplus : K.IsCleanFiniteWarp Qplus)
    (hA : A ⊆ K.initialSet Qplus) (hB : B ⊆ K.target) :
    ∃ Y Q : Set K.DPath,
      Y = initialRestriction K Qplus A ∧
      IsLinkageBetween K A K.target Y ∧
      IsLinkageBetween K A B Q := by
  let Y := initialRestriction K Qplus A
  have hQlink : IsLinkageBetween K (K.initialSet Qplus) K.target Qplus :=
    isLinkageBetween_of_cleanFiniteWarp hQplus
  have hY : IsLinkageBetween K A K.target Y :=
    isLinkageBetween_initialRestriction hQlink hA
  let Q := componentMixedFamily K T Y
    (badTerminalColour K Y B)
  have hQ : IsLinkageBetween K A B Q :=
    componentMixedFamily_repairs_terminalColour K hT hY hB
  exact ⟨Y, Q, rfl, hY, hQ⟩

/-- Support-retaining form of the clean component repair.  Every repaired
member is either an old designated member or a member of the designated
initial restriction of the mixed family. -/
theorem exists_targetColouredComponentRepair_of_clean_with_support
    {K : DWeb V} {A B : Set V} {T Qplus : Set K.DPath}
    (hT : IsLinkageBetween K A B T)
    (hQplus : K.IsCleanFiniteWarp Qplus)
    (hA : A ⊆ K.initialSet Qplus) (hB : B ⊆ K.target) :
    ∃ Y Q : Set K.DPath,
      Y = initialRestriction K Qplus A ∧
      IsLinkageBetween K A K.target Y ∧
      Q = componentMixedFamily K T Y (badTerminalColour K Y B) ∧
      Q ⊆ T ∪ Y ∧ IsLinkageBetween K A B Q := by
  let Y := initialRestriction K Qplus A
  have hQlink : IsLinkageBetween K (K.initialSet Qplus) K.target Qplus :=
    isLinkageBetween_of_cleanFiniteWarp hQplus
  have hY : IsLinkageBetween K A K.target Y :=
    isLinkageBetween_initialRestriction hQlink hA
  let Q := componentMixedFamily K T Y
    (badTerminalColour K Y B)
  have hQsub : Q ⊆ T ∪ Y := by
    rintro p (hp | hp)
    · exact Or.inl hp.1
    · exact Or.inr hp.1
  have hQ : IsLinkageBetween K A B Q :=
    componentMixedFamily_repairs_terminalColour K hT hY hB
  exact ⟨Y, Q, rfl, hY, rfl, hQsub, hQ⟩

#print axioms isLinkageBetween_of_cleanFiniteWarp
#print axioms cleanFiniteWarp_mono
#print axioms componentMixedFamily_repairs_terminalColour
#print axioms onePointAugmentation_clean_of_protectedFrontier
#print axioms exists_targetColouredComponentRepair_of_clean
#print axioms exists_targetColouredComponentRepair_of_clean_with_support

end SingularFiniteEndpointColorRepair
end CardinalInduction
end Erdos599
