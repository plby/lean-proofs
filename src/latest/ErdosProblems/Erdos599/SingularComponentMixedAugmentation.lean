/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteEndpointColorRepair
import ErdosProblems.Erdos599.SingularFiniteAugmentationEndpointComponent

/-!
# Componentwise localization of a one-point augmentation

The endpoint-colour repair uses `componentMixedFamily`, but its basic
structural properties do not require the two input families to have the
same boundary.  This file records those properties in the form needed for
a simultaneous two-colour repair.

For a one-point augmentation `Y` of `W`, retain `W` on a union `D` of
alternating components and retain `Y` off `D`.  If the new source and new
terminal are both off `D`, the mixed family is again a one-point
augmentation.  If both are in `D`, the mixed family has exactly the old
boundary.  Thus the only remaining issue in a colour-sensitive exchange is
to show that the two new endpoints lie in the same selected component; no
endpoint bookkeeping is lost by the component cut itself.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularComponentMixedAugmentation

open DWeb
open SliceCandidate
open SingularFiniteAugmentationEndpointComponent

universe u

variable {V : Type u}

/-- Mixing whole alternating components of two warps is still a warp.  No
agreement of their initial or terminal sets is needed. -/
theorem componentMixedFamily_isWarp
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V)
    (hW : G.IsWarp W) (hY : G.IsWarp Y)
    (hWfinite : G.HasFiniteCharacter W)
    (hYfinite : G.HasFiniteCharacter Y) :
    G.IsWarp (componentMixedFamily G W Y E) := by
  let D := exceptionalComponentVertices G W Y E
  let WL := initialPart G W D
  let YR := initialPart G Y Dᶜ
  have hWLsupport : ∀ p ∈ WL, p.support ⊆ D := by
    intro p hp
    exact path_support_subset_exceptionalComponents_left hWfinite
      hp.1 p.initial_mem_support hp.2
  have hYRsupport : ∀ p ∈ YR, Disjoint p.support D := by
    intro p hp
    rw [Set.disjoint_left]
    intro x hxp hxD
    exact hp.2 (path_support_subset_exceptionalComponents_right
      hYfinite hp.1 hxp hxD p.initial_mem_support)
  change G.IsWarp (WL ∪ YR)
  intro p hp q hq hpq
  rcases hp with hpWL | hpYR
  · rcases hq with hqWL | hqYR
    · exact hW hpWL.1 hqWL.1 hpq
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 (hYRsupport q hqYR) hxq
        (hWLsupport p hpWL hxp)
  · rcases hq with hqWL | hqYR
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 (hYRsupport p hpYR) hxp
        (hWLsupport q hqWL hxq)
    · exact hY hpYR.1 hqYR.1 hpq

/-- Finite character is inherited by a componentwise mixture. -/
theorem componentMixedFamily_hasFiniteCharacter
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V)
    (hWfinite : G.HasFiniteCharacter W)
    (hYfinite : G.HasFiniteCharacter Y) :
    G.HasFiniteCharacter (componentMixedFamily G W Y E) := by
  intro p hp
  exact hp.elim
    (fun hpW ↦ hWfinite hpW.1)
    (fun hpY ↦ hYfinite hpY.1)

/-- Exact initial boundary of a componentwise mixture. -/
theorem initialSet_componentMixedFamily
    (G : DWeb V) (W Y : Set G.DPath) (E : Set V) :
    let D := exceptionalComponentVertices G W Y E
    G.initialSet (componentMixedFamily G W Y E) =
      (G.initialSet W ∩ D) ∪ (G.initialSet Y ∩ Dᶜ) := by
  simp only [componentMixedFamily, G.initialSet_union,
    initialSet_initialPart]

/-- The terminal frontier of the left part is selected by the same
exceptional-component set as its initials. -/
theorem terminalFrontier_initialPart_exceptional_left
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V)
    (hWfinite : G.HasFiniteCharacter W) :
    let D := exceptionalComponentVertices G W Y E
    G.terminalFrontier (initialPart G W D) =
      G.terminalFrontier W ∩ D := by
  let D := exceptionalComponentVertices G W Y E
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨⟨p, hp.1, hpx⟩, ?_⟩
    exact path_support_subset_exceptionalComponents_left hWfinite
      hp.1 p.initial_mem_support hp.2 (G.terminal_mem_support hpx)
  · rintro ⟨⟨p, hpW, hpx⟩, hxD⟩
    have hpD : p.support ⊆ D :=
      path_support_subset_exceptionalComponents_left hWfinite
        hpW (G.terminal_mem_support hpx) hxD
    exact ⟨p, ⟨hpW, hpD p.initial_mem_support⟩, hpx⟩

/-- The terminal frontier of the right part is selected by the complement
of the exceptional-component set. -/
theorem terminalFrontier_initialPart_exceptional_right
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V)
    (hYfinite : G.HasFiniteCharacter Y) :
    let D := exceptionalComponentVertices G W Y E
    G.terminalFrontier (initialPart G Y Dᶜ) =
      G.terminalFrontier Y ∩ Dᶜ := by
  let D := exceptionalComponentVertices G W Y E
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨⟨p, hp.1, hpx⟩, ?_⟩
    intro hxD
    exact hp.2 (path_support_subset_exceptionalComponents_right
      hYfinite hp.1 (G.terminal_mem_support hpx) hxD
      p.initial_mem_support)
  · rintro ⟨⟨p, hpY, hpx⟩, hxNotD⟩
    refine ⟨p, ⟨hpY, ?_⟩, hpx⟩
    intro hpInitD
    exact hxNotD (path_support_subset_exceptionalComponents_right
      hYfinite hpY p.initial_mem_support hpInitD
      (G.terminal_mem_support hpx))

/-- Exact terminal boundary of a componentwise mixture. -/
theorem terminalFrontier_componentMixedFamily
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V)
    (hWfinite : G.HasFiniteCharacter W)
    (hYfinite : G.HasFiniteCharacter Y) :
    let D := exceptionalComponentVertices G W Y E
    G.terminalFrontier (componentMixedFamily G W Y E) =
      (G.terminalFrontier W ∩ D) ∪
        (G.terminalFrontier Y ∩ Dᶜ) := by
  rw [componentMixedFamily, G.terminalFrontier_union,
    terminalFrontier_initialPart_exceptional_left G E hWfinite,
    terminalFrontier_initialPart_exceptional_right G E hYfinite]

/-- If both new endpoints lie off the retained old components, component
mixing preserves the one-point augmentation exactly. -/
theorem componentMixedFamily_isOnePointAugmentation_of_endpoints_compl
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V) {a b : V}
    (hW : G.IsWarp W) (hWfinite : G.HasFiniteCharacter W)
    (ha : a ∈ G.source \ G.initialSet W)
    (hb : b ∈ G.target \ G.terminalFrontier W)
    (hY : G.IsWarp Y) (hYfinite : G.HasFiniteCharacter Y)
    (hinit : G.initialSet Y = insert a (G.initialSet W))
    (hterm : G.terminalFrontier Y = insert b (G.terminalFrontier W))
    (haD : a ∉ exceptionalComponentVertices G W Y E)
    (hbD : b ∉ exceptionalComponentVertices G W Y E) :
    G.IsOnePointAugmentation W (componentMixedFamily G W Y E) := by
  let D := exceptionalComponentVertices G W Y E
  have haD' : a ∉ D := by simpa only using haD
  have hbD' : b ∉ D := by simpa only using hbD
  refine ⟨a, ha, b, hb,
    componentMixedFamily_isWarp G E hW hY hWfinite hYfinite,
    componentMixedFamily_hasFiniteCharacter G E hWfinite hYfinite,
    ?_, ?_⟩
  · rw [initialSet_componentMixedFamily, hinit]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_insert_iff]
    constructor
    · rintro (⟨hxW, _hxD⟩ | ⟨hxa | hxW, _hxNotD⟩)
      · exact Or.inr hxW
      · exact Or.inl hxa
      · exact Or.inr hxW
    · rintro (rfl | hxW)
      · exact Or.inr ⟨Or.inl rfl, haD'⟩
      · by_cases hxD : x ∈ D
        · exact Or.inl ⟨hxW, hxD⟩
        · exact Or.inr ⟨Or.inr hxW, hxD⟩
  · rw [terminalFrontier_componentMixedFamily G E hWfinite hYfinite,
      hterm]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_insert_iff]
    constructor
    · rintro (⟨hxW, _hxD⟩ | ⟨hxb | hxW, _hxNotD⟩)
      · exact Or.inr hxW
      · exact Or.inl hxb
      · exact Or.inr hxW
    · rintro (rfl | hxW)
      · exact Or.inr ⟨Or.inl rfl, hbD'⟩
      · by_cases hxD : x ∈ D
        · exact Or.inl ⟨hxW, hxD⟩
        · exact Or.inr ⟨Or.inr hxW, hxD⟩

/-- If both new endpoints lie in the retained old components, component
mixing cancels the augmentation and restores the exact old boundary. -/
theorem componentMixedFamily_oldBoundary_of_endpoints_mem
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V) {a b : V}
    (hW : G.IsWarp W) (hWfinite : G.HasFiniteCharacter W)
    (ha : a ∈ G.source \ G.initialSet W)
    (hb : b ∈ G.target \ G.terminalFrontier W)
    (hY : G.IsWarp Y) (hYfinite : G.HasFiniteCharacter Y)
    (hinit : G.initialSet Y = insert a (G.initialSet W))
    (hterm : G.terminalFrontier Y = insert b (G.terminalFrontier W))
    (haD : a ∈ exceptionalComponentVertices G W Y E)
    (hbD : b ∈ exceptionalComponentVertices G W Y E) :
    G.IsWarp (componentMixedFamily G W Y E) ∧
      G.HasFiniteCharacter (componentMixedFamily G W Y E) ∧
      G.initialSet (componentMixedFamily G W Y E) = G.initialSet W ∧
      G.terminalFrontier (componentMixedFamily G W Y E) =
        G.terminalFrontier W := by
  let D := exceptionalComponentVertices G W Y E
  have haD' : a ∈ D := by simpa only using haD
  have hbD' : b ∈ D := by simpa only using hbD
  refine ⟨componentMixedFamily_isWarp G E hW hY hWfinite hYfinite,
    componentMixedFamily_hasFiniteCharacter G E hWfinite hYfinite,
    ?_, ?_⟩
  · rw [initialSet_componentMixedFamily, hinit]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_insert_iff]
    constructor
    · rintro (⟨hxW, _hxD⟩ | ⟨hxa | hxW, hxNotD⟩)
      · exact hxW
      · subst x
        exact False.elim (hxNotD haD')
      · exact hxW
    · intro hxW
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxW, hxD⟩
      · exact Or.inr ⟨Or.inr hxW, hxD⟩
  · rw [terminalFrontier_componentMixedFamily G E hWfinite hYfinite,
      hterm]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_insert_iff]
    constructor
    · rintro (⟨hxW, _hxD⟩ | ⟨hxb | hxW, hxNotD⟩)
      · exact hxW
      · subst x
        exact False.elim (hxNotD hbD')
      · exact hxW
    · intro hxW
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxW, hxD⟩
      · exact Or.inr ⟨Or.inr hxW, hxD⟩

/-- The two fresh endpoints of a finite augmentation belong to an
exceptional union of alternating components simultaneously. -/
theorem freshEndpoints_mem_exceptionalComponentVertices_iff
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V) {a b : V}
    (hW : G.IsWarp W) (hWfinite : G.HasFiniteCharacter W)
    (hWfamilyFinite : W.Finite) (hYfamilyFinite : Y.Finite)
    (ha : a ∈ G.source \ G.initialSet W)
    (hb : b ∈ G.target \ G.terminalFrontier W)
    (hY : G.IsWarp Y) (hYfinite : G.HasFiniteCharacter Y)
    (hinit : G.initialSet Y = insert a (G.initialSet W))
    (hterm : G.terminalFrontier Y = insert b (G.terminalFrontier W)) :
    a ∈ exceptionalComponentVertices G W Y E ↔
      b ∈ exceptionalComponentVertices G W Y E := by
  have habComponent :
      b ∈ AlternatingComponents.component W Y a :=
    freshEndpoints_mem_same_component hW hY hWfinite hYfinite
      hWfamilyFinite hYfamilyFinite ha.2 hb.2 hinit hterm
  constructor
  · intro haD
    simp only [exceptionalComponentVertices, Set.mem_iUnion] at haD ⊢
    obtain ⟨root, hrootE, haRoot⟩ := haD
    exact ⟨root, hrootE,
      AlternatingComponents.component_trans haRoot habComponent⟩
  · intro hbD
    simp only [exceptionalComponentVertices, Set.mem_iUnion] at hbD ⊢
    obtain ⟨root, hrootE, hbRoot⟩ := hbD
    exact ⟨root, hrootE,
      AlternatingComponents.component_trans hbRoot
        (AlternatingComponents.component_symm habComponent)⟩

/-- Unconditional finite component-cut dichotomy.  A whole-component mix
of a finite one-point augmentation either keeps both fresh endpoints and is
again an exact one-point augmentation, or discards both and has exactly the
old initial and terminal boundary. -/
theorem componentMixedFamily_onePointAugmentation_or_oldBoundary
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V)
    (hW : G.IsWarp W) (hWfinite : G.HasFiniteCharacter W)
    (hWfamilyFinite : W.Finite) (hYfamilyFinite : Y.Finite)
    (hplus : G.IsOnePointAugmentation W Y) :
    G.IsOnePointAugmentation W (componentMixedFamily G W Y E) ∨
      (G.IsWarp (componentMixedFamily G W Y E) ∧
        G.HasFiniteCharacter (componentMixedFamily G W Y E) ∧
        G.initialSet (componentMixedFamily G W Y E) = G.initialSet W ∧
        G.terminalFrontier (componentMixedFamily G W Y E) =
          G.terminalFrontier W) := by
  obtain ⟨a, ha, b, hb, hY, hYfinite, hinit, hterm⟩ := hplus
  let D := exceptionalComponentVertices G W Y E
  have habD : a ∈ D ↔ b ∈ D :=
    freshEndpoints_mem_exceptionalComponentVertices_iff G E
      hW hWfinite hWfamilyFinite hYfamilyFinite ha hb hY hYfinite
      hinit hterm
  by_cases haD : a ∈ D
  · right
    exact componentMixedFamily_oldBoundary_of_endpoints_mem G E
      hW hWfinite ha hb hY hYfinite hinit hterm haD (habD.mp haD)
  · left
    exact componentMixedFamily_isOnePointAugmentation_of_endpoints_compl G E
      hW hWfinite ha hb hY hYfinite hinit hterm haD
        (fun hbD ↦ haD (habD.mpr hbD))

#print axioms componentMixedFamily_isWarp
#print axioms terminalFrontier_componentMixedFamily
#print axioms componentMixedFamily_isOnePointAugmentation_of_endpoints_compl
#print axioms componentMixedFamily_oldBoundary_of_endpoints_mem
#print axioms freshEndpoints_mem_exceptionalComponentVertices_iff
#print axioms componentMixedFamily_onePointAugmentation_or_oldBoundary

end SingularComponentMixedAugmentation
end CardinalInduction
end Erdos599
