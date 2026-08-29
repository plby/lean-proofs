/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteBadComponentExchange
import ErdosProblems.Erdos599.SingularFiniteExactBoundaryGlobalExchange

/-!
# Switching only the fresh alternating component

The first finite colour repair switched every component not forced back by a
bad designated terminal.  That is unnecessarily large.  In the successful
branch the component containing the two fresh endpoints contains no bad
designated terminal, so one can keep the old family on *all other*
components and use the new family only on this fresh component.

This localization is important for the remaining roof correction: every old
carrier vertex freed by the switch is then in the fresh component.  The file
establishes the component and endpoint-colour facts needed for that sharper
global exchange.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteFreshComponentRepair

open DWeb Alternating
open SliceCandidate SliceSpliceSource
open SingularComponentMixedAugmentation
open SingularFiniteEndpointColorRepair
open SingularMarkedResidualSimultaneousColourRepair

universe u

variable {V : Type u}

/-- Taking every vertex outside one alternating component as a set of roots
recovers exactly the complement of that component. -/
theorem exceptionalComponentVertices_compl_component
    (G : DWeb V) (W Y : Set G.DPath) (a : V) :
    exceptionalComponentVertices G W Y
        (AlternatingComponents.component W Y a)ᶜ =
      (AlternatingComponents.component W Y a)ᶜ := by
  ext x
  constructor
  · simp only [exceptionalComponentVertices, Set.mem_iUnion,
      Set.mem_compl_iff]
    rintro ⟨root, hroot, hxroot⟩ hx
    apply hroot
    exact AlternatingComponents.component_trans hx
      (AlternatingComponents.component_symm hxroot)
  · intro hx
    simp only [exceptionalComponentVertices, Set.mem_iUnion,
      Set.mem_compl_iff]
    exact ⟨x, hx, AlternatingComponents.mem_component_self W Y x⟩

/-- The component mixture rooted at the complement of `a`'s component uses
old paths off that component and new paths on it. -/
theorem componentMixedFamily_compl_component_eq
    (G : DWeb V) (W Y : Set G.DPath) (a : V) :
    componentMixedFamily G W Y
        (AlternatingComponents.component W Y a)ᶜ =
      initialPart G W (AlternatingComponents.component W Y a)ᶜ ∪
        initialPart G Y (AlternatingComponents.component W Y a) := by
  simp only [componentMixedFamily,
    exceptionalComponentVertices_compl_component, compl_compl]

/-- A one-point augmentation remains a one-point augmentation after keeping
only its fresh alternating component and reverting every other component. -/
theorem componentMixedFamily_compl_freshComponent_isOnePointAugmentation
    (G : DWeb V) {W Y : Set G.DPath} {a b : V}
    (hW : G.IsWarp W) (hWfinite : G.HasFiniteCharacter W)
    (hWfamilyFinite : W.Finite) (hYfamilyFinite : Y.Finite)
    (ha : a ∈ G.source \ G.initialSet W)
    (hb : b ∈ G.target \ G.terminalFrontier W)
    (hY : G.IsWarp Y) (hYfinite : G.HasFiniteCharacter Y)
    (hinit : G.initialSet Y = insert a (G.initialSet W))
    (hterm : G.terminalFrontier Y = insert b (G.terminalFrontier W)) :
    G.IsOnePointAugmentation W
      (componentMixedFamily G W Y
        (AlternatingComponents.component W Y a)ᶜ) := by
  have hab : b ∈ AlternatingComponents.component W Y a :=
    SingularFiniteAugmentationEndpointComponent.freshEndpoints_mem_same_component
      hW hY hWfinite hYfinite hWfamilyFinite hYfamilyFinite
        ha.2 hb.2 hinit hterm
  have haNot : a ∉ exceptionalComponentVertices G W Y
      (AlternatingComponents.component W Y a)ᶜ := by
    rw [exceptionalComponentVertices_compl_component]
    simpa only [Set.mem_compl_iff, not_not] using
      (AlternatingComponents.mem_component_self W Y a)
  have hbNot : b ∉ exceptionalComponentVertices G W Y
      (AlternatingComponents.component W Y a)ᶜ := by
    rw [exceptionalComponentVertices_compl_component]
    simpa only [Set.mem_compl_iff, not_not] using hab
  exact componentMixedFamily_isOnePointAugmentation_of_endpoints_compl
    G _ hW hWfinite ha hb hY hYfinite hinit hterm haNot hbNot

/-- If the fresh component is outside the canonical bad-terminal closure,
then it contains no bad terminal at all. -/
theorem badTerminalColour_disjoint_freshComponent_of_not_mem_exceptional
    (G : DWeb V) {W Y : Set G.DPath} {A B : Set V} {a : V}
    (ha : a ∉ exceptionalComponentVertices G W Y
      (badTerminalColour G (initialRestriction G Y A) B)) :
    Disjoint (badTerminalColour G (initialRestriction G Y A) B)
      (AlternatingComponents.component W Y a) := by
  rw [Set.disjoint_left]
  intro x hxBad hxFresh
  apply ha
  simp only [exceptionalComponentVertices, Set.mem_iUnion]
  exact ⟨x, hxBad, AlternatingComponents.component_symm hxFresh⟩

/-- Endpoint-colour repair for an arbitrary union of whole alternating
components, provided it contains every bad designated terminal.  The
canonical repair is the special case where the roots are the bad terminals
themselves; the fresh-component repair uses the complement of the fresh
component as roots. -/
theorem initialRestriction_componentMixedFamily_repairs_terminalColour_of_bad_subset
    (G : DWeb V) {W Y : Set G.DPath} {A B C E : Set V}
    (hW : IsLinkageBetween G (G.initialSet W) C W)
    (hY : IsLinkageBetween G (G.initialSet Y) C Y)
    (hAW : A ⊆ G.initialSet W) (hAY : A ⊆ G.initialSet Y)
    (hB : B ⊆ C)
    (hOld : IsLinkageBetween G A B (initialRestriction G W A))
    (hbad : badTerminalColour G (initialRestriction G Y A) B ⊆
      exceptionalComponentVertices G W Y E) :
    IsLinkageBetween G A B
      (initialRestriction G (componentMixedFamily G W Y E) A) := by
  let D := exceptionalComponentVertices G W Y E
  let Z := componentMixedFamily G W Y E
  let ZA := initialRestriction G Z A
  have hZwarp : G.IsWarp Z :=
    componentMixedFamily_isWarp G E hW.isWarp hY.isWarp
      hW.finiteCharacter hY.finiteCharacter
  have hZfinite : G.HasFiniteCharacter Z :=
    componentMixedFamily_hasFiniteCharacter G E
      hW.finiteCharacter hY.finiteCharacter
  have hZAwarp : G.IsWarp ZA := fun p hp q hq hpq ↦
    hZwarp hp.1 hq.1 hpq
  have hZAfinite : G.HasFiniteCharacter ZA := fun {_p} hp ↦
    hZfinite hp.1
  have hZAinitial : G.initialSet ZA = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact hp.2
    · intro x hxA
      by_cases hxD : x ∈ D
      · obtain ⟨p, hpW, hpx⟩ := hAW hxA
        refine ⟨p, ⟨Or.inl ⟨hpW, ?_⟩, ?_⟩, hpx⟩
        · exact hpx ▸ hxD
        · exact hpx ▸ hxA
      · obtain ⟨p, hpY, hpx⟩ := hAY hxA
        refine ⟨p, ⟨Or.inr ⟨hpY, ?_⟩, ?_⟩, hpx⟩
        · exact fun hpD ↦ hxD (hpx.symm ▸ hpD)
        · exact hpx ▸ hxA
  have hZAterminal : G.terminalFrontier ZA ⊆ B := by
    rintro x ⟨p, hpZA, hpx⟩
    rcases hpZA.1 with hpW | hpY
    · exact hOld.terminalFrontier_subset
        ⟨p, ⟨hpW.1, hpZA.2⟩, hpx⟩
    · by_contra hxB
      have hxBad : x ∈ badTerminalColour G
          (initialRestriction G Y A) B :=
        ⟨⟨p, ⟨hpY.1, hpZA.2⟩, hpx⟩, hxB⟩
      have hxD : x ∈ D := hbad hxBad
      have hpD : p.support ⊆ D :=
        path_support_subset_exceptionalComponents_right
          hY.finiteCharacter hpY.1 (G.terminal_mem_support hpx) hxD
      exact hpY.2 (hpD p.initial_mem_support)
  refine ⟨hZAwarp, hZAfinite, hZAinitial, hZAterminal, ?_⟩
  intro p hpZA
  have hpLarge : IsPathBetween G (G.initialSet W) C p ∨
      IsPathBetween G (G.initialSet Y) C p := by
    rcases hpZA.1 with hpW | hpY
    · exact Or.inl (hW.endpointPure p hpW.1)
    · exact Or.inr (hY.endpointPure p hpY.1)
  rcases hpLarge with hpW | hpY
  · apply SingularFiniteExactBoundaryGlobalExchange.IsPathBetween.narrow_endpoint_colours
      hpW hAW hB hpZA.2
    intro q hpq
    subst p
    exact hZAterminal ⟨.inl q, hpZA, rfl⟩
  · apply SingularFiniteExactBoundaryGlobalExchange.IsPathBetween.narrow_endpoint_colours
      hpY hAY hB hpZA.2
    intro q hpq
    subst p
    exact hZAterminal ⟨.inl q, hpZA, rfl⟩

/-- In the successful branch, switching only the fresh component still
repairs the designated terminal colour. -/
theorem initialRestriction_freshComponentMix_repairs_terminalColour
    (G : DWeb V) {W Y : Set G.DPath} {A B C : Set V} {a : V}
    (hW : IsLinkageBetween G (G.initialSet W) C W)
    (hY : IsLinkageBetween G (G.initialSet Y) C Y)
    (hAW : A ⊆ G.initialSet W) (hAY : A ⊆ G.initialSet Y)
    (hB : B ⊆ C)
    (hOld : IsLinkageBetween G A B (initialRestriction G W A))
    (ha : a ∉ exceptionalComponentVertices G W Y
      (badTerminalColour G (initialRestriction G Y A) B)) :
    IsLinkageBetween G A B
      (initialRestriction G
        (componentMixedFamily G W Y
          (AlternatingComponents.component W Y a)ᶜ) A) := by
  apply initialRestriction_componentMixedFamily_repairs_terminalColour_of_bad_subset
    G hW hY hAW hAY hB hOld
  intro x hxBad
  rw [exceptionalComponentVertices_compl_component]
  exact fun hxFresh ↦
    Set.disjoint_left.1
      (badTerminalColour_disjoint_freshComponent_of_not_mem_exceptional
        G ha) hxBad hxFresh

#print axioms exceptionalComponentVertices_compl_component
#print axioms componentMixedFamily_compl_freshComponent_isOnePointAugmentation
#print axioms badTerminalColour_disjoint_freshComponent_of_not_mem_exceptional
#print axioms initialRestriction_componentMixedFamily_repairs_terminalColour_of_bad_subset
#print axioms initialRestriction_freshComponentMix_repairs_terminalColour

end SingularFiniteFreshComponentRepair
end CardinalInduction
end Erdos599
