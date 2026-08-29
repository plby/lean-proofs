/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate

/-!
# The two fresh ends of a finite augmentation lie in one component

Whole-component colour repair is useful only if it does not separate the
new residual source from the new target.  This file records the finite
counting fact behind that assertion.  If two finite-character warps differ
by one initial vertex and one terminal vertex, then those two fresh vertices
belong to the same alternating component of the two families.

The finiteness of the two families is essential for this argument: on an
infinite component, cardinal arithmetic alone cannot detect the addition of
one endpoint.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteAugmentationEndpointComponent

open DWeb Alternating
open SliceCandidate

universe u

variable {V : Type u}

/-- A finite-character warp has equally many members, initial vertices, and
terminal vertices.  We only expose the equality of the two endpoint sets. -/
theorem ncard_initialSet_eq_terminalFrontier
    {G : DWeb V} {W : Set G.DPath}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W) :
    (G.initialSet W).ncard = (G.terminalFrontier W).ncard := by
  have hhasTerminal : ∀ p : G.DPath, p ∈ W →
      ∃ t, G.terminal? p = some t := by
    intro p hp
    obtain ⟨q, rfl⟩ := hfinite hp
    exact ⟨q.finish, rfl⟩
  let terminalValue : ∀ p : G.DPath, p ∈ W → V := fun p hp ↦
    Classical.choose (hhasTerminal p hp)
  have hterminalValue : ∀ p : G.DPath, ∀ hp : p ∈ W,
      G.terminal? p = some (terminalValue p hp) := by
    intro p hp
    exact Classical.choose_spec (hhasTerminal p hp)
  have hinitial : W.ncard = (G.initialSet W).ncard := by
    apply Set.ncard_congr (fun p _hp ↦ p.initial)
    · intro p hp
      exact ⟨p, hp, rfl⟩
    · intro p q hp hq hpq
      exact DWeb.IsWarp.eq_of_initial_eq G hW hp hq hpq
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨p, hp, rfl⟩
  have hterminal : W.ncard = (G.terminalFrontier W).ncard := by
    apply Set.ncard_congr terminalValue
    · intro p hp
      exact ⟨p, hp, hterminalValue p hp⟩
    · intro p q hp hq hpq
      exact DWeb.IsWarp.eq_of_terminal_eq G hW hp hq
        (hterminalValue p hp) (hpq ▸ hterminalValue q hq)
    · intro x hx
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨p, hp, ?_⟩
      exact Option.some.inj ((hterminalValue p hp).symm.trans hpx)
  exact hinitial.symm.trans hterminal

/-- Restricting a finite-character warp to the members whose initials lie
in one alternating component restricts its terminal frontier to that same
component. -/
theorem terminalFrontier_initialPart_component
    {G : DWeb V} {W Y : Set G.DPath}
    (hfinite : G.HasFiniteCharacter W) (root : V) :
    G.terminalFrontier
        (initialPart G W (AlternatingComponents.component W Y root)) =
      G.terminalFrontier W ∩
        AlternatingComponents.component W Y root := by
  let C := AlternatingComponents.component W Y root
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    have hpW : p ∈ W := hp.1
    obtain ⟨q, rfl⟩ := hfinite hpW
    have hsupport : q.support ⊆ C :=
      AlternatingComponents.finitePath_support_subset_component_of_touches_left
        hp.2 hpW q.start_mem_support
    exact ⟨⟨.inl q, hpW, hpx⟩,
      hsupport (G.terminal_mem_support hpx)⟩
  · rintro x ⟨⟨p, hpW, hpx⟩, hxC⟩
    obtain ⟨q, rfl⟩ := hfinite hpW
    have hsupport : q.support ⊆ C :=
      AlternatingComponents.finitePath_support_subset_component_of_touches_left
        hxC hpW (G.terminal_mem_support hpx)
    exact ⟨.inl q, ⟨hpW, hsupport q.start_mem_support⟩, hpx⟩

/-- Right-family version of `terminalFrontier_initialPart_component`. -/
theorem terminalFrontier_initialPart_component_right
    {G : DWeb V} {W Y : Set G.DPath}
    (hfinite : G.HasFiniteCharacter Y) (root : V) :
    G.terminalFrontier
        (initialPart G Y (AlternatingComponents.component W Y root)) =
      G.terminalFrontier Y ∩
        AlternatingComponents.component W Y root := by
  let C := AlternatingComponents.component W Y root
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    have hpY : p ∈ Y := hp.1
    obtain ⟨q, rfl⟩ := hfinite hpY
    have hsupport : q.support ⊆ C :=
      AlternatingComponents.finitePath_support_subset_component_of_touches_right
        hp.2 hpY q.start_mem_support
    exact ⟨⟨.inl q, hpY, hpx⟩,
      hsupport (G.terminal_mem_support hpx)⟩
  · rintro x ⟨⟨p, hpY, hpx⟩, hxC⟩
    obtain ⟨q, rfl⟩ := hfinite hpY
    have hsupport : q.support ⊆ C :=
      AlternatingComponents.finitePath_support_subset_component_of_touches_right
        hxC hpY (G.terminal_mem_support hpx)
    exact ⟨.inl q, ⟨hpY, hsupport q.start_mem_support⟩, hpx⟩

/-- Exact finite endpoint-component principle. -/
theorem freshEndpoints_mem_same_component
    {G : DWeb V} {W Y : Set G.DPath} {a b : V}
    (hWwarp : G.IsWarp W) (hYwarp : G.IsWarp Y)
    (hWcharacter : G.HasFiniteCharacter W)
    (hYcharacter : G.HasFiniteCharacter Y)
    (hWfinite : W.Finite) (hYfinite : Y.Finite)
    (ha : a ∉ G.initialSet W) (hb : b ∉ G.terminalFrontier W)
    (hinitial : G.initialSet Y = insert a (G.initialSet W))
    (hterminal : G.terminalFrontier Y = insert b (G.terminalFrontier W)) :
    b ∈ AlternatingComponents.component W Y a := by
  let C := AlternatingComponents.component W Y a
  by_contra hbC
  let WC := initialPart G W C
  let YC := initialPart G Y C
  have hWCwarp : G.IsWarp WC := fun p hp q hq hpq ↦
    hWwarp hp.1 hq.1 hpq
  have hYCwarp : G.IsWarp YC := fun p hp q hq hpq ↦
    hYwarp hp.1 hq.1 hpq
  have hWCcharacter : G.HasFiniteCharacter WC := fun {_p} hp ↦
    hWcharacter hp.1
  have hYCcharacter : G.HasFiniteCharacter YC := fun {_p} hp ↦
    hYcharacter hp.1
  have hWendpoint : (G.initialSet WC).ncard =
      (G.terminalFrontier WC).ncard :=
    ncard_initialSet_eq_terminalFrontier hWCwarp hWCcharacter
  have hYendpoint : (G.initialSet YC).ncard =
      (G.terminalFrontier YC).ncard :=
    ncard_initialSet_eq_terminalFrontier hYCwarp hYCcharacter
  have hinitW : G.initialSet WC = G.initialSet W ∩ C := by
    exact initialSet_initialPart G W C
  have hinitY : G.initialSet YC = G.initialSet Y ∩ C := by
    exact initialSet_initialPart G Y C
  have htermW : G.terminalFrontier WC = G.terminalFrontier W ∩ C :=
    terminalFrontier_initialPart_component hWcharacter a
  have htermY : G.terminalFrontier YC = G.terminalFrontier Y ∩ C :=
    terminalFrontier_initialPart_component_right hYcharacter a
  have haC : a ∈ C :=
    AlternatingComponents.mem_component_self W Y a
  have hinitInsert : G.initialSet Y ∩ C =
      insert a (G.initialSet W ∩ C) := by
    rw [hinitial]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨rfl | hxW, hxC⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hxW, hxC⟩
    · rintro (rfl | ⟨hxW, hxC⟩)
      · exact ⟨Or.inl rfl, haC⟩
      · exact ⟨Or.inr hxW, hxC⟩
  have htermEq : G.terminalFrontier Y ∩ C =
      G.terminalFrontier W ∩ C := by
    rw [hterminal]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨rfl | hxW, hxC⟩
      · exact False.elim (hbC hxC)
      · exact ⟨hxW, hxC⟩
    · rintro ⟨hxW, hxC⟩
      exact ⟨Or.inr hxW, hxC⟩
  have hIWfinite : (G.initialSet W ∩ C).Finite := by
    have hInitialFinite : (G.initialSet W).Finite := by
      simpa only [DWeb.initialSet] using
        hWfinite.image (fun p : G.DPath ↦ p.initial)
    exact hInitialFinite.inter_of_left C
  have haNotIW : a ∉ G.initialSet W ∩ C := fun h ↦ ha h.1
  have hsucc : (G.initialSet YC).ncard =
      (G.initialSet WC).ncard + 1 := by
    rw [hinitY, hinitW, hinitInsert,
      Set.ncard_insert_of_notMem haNotIW hIWfinite]
  have heq : (G.initialSet YC).ncard =
      (G.initialSet WC).ncard := by
    rw [hYendpoint, hWendpoint, htermY, htermW, htermEq]
  omega

/-- The endpoint-component principle packaged directly for a finite
one-point augmentation. -/
theorem IsOnePointAugmentation.freshEndpoints_mem_same_component
    {G : DWeb V} {W Y : Set G.DPath}
    (hWwarp : G.IsWarp W) (hWcharacter : G.HasFiniteCharacter W)
    (hWfinite : W.Finite) (hYfinite : Y.Finite)
    (hplus : G.IsOnePointAugmentation W Y) :
    ∃ a b : V,
      a ∈ G.source \ G.initialSet W ∧
      b ∈ G.target \ G.terminalFrontier W ∧
      b ∈ AlternatingComponents.component W Y a := by
  obtain ⟨a, ha, b, hb, hYwarp, hYcharacter, hinitial, hterminal⟩ := hplus
  exact ⟨a, b, ha, hb,
    SingularFiniteAugmentationEndpointComponent.freshEndpoints_mem_same_component
      (hWwarp := hWwarp) (hYwarp := hYwarp)
      (hWcharacter := hWcharacter) (hYcharacter := hYcharacter)
      hWfinite hYfinite ha.2 hb.2 hinitial hterminal⟩

/-- A union of whole old/new alternating components contains the fresh
source exactly when it contains the fresh terminal. -/
theorem mem_exceptionalComponentVertices_fresh_iff
    {G : DWeb V} {W Y : Set G.DPath} {a b : V} (S : Set V)
    (hab : b ∈ AlternatingComponents.component W Y a) :
    a ∈ exceptionalComponentVertices G W Y S ↔
      b ∈ exceptionalComponentVertices G W Y S := by
  constructor
  · intro ha
    simp only [exceptionalComponentVertices, Set.mem_iUnion] at ha ⊢
    obtain ⟨root, hrootS, haroot⟩ := ha
    exact ⟨root, hrootS,
      AlternatingComponents.component_trans haroot hab⟩
  · intro hb
    simp only [exceptionalComponentVertices, Set.mem_iUnion] at hb ⊢
    obtain ⟨root, hrootS, hbroot⟩ := hb
    have hab' : a ∈ AlternatingComponents.component W Y b :=
      AlternatingComponents.component_symm hab
    exact ⟨root, hrootS,
      AlternatingComponents.component_trans hbroot hab'⟩

/-- The previous dichotomy specialized to the endpoint data of a finite
one-point augmentation. -/
theorem exceptionalComponentVertices_fresh_iff_of_onePointAugmentation
    {G : DWeb V} {W Y : Set G.DPath} {a b : V}
    (hWwarp : G.IsWarp W) (hYwarp : G.IsWarp Y)
    (hWcharacter : G.HasFiniteCharacter W)
    (hYcharacter : G.HasFiniteCharacter Y)
    (hWfinite : W.Finite) (hYfinite : Y.Finite)
    (ha : a ∉ G.initialSet W) (hb : b ∉ G.terminalFrontier W)
    (hinitial : G.initialSet Y = insert a (G.initialSet W))
    (hterminal : G.terminalFrontier Y = insert b (G.terminalFrontier W))
    (S : Set V) :
    a ∈ exceptionalComponentVertices G W Y S ↔
      b ∈ exceptionalComponentVertices G W Y S := by
  apply mem_exceptionalComponentVertices_fresh_iff S
  exact freshEndpoints_mem_same_component hWwarp hYwarp
    hWcharacter hYcharacter hWfinite hYfinite ha hb hinitial hterminal

#print axioms ncard_initialSet_eq_terminalFrontier
#print axioms terminalFrontier_initialPart_component
#print axioms terminalFrontier_initialPart_component_right
#print axioms freshEndpoints_mem_same_component
#print axioms IsOnePointAugmentation.freshEndpoints_mem_same_component
#print axioms mem_exceptionalComponentVertices_fresh_iff
#print axioms exceptionalComponentVertices_fresh_iff_of_onePointAugmentation

end SingularFiniteAugmentationEndpointComponent
end CardinalInduction
end Erdos599
