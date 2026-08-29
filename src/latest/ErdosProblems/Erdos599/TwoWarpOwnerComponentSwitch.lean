/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IndexedWarpComponents
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Simultaneous switching on a whole two-warp owner component

A nonconvex set of removed reference edges cannot in general be repaired
along one distinguished alternating route.  The sound closure operation is
simultaneous: close under *whole path owners*, retain the `W`-members in the
resulting component, and retain the `Y`-members outside it.

This file proves the two facts needed from that operation without imposing a
normal form on alternating paths:

* the component mixture is again a warp, even when either input contains
  rays;
* every nontrivial finite path in the mixed relation which starts in the
  switched component is a fragment of one original `W`-member.

The latter is the relational replacement for the invalid inference from a
raw alternating run to an `AltPath.CompatibleInOrder` certificate.  Notice
that the theorem deliberately does not assert that two prescribed vertices
of the component are connected by the mixed relation.  Whole-component
closure is simultaneous and may put those vertices on distinct `W`-members.
-/

noncomputable section

open Set
open _root_.Erdos599.DirectedPath

namespace Erdos599
namespace TwoWarpOwnerComponentSwitch

open Alternating

universe u

variable {V : Type u} {G : DWeb V}

/-- The two input warps, regarded as a `Bool`-indexed family. -/
def pairFamily (W Y : Set G.DPath) : ULift.{u} Bool → Set G.DPath
  | ⟨false⟩ => W
  | ⟨true⟩ => Y

/-- Closure of `root` under whole members of both input warps. -/
def ownerComponent (W Y : Set G.DPath) (root : V) : Set V :=
  IndexedWarpComponents.component (pairFamily W Y) root

theorem mem_ownerComponent_self (W Y : Set G.DPath) (root : V) :
    root ∈ ownerComponent W Y root :=
  IndexedWarpComponents.mem_component_self (pairFamily W Y) root

/-- A `W`-member which touches the owner component is wholly contained in
it. -/
theorem support_subset_ownerComponent_left
    {W Y : Set G.DPath} {root x : V} {p : G.DPath}
    (hx : x ∈ ownerComponent W Y root) (hp : p ∈ W)
    (hxp : x ∈ p.support) : p.support ⊆ ownerComponent W Y root := by
  exact IndexedWarpComponents.support_subset_component_of_touches
    (W := pairFamily W Y) (i := ULift.up false) hx
      (by simpa [pairFamily] using hp) hxp

/-- A `Y`-member which touches the owner component is wholly contained in
it. -/
theorem support_subset_ownerComponent_right
    {W Y : Set G.DPath} {root x : V} {p : G.DPath}
    (hx : x ∈ ownerComponent W Y root) (hp : p ∈ Y)
    (hxp : x ∈ p.support) : p.support ⊆ ownerComponent W Y root := by
  exact IndexedWarpComponents.support_subset_component_of_touches
    (W := pairFamily W Y) (i := ULift.up true) hx
      (by simpa [pairFamily] using hp) hxp

/-- The original members selected on the switched component.  Initial
membership suffices because whole-owner closure contains every touched
member. -/
def selectedForward (W Y : Set G.DPath) (root : V) : Set G.DPath :=
  {p | p ∈ W ∧ p.initial ∈ ownerComponent W Y root}

/-- Reference members retained outside the switched component. -/
def retainedReference (W Y : Set G.DPath) (root : V) : Set G.DPath :=
  {p | p ∈ Y ∧ p.initial ∉ ownerComponent W Y root}

/-- Replace the reference family on the complete owner component of `root`
by the original family there. -/
def switchedFamily (W Y : Set G.DPath) (root : V) : Set G.DPath :=
  selectedForward W Y root ∪ retainedReference W Y root

/-- All reference edges belonging to an owner selected by the component.
Removing the entire owner, rather than an arbitrary nonconvex subset, is the
closure step which fills every reference-owner gap. -/
def removedReferenceEdges (W Y : Set G.DPath) (root : V) : Set (V × V) :=
  {e | e ∈ familyEdges Y ∧ e.1 ∈ ownerComponent W Y root}

/-- All forward edges on the selected original owners. -/
def insertedForwardEdges (W Y : Set G.DPath) (root : V) : Set (V × V) :=
  familyEdges (selectedForward W Y root)

/-- The literal relational whole-owner switch. -/
def switchedEdges (W Y : Set G.DPath) (root : V) : Set (V × V) :=
  (familyEdges Y \ removedReferenceEdges W Y root) ∪
    insertedForwardEdges W Y root

theorem selectedForward_support_subset
    {W Y : Set G.DPath} {root : V} {p : G.DPath}
    (hp : p ∈ selectedForward W Y root) :
    p.support ⊆ ownerComponent W Y root := by
  exact support_subset_ownerComponent_left hp.2 hp.1 p.initial_mem_support

theorem retainedReference_support_disjoint
    {W Y : Set G.DPath} {root : V} {p : G.DPath}
    (hp : p ∈ retainedReference W Y root) :
    Disjoint p.support (ownerComponent W Y root) := by
  apply Set.disjoint_left.2
  intro x hxp hxC
  have hsub : p.support ⊆ ownerComponent W Y root :=
    support_subset_ownerComponent_right hxC hp.1 hxp
  exact hp.2 (hsub p.initial_mem_support)

theorem removedReferenceEdges_subset
    (W Y : Set G.DPath) (root : V) :
    removedReferenceEdges W Y root ⊆ familyEdges Y :=
  fun _ h ↦ h.1

theorem insertedForwardEdges_subset
    (W Y : Set G.DPath) (root : V) :
    insertedForwardEdges W Y root ⊆ familyEdges W := by
  intro e he
  simp only [insertedForwardEdges, familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, he⟩ := he
  exact ⟨p, hp.1, he⟩

/-- Each reference owner is either removed in full or retained in full, so
the removed relation is interval-convex on every reference member. -/
theorem removedReferenceEdges_interval
    {W Y : Set G.DPath} (root : V) (p : G.DPath) (hpY : p ∈ Y) :
    IsEdgeInterval (removedReferenceEdges W Y root ∩ p.edgeSet) p := by
  by_cases hpC : p.initial ∈ ownerComponent W Y root
  · right
    refine ⟨p, p.isSubpathOf_self, Set.inter_eq_right.2 ?_⟩
    intro e he
    have hsub : p.support ⊆ ownerComponent W Y root :=
      support_subset_ownerComponent_right hpC hpY p.initial_mem_support
    change e ∈ familyEdges Y ∧ e.1 ∈ ownerComponent W Y root
    exact ⟨by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpY, he⟩, hsub (p.edgeSet_subset_support_prod he).1⟩
  · left
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨e, heR, hep⟩
    have hs := p.edgeSet_subset_support_prod hep
    have hsub : p.support ⊆ ownerComponent W Y root :=
      support_subset_ownerComponent_right heR.2 hpY hs.1
    exact hpC (hsub p.initial_mem_support)

/-- The path-family mixture realizes exactly the relational whole-owner
switch. -/
theorem familyEdges_switchedFamily
    (W Y : Set G.DPath) (root : V) :
    familyEdges (switchedFamily W Y root) = switchedEdges W Y root := by
  ext e
  simp only [switchedEdges, Set.mem_union]
  constructor
  · intro he
    simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨p, hp, hep⟩ := he
    rcases hp with hpW | hpY
    · apply Or.inr
      change e ∈ familyEdges (selectedForward W Y root)
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpW, hep⟩
    · refine Or.inl ⟨?_, ?_⟩
      · simp only [familyEdges, Set.mem_iUnion]
        exact ⟨p, hpY.1, hep⟩
      · intro heR
        exact Set.disjoint_left.1 (retainedReference_support_disjoint hpY)
          (p.edgeSet_subset_support_prod hep).1 heR.2
  · rintro (he | he)
    · rcases he with ⟨heY, heNotRemoved⟩
      simp only [familyEdges, Set.mem_iUnion] at heY ⊢
      obtain ⟨p, hpY, hep⟩ := heY
      have hpOutside : p.initial ∉ ownerComponent W Y root := by
        intro hpC
        have hsub : p.support ⊆ ownerComponent W Y root :=
          support_subset_ownerComponent_right hpC hpY p.initial_mem_support
        apply heNotRemoved
        change e ∈ familyEdges Y ∧ e.1 ∈ ownerComponent W Y root
        refine ⟨?_, hsub (p.edgeSet_subset_support_prod hep).1⟩
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨p, hpY, hep⟩
      exact ⟨p, Or.inr ⟨hpY, hpOutside⟩, hep⟩
    · change e ∈ familyEdges (selectedForward W Y root) at he
      simp only [familyEdges, Set.mem_iUnion] at he ⊢
      obtain ⟨p, hp, hep⟩ := he
      exact ⟨p, Or.inl hp, hep⟩

/-- The simultaneous whole-component exchange preserves vertex
disjointness.  No finite-character assumption is needed. -/
theorem switchedFamily_isWarp
    {W Y : Set G.DPath} (hW : G.IsWarp W) (hY : G.IsWarp Y)
    (root : V) : G.IsWarp (switchedFamily W Y root) := by
  intro p hp q hq hpq
  rcases hp with hpW | hpY
  · rcases hq with hqW | hqY
    · exact hW hpW.1 hqW.1 hpq
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 (retainedReference_support_disjoint hqY)
        hxq (selectedForward_support_subset hpW hxp)
  · rcases hq with hqW | hqY
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 (retainedReference_support_disjoint hpY)
        hxp (selectedForward_support_subset hqW hxq)
    · exact hY hpY.1 hqY.1 hpq

/-- The literal switched relation is locally biunique because it is exactly
the edge relation of the mixed warp. -/
theorem switchedEdges_biUnique
    {W Y : Set G.DPath} (hW : G.IsWarp W) (hY : G.IsWarp Y)
    (root : V) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ switchedEdges W Y root) := by
  rw [← familyEdges_switchedFamily]
  exact Alternating.IsWarp.familyEdges_biUnique
    (switchedFamily_isWarp hW hY root)

/-- In the exclusive-edge setting the inserted part satisfies the
disjointness premise of the relational interval-switching lemmas.  It is
kept as an explicit hypothesis because two arbitrary warps may share edges. -/
theorem insertedForwardEdges_disjoint_reference
    {W Y : Set G.DPath} (root : V)
    (hdisjoint : Disjoint (familyEdges W) (familyEdges Y)) :
    Disjoint (insertedForwardEdges W Y root) (familyEdges Y) :=
  hdisjoint.mono_left (insertedForwardEdges_subset W Y root)

/-- An exchanged edge whose tail lies in the switched component is an
original `W`-edge, and its head remains in the same owner component. -/
theorem switched_edge_from_component
    {W Y : Set G.DPath} {root x y : V}
    (hxy : (x, y) ∈ familyEdges (switchedFamily W Y root))
    (hx : x ∈ ownerComponent W Y root) :
    (x, y) ∈ familyEdges W ∧ y ∈ ownerComponent W Y root := by
  simp only [familyEdges, Set.mem_iUnion] at hxy ⊢
  obtain ⟨p, hp, hpxy⟩ := hxy
  rcases hp with hpW | hpY
  · have hs := p.edgeSet_subset_support_prod hpxy
    exact ⟨⟨p, hpW.1, hpxy⟩,
      selectedForward_support_subset hpW hs.2⟩
  · have hs := p.edgeSet_subset_support_prod hpxy
    exact False.elim <| Set.disjoint_left.1
      (retainedReference_support_disjoint hpY) hs.1 hx

/-- A finite walk starting in the exchanged component and using only mixed
edges never leaves that component and in fact uses only original `W` edges. -/
theorem walk_support_subset_and_edgeSet_subset_left
    {W Y : Set G.DPath} {root a b : V} (p : Walk G.graph a b)
    (ha : a ∈ ownerComponent W Y root)
    (hE : p.edgeSet ⊆ familyEdges (switchedFamily W Y root)) :
    (∀ x, x ∈ p.support → x ∈ ownerComponent W Y root) ∧
      p.edgeSet ⊆ familyEdges W := by
  induction p with
  | nil =>
      constructor
      · simpa using ha
      · simp
  | @cons a c b hac p ih =>
      have hacMixed : (a, c) ∈
          familyEdges (switchedFamily W Y root) :=
        hE (by simp [Walk.edgeSet])
      have hacData := switched_edge_from_component hacMixed ha
      have htail : p.edgeSet ⊆
          familyEdges (switchedFamily W Y root) := by
        intro e he
        exact hE (by simp [Walk.edgeSet, he])
      have hi := ih hacData.2 htail
      constructor
      · intro x hx
        simp only [Walk.support_cons, List.mem_cons] at hx
        exact hx.elim (fun h ↦ h ▸ ha) (fun hx ↦ hi.1 x hx)
      · intro e he
        simp only [Walk.edgeSet_cons] at he
        exact he.elim (fun h ↦ h ▸ hacData.1) (fun he ↦ hi.2 he)

/-- Relational confinement for the simultaneous component switch: every
nontrivial finite switched path beginning in the selected component is a
fragment of one original `W`-member. -/
theorem finitePath_isFragmentOf_left_of_start_mem_ownerComponent
    {W Y : Set G.DPath} (hW : G.IsWarp W) {root : V}
    (p : FinitePath G.graph) (hpne : p.start ≠ p.finish)
    (hstart : p.start ∈ ownerComponent W Y root)
    (hE : p.edgeSet ⊆ familyEdges (switchedFamily W Y root)) :
    Alternating.IsFragmentOf p W := by
  have hp := walk_support_subset_and_edgeSet_subset_left p.walk hstart hE
  exact SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hW p hpne hp.2

/-- The owner component is countable for two arbitrary warps, including
rays. -/
theorem ownerComponent_countable
    {W Y : Set G.DPath} (hW : G.IsWarp W) (hY : G.IsWarp Y)
    (root : V) : (ownerComponent W Y root).Countable := by
  change (IndexedWarpComponents.component (pairFamily W Y) root).Countable
  apply IndexedWarpComponents.component_countable_general
  · intro i
    rcases i with ⟨i⟩
    cases i <;> simp [pairFamily, hW, hY]
  · simpa [Cardinal.mk_uLift, Cardinal.mk_bool] using
      (Cardinal.nat_lt_aleph0 2).le

#print axioms switchedFamily_isWarp
#print axioms switchedEdges_biUnique
#print axioms removedReferenceEdges_interval
#print axioms familyEdges_switchedFamily
#print axioms switched_edge_from_component
#print axioms finitePath_isFragmentOf_left_of_start_mem_ownerComponent
#print axioms ownerComponent_countable

end TwoWarpOwnerComponentSwitch
end Erdos599
