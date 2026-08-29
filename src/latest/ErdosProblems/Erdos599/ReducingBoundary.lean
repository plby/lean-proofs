/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CyclowarpDecomposition
import Mathlib.Algebra.BigOperators.Fin

/-!
# Boundary bookkeeping for reducing switches

Cycle components of a cyclowarp have both an incoming and an outgoing edge
at every vertex.  Consequently they do not contribute to either oriented
boundary, and discarding them preserves the boundary computed from the full
cyclowarp edge relation.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath
open scoped BigOperators

universe u

variable {V : Type u} {Γ : DWeb V}

/-- The cyclic successor on a nonempty finite cycle is surjective. -/
theorem DirectedCycle.exists_predecessor (C : DirectedCycle V)
    (i : Fin C.length) : ∃ j, C.next j = i := by
  by_cases hi : i.1 = 0
  · let j : Fin C.length :=
      ⟨C.length - 1, Nat.sub_lt C.positive (by omega)⟩
    refine ⟨j, Fin.ext ?_⟩
    simp only [DirectedCycle.next]
    dsimp [j]
    rw [Nat.sub_add_cancel C.positive]
    simp [hi]
  · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi
    let j : Fin C.length := ⟨i.1 - 1, by omega⟩
    refine ⟨j, Fin.ext ?_⟩
    simp only [DirectedCycle.next]
    dsimp [j]
    rw [Nat.sub_add_cancel hipos]
    exact Nat.mod_eq_of_lt i.2

theorem DirectedCycle.hasOutgoing_of_mem_support
    (C : DirectedCycle V) {x : V} (hx : x ∈ C.support) :
    HasOutgoing C.EdgeSet x := by
  rcases hx with ⟨i, rfl⟩
  exact ⟨C.vertex (C.next i), i, rfl⟩

theorem DirectedCycle.hasIncoming_of_mem_support
    (C : DirectedCycle V) {x : V} (hx : x ∈ C.support) :
    HasIncoming C.EdgeSet x := by
  rcases hx with ⟨i, rfl⟩
  rcases C.exists_predecessor i with ⟨j, hj⟩
  exact ⟨C.vertex j, j, by rw [hj]⟩

theorem DirectedCycle.hasIncoming_of_mem_edgeSet_source
    (C : DirectedCycle V) {x y : V} (hxy : (x, y) ∈ C.EdgeSet) :
    HasIncoming C.EdgeSet x := by
  rcases hxy with ⟨i, hi⟩
  have hx : x = C.vertex i := congrArg Prod.fst hi
  subst x
  exact C.hasIncoming_of_mem_support ⟨i, rfl⟩

theorem DirectedCycle.hasOutgoing_of_mem_edgeSet_target
    (C : DirectedCycle V) {x y : V} (hxy : (x, y) ∈ C.EdgeSet) :
    HasOutgoing C.EdgeSet y := by
  rcases hxy with ⟨i, hi⟩
  have hy : y = C.vertex (C.next i) := congrArg Prod.snd hi
  subst y
  exact C.hasOutgoing_of_mem_support ⟨C.next i, rfl⟩

/-- Directed cycles have no outgoing-only boundary vertices, so the
outgoing boundary of the full cyclowarp is exactly that of its path part. -/
theorem Cyclowarp.outgoingBoundary_edges_eq_pathPart (C : Cyclowarp Γ) :
    {x | HasOutgoing C.edges x ∧ ¬ HasIncoming C.edges x} =
      {x | HasOutgoing (familyEdges C.pathPart) x ∧
        ¬ HasIncoming (familyEdges C.pathPart) x} := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hnin⟩
    change (x, y) ∈ familyEdges C.paths ∪
      ⋃ c ∈ C.cycles, c.EdgeSet at hy
    rcases hy with hyp | hcyc
    · refine ⟨⟨y, hyp⟩, ?_⟩
      rintro ⟨z, hz⟩
      exact hnin ⟨z, Or.inl hz⟩
    · simp only [Set.mem_iUnion] at hcyc
      rcases hcyc with ⟨c, hcC, hxyc⟩
      obtain ⟨z, hzc⟩ := c.hasIncoming_of_mem_edgeSet_source hxyc
      exact False.elim (hnin ⟨z, Or.inr (Set.mem_iUnion.2
        ⟨c, Set.mem_iUnion.2 ⟨hcC, hzc⟩⟩)⟩)
  · rintro ⟨⟨y, hyp⟩, hnin⟩
    refine ⟨⟨y, Or.inl hyp⟩, ?_⟩
    rintro ⟨z, hz⟩
    change (z, x) ∈ familyEdges C.paths ∪
      ⋃ c ∈ C.cycles, c.EdgeSet at hz
    rcases hz with hzp | hzc
    · exact hnin ⟨z, hzp⟩
    · simp only [Set.mem_iUnion] at hzc
      rcases hzc with ⟨c, hcC, hzxc⟩
      simp only [familyEdges, Set.mem_iUnion] at hyp
      rcases hyp with ⟨p, hpC, hxyp⟩
      have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
      have hxc : x ∈ c.support := by
        rcases hzxc with ⟨i, hi⟩
        exact ⟨c.next i, (congrArg Prod.snd hi).symm⟩
      exact Set.disjoint_left.1 (C.paths_cycles_disjoint p hpC c hcC) hxp hxc

/-- Directed cycles have no incoming-only boundary vertices, so the
incoming boundary of the full cyclowarp is exactly that of its path part. -/
theorem Cyclowarp.incomingBoundary_edges_eq_pathPart (C : Cyclowarp Γ) :
    {x | HasIncoming C.edges x ∧ ¬ HasOutgoing C.edges x} =
      {x | HasIncoming (familyEdges C.pathPart) x ∧
        ¬ HasOutgoing (familyEdges C.pathPart) x} := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hnout⟩
    change (y, x) ∈ familyEdges C.paths ∪
      ⋃ c ∈ C.cycles, c.EdgeSet at hy
    rcases hy with hyp | hcyc
    · refine ⟨⟨y, hyp⟩, ?_⟩
      rintro ⟨z, hz⟩
      exact hnout ⟨z, Or.inl hz⟩
    · simp only [Set.mem_iUnion] at hcyc
      rcases hcyc with ⟨c, hcC, hyxc⟩
      obtain ⟨z, hzc⟩ := c.hasOutgoing_of_mem_edgeSet_target hyxc
      exact False.elim (hnout ⟨z, Or.inr (Set.mem_iUnion.2
        ⟨c, Set.mem_iUnion.2 ⟨hcC, hzc⟩⟩)⟩)
  · rintro ⟨⟨y, hyp⟩, hnout⟩
    refine ⟨⟨y, Or.inl hyp⟩, ?_⟩
    rintro ⟨z, hz⟩
    change (x, z) ∈ familyEdges C.paths ∪
      ⋃ c ∈ C.cycles, c.EdgeSet at hz
    rcases hz with hzp | hzc
    · exact hnout ⟨z, hzp⟩
    · simp only [Set.mem_iUnion] at hzc
      rcases hzc with ⟨c, hcC, hxzc⟩
      simp only [familyEdges, Set.mem_iUnion] at hyp
      rcases hyp with ⟨p, hpC, hypx⟩
      have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hypx |>.2
      have hxc : x ∈ c.support := by
        rcases hxzc with ⟨i, hi⟩
        exact ⟨i, (congrArg Prod.fst hi).symm⟩
      exact Set.disjoint_left.1 (C.paths_cycles_disjoint p hpC c hcC) hxp hxc

noncomputable def propInt (P : Prop) : Int := by
  classical
  exact if P then 1 else 0

noncomputable def edgeBalance (E : Set (V × V)) (x : V) : Int :=
  propInt (HasOutgoing E x) - propInt (HasIncoming E x)

private theorem propInt_or_of_disjoint {P Q : Prop} (h : ¬ (P ∧ Q)) :
    propInt (P ∨ Q) = propInt P + propInt Q := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [propInt, hp, hq] at h ⊢

private theorem hasOutgoing_sdiff_iff {E B : Set (V × V)} {x : V}
    (hBE : B ⊆ E)
    (huniq : Relator.RightUnique (fun a b ↦ (a, b) ∈ E)) :
    HasOutgoing (E \ B) x ↔ HasOutgoing E x ∧ ¬ HasOutgoing B x := by
  constructor
  · rintro ⟨y, hyE, hyB⟩
    refine ⟨⟨y, hyE⟩, ?_⟩
    rintro ⟨z, hzB⟩
    have hyz : y = z := huniq hyE (hBE hzB)
    subst z
    exact hyB hzB
  · rintro ⟨⟨y, hyE⟩, hnB⟩
    refine ⟨y, hyE, ?_⟩
    intro hyB
    exact hnB ⟨y, hyB⟩

private theorem hasIncoming_sdiff_iff {E B : Set (V × V)} {x : V}
    (hBE : B ⊆ E)
    (huniq : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E)) :
    HasIncoming (E \ B) x ↔ HasIncoming E x ∧ ¬ HasIncoming B x := by
  constructor
  · rintro ⟨y, hyE, hyB⟩
    refine ⟨⟨y, hyE⟩, ?_⟩
    rintro ⟨z, hzB⟩
    have hyz : y = z := huniq hyE (hBE hzB)
    subst z
    exact hyB hzB
  · rintro ⟨⟨y, hyE⟩, hnB⟩
    refine ⟨y, hyE, ?_⟩
    intro hyB
    exact hnB ⟨y, hyB⟩

private theorem outgoing_indicator_sdiff_add
    {E B : Set (V × V)} {x : V}
    (hBE : B ⊆ E)
    (huniq : Relator.RightUnique (fun a b ↦ (a, b) ∈ E)) :
    propInt (HasOutgoing (E \ B) x) + propInt (HasOutgoing B x) =
      propInt (HasOutgoing E x) := by
  rw [hasOutgoing_sdiff_iff hBE huniq]
  classical
  by_cases hE : HasOutgoing E x
  · by_cases hB : HasOutgoing B x <;> simp [propInt, hE, hB]
  · have hnB : ¬ HasOutgoing B x := by
      rintro ⟨y, hy⟩
      exact hE ⟨y, hBE hy⟩
    simp [propInt, hE, hnB]

private theorem incoming_indicator_sdiff_add
    {E B : Set (V × V)} {x : V}
    (hBE : B ⊆ E)
    (huniq : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E)) :
    propInt (HasIncoming (E \ B) x) + propInt (HasIncoming B x) =
      propInt (HasIncoming E x) := by
  rw [hasIncoming_sdiff_iff hBE huniq]
  classical
  by_cases hE : HasIncoming E x
  · by_cases hB : HasIncoming B x <;> simp [propInt, hE, hB]
  · have hnB : ¬ HasIncoming B x := by
      rintro ⟨y, hy⟩
      exact hE ⟨y, hBE hy⟩
    simp [propInt, hE, hnB]

private theorem outgoing_indicator_union
    {E F : Set (V × V)} {x : V}
    (huniq : Relator.RightUnique (fun a b ↦ (a, b) ∈ E ∪ F))
    (hdisj : Disjoint E F) :
    propInt (HasOutgoing (E ∪ F) x) =
      propInt (HasOutgoing E x) + propInt (HasOutgoing F x) := by
  have hor : HasOutgoing (E ∪ F) x ↔
      HasOutgoing E x ∨ HasOutgoing F x := by
    simp only [HasOutgoing, Set.mem_union]
    constructor
    · rintro ⟨y, hy | hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩
    · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
      · exact ⟨y, Or.inl hy⟩
      · exact ⟨y, Or.inr hy⟩
  rw [hor]
  apply propInt_or_of_disjoint
  rintro ⟨⟨y, hyE⟩, ⟨z, hzF⟩⟩
  have hyz : y = z := huniq (Or.inl hyE) (Or.inr hzF)
  subst z
  exact Set.disjoint_left.1 hdisj hyE hzF

private theorem incoming_indicator_union
    {E F : Set (V × V)} {x : V}
    (huniq : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E ∪ F))
    (hdisj : Disjoint E F) :
    propInt (HasIncoming (E ∪ F) x) =
      propInt (HasIncoming E x) + propInt (HasIncoming F x) := by
  have hor : HasIncoming (E ∪ F) x ↔
      HasIncoming E x ∨ HasIncoming F x := by
    simp only [HasIncoming, Set.mem_union]
    constructor
    · rintro ⟨y, hy | hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩
    · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
      · exact ⟨y, Or.inl hy⟩
      · exact ⟨y, Or.inr hy⟩
  rw [hor]
  apply propInt_or_of_disjoint
  rintro ⟨⟨y, hyE⟩, ⟨z, hzF⟩⟩
  have hyz : y = z := huniq (Or.inl hyE) (Or.inr hzF)
  subst z
  exact Set.disjoint_left.1 hdisj hyE hzF

/-- Removing a locally unique subrelation and adding a disjoint locally
unique relation changes edge balance by the balance of the added edges minus
the balance of the removed edges. -/
theorem edgeBalance_sdiff_union_eq_add_sub
    {E B F : Set (V × V)}
    (hBE : B ⊆ E)
    (houtE : Relator.RightUnique (fun a b ↦ (a, b) ∈ E))
    (hinE : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E))
    (houtS : Relator.RightUnique
      (fun a b ↦ (a, b) ∈ (E \ B) ∪ F))
    (hinS : Relator.LeftUnique
      (fun a b ↦ (a, b) ∈ (E \ B) ∪ F))
    (hdisj : Disjoint (E \ B) F) (x : V) :
    edgeBalance ((E \ B) ∪ F) x =
      edgeBalance E x + edgeBalance F x - edgeBalance B x := by
  simp only [edgeBalance]
  rw [outgoing_indicator_union houtS hdisj,
    incoming_indicator_union hinS hdisj]
  have ho := outgoing_indicator_sdiff_add hBE houtE (x := x)
  have hi := incoming_indicator_sdiff_add hBE hinE (x := x)
  omega

theorem BackwardLinksOn.directionEdges_subset_familyEdges
    {Z : Set Γ.DPath} {T : AltPath Γ.graph}
    (hback : BackwardLinksOn Z T) :
    T.directionEdges .backward ⊆ familyEdges Z := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  rcases he with ⟨l, hl, hdir, he⟩
  rcases hback l hl hdir with ⟨p, hpZ, hsub⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨p, hpZ, hsub.2 he⟩

theorem FiniteTrace.switchedEdges_eq_backward_sdiff_union_forward
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) :
    switchedEdges Z (.finite Q) =
      (familyEdges Z \ (AltPath.finite Q).directionEdges .backward) ∪
        (AltPath.finite Q).directionEdges .forward := by
  have hB := hQ.1.2.1.directionEdges_subset_familyEdges
  have hF := hQ.2.1.directionEdges_disjoint
  ext e
  have hQE : e ∈ (AltPath.finite Q).edgeSet ↔
      e ∈ (AltPath.finite Q).directionEdges .forward ∨
        e ∈ (AltPath.finite Q).directionEdges .backward := by
    rw [(AltPath.finite Q).edgeSet_eq_directionEdges_union]
    rfl
  constructor
  · rintro (⟨heZ, heQ⟩ | ⟨heQ, heZ⟩)
    · left
      exact ⟨heZ, fun heB ↦ heQ (hQE.2 (Or.inr heB))⟩
    · rcases hQE.1 heQ with heF | heB
      · exact Or.inr heF
      · exact False.elim (heZ (hB heB))
  · rintro (⟨heZ, heB⟩ | heF)
    · left
      exact ⟨heZ, fun heQ ↦ by
        rcases hQE.1 heQ with heF | heB'
        · exact Set.disjoint_left.1 hF heF heZ
        · exact heB heB'⟩
    · right
      refine ⟨hQE.2 (Or.inl heF), ?_⟩
      exact fun heZ ↦ Set.disjoint_left.1 hF heF heZ

theorem FiniteTrace.edgeBalance_switched_eq_add_directionBalances
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) (x : V) :
    edgeBalance (switchedEdges Z (.finite Q)) x =
      edgeBalance (familyEdges Z) x +
        edgeBalance ((AltPath.finite Q).directionEdges .forward) x -
        edgeBalance ((AltPath.finite Q).directionEdges .backward) x := by
  let E := familyEdges Z
  let B := (AltPath.finite Q).directionEdges .backward
  let F := (AltPath.finite Q).directionEdges .forward
  have hBE : B ⊆ E := hQ.1.2.1.directionEdges_subset_familyEdges
  have hFB : Disjoint (E \ B) F := by
    rw [Set.disjoint_left]
    intro e heEF heF
    exact Set.disjoint_left.1 hQ.2.1.directionEdges_disjoint heF heEF.1
  have houtE : Relator.RightUnique (fun a b ↦ (a, b) ∈ E) :=
    fun _ _ _ h₁ h₂ ↦ familyEdges_out_unique hQ.1.1 h₁ h₂
  have hinE : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E) :=
    fun _ _ _ h₁ h₂ ↦ familyEdges_in_unique hQ.1.1 h₁ h₂
  have houtS : Relator.RightUnique (fun a b ↦ (a, b) ∈ E \ B ∪ F) := by
    rw [← Q.switchedEdges_eq_backward_sdiff_union_forward hQ]
    exact fun _ _ _ h₁ h₂ ↦ Q.switchedEdges_out_unique hQ h₁ h₂
  have hinS : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E \ B ∪ F) := by
    rw [← Q.switchedEdges_eq_backward_sdiff_union_forward hQ]
    exact fun _ _ _ h₁ h₂ ↦ Q.switchedEdges_in_unique hQ h₁ h₂
  rw [Q.switchedEdges_eq_backward_sdiff_union_forward hQ]
  simp only [edgeBalance]
  rw [outgoing_indicator_union houtS hFB,
    incoming_indicator_union hinS hFB]
  have ho := outgoing_indicator_sdiff_add hBE houtE (x := x)
  have hi := incoming_indicator_sdiff_add hBE hinE (x := x)
  dsimp [E, B, F] at ho hi ⊢
  omega

theorem FinitePath.hasOutgoing_edgeSet_iff
    {D : Digraph V} (p : FinitePath D) (x : V) :
    HasOutgoing p.edgeSet x ↔ x ∈ p.support ∧ x ≠ p.finish := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨p.edgeSet_subset_support_prod hy |>.1,
      _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet p hy⟩
  · rintro ⟨hx, hne⟩
    exact _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      p hx hne

theorem FinitePath.hasIncoming_edgeSet_iff
    {D : Digraph V} (p : FinitePath D) (x : V) :
    HasIncoming p.edgeSet x ↔ x ∈ p.support ∧ x ≠ p.start := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨p.edgeSet_subset_support_prod hy |>.2,
      _root_.Erdos599.Alternating.FinitePath.target_ne_start_of_mem_edgeSet p hy⟩
  · rintro ⟨hx, hne⟩
    exact _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
      p hx hne

theorem FinitePath.edgeBalance_eq_endpoints
    {D : Digraph V} (p : FinitePath D) (hnontrivial : p.start ≠ p.finish)
    (x : V) :
    edgeBalance p.edgeSet x =
      propInt (x = p.start) - propInt (x = p.finish) := by
  classical
  rw [edgeBalance,
    _root_.Erdos599.Alternating.FinitePath.hasOutgoing_edgeSet_iff,
    _root_.Erdos599.Alternating.FinitePath.hasIncoming_edgeSet_iff]
  by_cases hxs : x = p.start
  · subst x
    have hmem : p.start ∈ p.support := p.start_mem_support
    simp [propInt, hmem, hnontrivial]
  · by_cases hxf : x = p.finish
    · subst x
      have hmem : p.finish ∈ p.support := p.finish_mem_support
      simp [propInt, hmem, hxs]
    · by_cases hx : x ∈ p.support <;> simp [propInt, hx, hxs, hxf]

private theorem FiniteTrace.sameDirection_outgoing_index_eq
    {D : Digraph V} (Q : FiniteTrace D)
    {i j : Fin (Q.lastIndex + 1)}
    (hdir : (Q.link i).direction = (Q.link j).direction)
    {x y z : V} (hxy : (x, y) ∈ (Q.link i).path.edgeSet)
    (hxz : (x, z) ∈ (Q.link j).path.edgeSet) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hcomp := Q.compatible i j hij
    cases hd : (Q.link i).direction <;>
      simp only [CompatibleInOrder, hd, ← hdir] at hcomp
    · rcases hcomp
          ((Q.link i).path.edgeSet_subset_support_prod hxy |>.1)
          ((Q.link j).path.edgeSet_subset_support_prod hxz |>.1) with h | h
      · exact _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
          (Q.link j).path hxz
          (by simpa [Link.exit, ← hdir, hd] using h.2)
      · exact _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
          (Q.link i).path hxy
          (by simpa [Link.exit, hd] using h.1)
    · rcases hcomp
          ((Q.link i).path.edgeSet_subset_support_prod hxy |>.1)
          ((Q.link j).path.edgeSet_subset_support_prod hxz |>.1) with h | h
      · exact _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
          (Q.link i).path hxy
          (by simpa [Link.entry, hd] using h.1)
      · exact _root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
          (Q.link j).path hxz
          (by simpa [Link.entry, ← hdir, hd] using h.2)
  · exact hne (Q.sameDirection_outgoing_index_eq hdir.symm hxz hxy).symm

private theorem FiniteTrace.sameDirection_incoming_index_eq
    {D : Digraph V} (Q : FiniteTrace D)
    {i j : Fin (Q.lastIndex + 1)}
    (hdir : (Q.link i).direction = (Q.link j).direction)
    {x y z : V} (hyx : (y, x) ∈ (Q.link i).path.edgeSet)
    (hzx : (z, x) ∈ (Q.link j).path.edgeSet) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hcomp := Q.compatible i j hij
    cases hd : (Q.link i).direction <;>
      simp only [CompatibleInOrder, hd, ← hdir] at hcomp
    · rcases hcomp
          ((Q.link i).path.edgeSet_subset_support_prod hyx |>.2)
          ((Q.link j).path.edgeSet_subset_support_prod hzx |>.2) with h | h
      · exact _root_.Erdos599.Alternating.FinitePath.target_ne_start_of_mem_edgeSet
          (Q.link i).path hyx
          (by simpa [Link.entry, hd] using h.1)
      · exact _root_.Erdos599.Alternating.FinitePath.target_ne_start_of_mem_edgeSet
          (Q.link j).path hzx
          (by simpa [Link.entry, ← hdir, hd] using h.2)
    · rcases hcomp
          ((Q.link i).path.edgeSet_subset_support_prod hyx |>.2)
          ((Q.link j).path.edgeSet_subset_support_prod hzx |>.2) with h | h
      · exact _root_.Erdos599.Alternating.FinitePath.target_ne_start_of_mem_edgeSet
          (Q.link j).path hzx
          (by simpa [Link.exit, ← hdir, hd] using h.2)
      · exact _root_.Erdos599.Alternating.FinitePath.target_ne_start_of_mem_edgeSet
          (Q.link i).path hyx
          (by simpa [Link.exit, hd] using h.1)
  · exact hne (Q.sameDirection_incoming_index_eq hdir.symm hzx hyx).symm

private theorem propInt_exists_eq_sum_of_unique
    {ι : Type*} [Fintype ι] (P : ι → Prop)
    (huniq : ∀ {i j}, P i → P j → i = j) :
    propInt (∃ i, P i) = ∑ i, propInt (P i) := by
  classical
  by_cases h : ∃ i, P i
  · rcases h with ⟨i, hi⟩
    have hex : ∃ j, P j := ⟨i, hi⟩
    rw [Finset.sum_eq_single i]
    · simp [propInt, hi, hex]
    · intro j _ hji
      have hnj : ¬ P j := fun hj ↦ hji (huniq hj hi)
      simp [propInt, hnj]
    · simp
  · have hall : ∀ i, ¬ P i := fun i hi ↦ h ⟨i, hi⟩
    simp [propInt, h, hall]

theorem FiniteTrace.directionEdges_edgeBalance_eq_sum
    {D : Digraph V} (Q : FiniteTrace D) (d : Direction) (x : V) :
    edgeBalance (AltPath.directionEdges (.finite Q) d) x =
      ∑ i, if (Q.link i).direction = d then
        edgeBalance (Q.link i).path.edgeSet x else 0 := by
  classical
  have hout : HasOutgoing (AltPath.directionEdges (.finite Q) d) x ↔
      ∃ i, (Q.link i).direction = d ∧
        HasOutgoing (Q.link i).path.edgeSet x := by
    simp only [HasOutgoing, AltPath.directionEdges, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨y, l, ⟨i, rfl⟩, hdir, hxy⟩
      exact ⟨i, hdir, y, hxy⟩
    · rintro ⟨i, hdir, y, hxy⟩
      exact ⟨y, Q.link i, ⟨i, rfl⟩, hdir, hxy⟩
  have hin : HasIncoming (AltPath.directionEdges (.finite Q) d) x ↔
      ∃ i, (Q.link i).direction = d ∧
        HasIncoming (Q.link i).path.edgeSet x := by
    simp only [HasIncoming, AltPath.directionEdges, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨y, l, ⟨i, rfl⟩, hdir, hyx⟩
      exact ⟨i, hdir, y, hyx⟩
    · rintro ⟨i, hdir, y, hyx⟩
      exact ⟨y, Q.link i, ⟨i, rfl⟩, hdir, hyx⟩
  have houtuniq : ∀ {i j},
      ((Q.link i).direction = d ∧
        HasOutgoing (Q.link i).path.edgeSet x) →
      ((Q.link j).direction = d ∧
        HasOutgoing (Q.link j).path.edgeSet x) → i = j := by
    rintro i j ⟨hdi, y, hiy⟩ ⟨hdj, z, hjz⟩
    exact Q.sameDirection_outgoing_index_eq (hdi.trans hdj.symm) hiy hjz
  have hinuniq : ∀ {i j},
      ((Q.link i).direction = d ∧
        HasIncoming (Q.link i).path.edgeSet x) →
      ((Q.link j).direction = d ∧
        HasIncoming (Q.link j).path.edgeSet x) → i = j := by
    rintro i j ⟨hdi, y, hiy⟩ ⟨hdj, z, hjz⟩
    exact Q.sameDirection_incoming_index_eq (hdi.trans hdj.symm) hiy hjz
  rw [edgeBalance, hout, hin,
    propInt_exists_eq_sum_of_unique _ houtuniq,
    propInt_exists_eq_sum_of_unique _ hinuniq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hdi : (Q.link i).direction = d <;>
    simp [edgeBalance, propInt, hdi]

theorem FiniteTrace.directionBalance_difference_eq_sum_entries
    (Q : FiniteTrace Γ.graph) (x : V) :
    edgeBalance ((AltPath.finite Q).directionEdges .forward) x -
        edgeBalance ((AltPath.finite Q).directionEdges .backward) x =
      ∑ i, (propInt (x = (Q.link i).entry) -
        propInt (x = (Q.link i).exit)) := by
  classical
  rw [Q.directionEdges_edgeBalance_eq_sum,
    Q.directionEdges_edgeBalance_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hpath := _root_.Erdos599.Alternating.FinitePath.edgeBalance_eq_endpoints
    (Q.link i).path
    (Q.link i).nontrivial x
  cases hdir : (Q.link i).direction
  · simp [hdir, hpath, Link.entry, Link.exit]
  · simp [hdir, hpath, Link.entry, Link.exit]

theorem FiniteTrace.sum_entry_exit_eq_boundary
    (Q : FiniteTrace Γ.graph) (x : V) :
    (∑ i, (propInt (x = (Q.link i).entry) -
        propInt (x = (Q.link i).exit))) =
      propInt (x = Q.initial) - propInt (x = Q.terminal) := by
  classical
  rw [Finset.sum_sub_distrib]
  have hentry := Fin.sum_univ_succ
    (fun i : Fin (Q.lastIndex + 1) ↦ propInt (x = (Q.link i).entry))
  have hexit := Fin.sum_univ_castSucc
    (fun i : Fin (Q.lastIndex + 1) ↦ propInt (x = (Q.link i).exit))
  rw [hentry, hexit]
  have hmiddle :
      (∑ i : Fin Q.lastIndex,
        propInt (x = (Q.link i.succ).entry)) =
      ∑ i : Fin Q.lastIndex,
        propInt (x = (Q.link i.castSucc).exit) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.joins i]
  rw [hmiddle]
  change propInt (x = (Q.link 0).entry) +
      (∑ i : Fin Q.lastIndex,
        propInt (x = (Q.link i.castSucc).exit)) -
      ((∑ i : Fin Q.lastIndex,
        propInt (x = (Q.link i.castSucc).exit)) +
        propInt (x = (Q.link (Fin.last Q.lastIndex)).exit)) =
    propInt (x = (Q.link 0).entry) -
      propInt (x = (Q.link (Fin.last Q.lastIndex)).exit)
  omega

theorem FiniteTrace.hasReducingBalanceDelta
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) (x : V) :
    edgeBalance (switchedEdges Z (.finite Q)) x =
      edgeBalance (familyEdges Z) x + propInt (x = Q.initial) -
        propInt (x = Q.terminal) := by
  rw [Q.edgeBalance_switched_eq_add_directionBalances hQ]
  have hdir := Q.directionBalance_difference_eq_sum_entries x
  have hsum := Q.sum_entry_exit_eq_boundary x
  omega

theorem edgeBalance_eq_one_iff {E : Set (V × V)} {x : V} :
    edgeBalance E x = 1 ↔ HasOutgoing E x ∧ ¬ HasIncoming E x := by
  classical
  by_cases hout : HasOutgoing E x <;>
    by_cases hin : HasIncoming E x <;>
    simp [edgeBalance, propInt, hout, hin]

theorem edgeBalance_eq_neg_one_iff {E : Set (V × V)} {x : V} :
    edgeBalance E x = -1 ↔ HasIncoming E x ∧ ¬ HasOutgoing E x := by
  classical
  by_cases hout : HasOutgoing E x <;>
    by_cases hin : HasIncoming E x <;>
    simp [edgeBalance, propInt, hout, hin]

theorem mem_initialSet_iff_isolated_or_edgeBalance_eq_one
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hWfin : Γ.HasFiniteCharacter W) {x : V} :
    x ∈ Γ.initialSet W ↔
      x ∈ isolatedVertices W ∨ edgeBalance (familyEdges W) x = 1 := by
  rw [initialSet_eq_isolated_union_outgoing_boundary hW hWfin]
  simp only [Set.mem_union, Set.mem_setOf_eq, edgeBalance_eq_one_iff]

theorem mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hWfin : Γ.HasFiniteCharacter W) {x : V} :
    x ∈ Γ.terminalFrontier W ↔
      x ∈ isolatedVertices W ∨ edgeBalance (familyEdges W) x = -1 := by
  rw [terminalFrontier_eq_isolated_union_incoming_boundary hW hWfin]
  simp only [Set.mem_union, Set.mem_setOf_eq, edgeBalance_eq_neg_one_iff]

theorem Cyclowarp.mem_initialSet_pathPart_iff_isolated_or_edgeBalance_eq_one
    (C : Cyclowarp Γ) (hCfin : Γ.HasFiniteCharacter C.pathPart) {x : V} :
    x ∈ Γ.initialSet C.pathPart ↔
      x ∈ C.isolated ∨ edgeBalance C.edges x = 1 := by
  rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one C.pathPart_isWarp hCfin]
  change x ∈ C.isolated ∨ edgeBalance (familyEdges C.pathPart) x = 1 ↔ _
  rw [edgeBalance_eq_one_iff, edgeBalance_eq_one_iff]
  change x ∈ C.isolated ∨
      x ∈ {y | HasOutgoing (familyEdges C.pathPart) y ∧
        ¬ HasIncoming (familyEdges C.pathPart) y} ↔
    x ∈ C.isolated ∨
      x ∈ {y | HasOutgoing C.edges y ∧ ¬ HasIncoming C.edges y}
  rw [← C.outgoingBoundary_edges_eq_pathPart]

theorem Cyclowarp.mem_terminalFrontier_pathPart_iff_isolated_or_edgeBalance_eq_neg_one
    (C : Cyclowarp Γ) (hCfin : Γ.HasFiniteCharacter C.pathPart) {x : V} :
    x ∈ Γ.terminalFrontier C.pathPart ↔
      x ∈ C.isolated ∨ edgeBalance C.edges x = -1 := by
  rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
    C.pathPart_isWarp hCfin]
  change x ∈ C.isolated ∨ edgeBalance (familyEdges C.pathPart) x = -1 ↔ _
  rw [edgeBalance_eq_neg_one_iff, edgeBalance_eq_neg_one_iff]
  change x ∈ C.isolated ∨
      x ∈ {y | HasIncoming (familyEdges C.pathPart) y ∧
        ¬ HasOutgoing (familyEdges C.pathPart) y} ↔
    x ∈ C.isolated ∨
      x ∈ {y | HasIncoming C.edges y ∧ ¬ HasOutgoing C.edges y}
  rw [← C.incomingBoundary_edges_eq_pathPart]

theorem not_isolated_of_hasIncoming
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) {x : V}
    (hin : HasIncoming (familyEdges W) x) :
    x ∉ isolatedVertices W := by
  intro hx
  exact not_hasIncoming_of_mem_isolatedVertices hW hx hin

theorem not_isolated_of_hasOutgoing
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) {x : V}
    (hout : HasOutgoing (familyEdges W) x) :
    x ∉ isolatedVertices W := by
  intro hx
  exact not_hasOutgoing_of_mem_isolatedVertices hW hx hout

theorem FiniteTrace.reducing_start_hasIncoming
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsAlternating Z (.finite Q)) {v : V}
    (hv : v ∈ Γ.terminalFrontier Z)
    (hQi : (AltPath.finite Q).initial = v) :
    HasIncoming (familyEdges Z) v := by
  have hnontrivial :
      ∀ x, (AltPath.finite Q : AltPath Γ.graph) ≠ .trivial x := by
    intro x h
    cases h
  have hdir : Q.firstLink.direction = .backward := by
    have h := firstDirection_eq_backward_of_initial_mem hQ
      (by
        rw [hQi]
        exact terminalFrontier_subset_vertexSet Z hv)
      hnontrivial
    simpa [AltPath.firstDirection?] using Option.some.inj h
  have hfinish : Q.firstLink.path.finish = v := by
    rw [← hQi]
    change Q.firstLink.path.finish = Q.firstLink.entry
    simp [Link.entry, hdir]
  have hne : Q.firstLink.path.finish ≠ Q.firstLink.path.start :=
    Q.firstLink.nontrivial.symm
  rcases _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
      Q.firstLink.path Q.firstLink.path.finish_mem_support hne with ⟨y, hy⟩
  rcases hQ.2.1 Q.firstLink Q.firstLink_mem_links hdir with
    ⟨p, hpZ, hpSub⟩
  refine ⟨y, ?_⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨p, hpZ, hpSub.2 (hfinish ▸ hy)⟩

theorem FiniteTrace.reducing_terminal_hasOutgoing
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsAlternating Z (.finite Q)) {u : V}
    (hu : u ∈ Γ.initialSet Z)
    (hQt : (AltPath.finite Q).terminal? = some u) :
    HasOutgoing (familyEdges Z) u := by
  have hnontrivial :
      ∀ x, (AltPath.finite Q : AltPath Γ.graph) ≠ .trivial x := by
    intro x h
    cases h
  have hdir : Q.lastLink.direction = .backward := by
    have h := lastDirection_eq_backward_of_terminal_mem hQ hQt
      (initialSet_subset_vertexSet Z hu) hnontrivial
    simpa [AltPath.lastDirection?] using Option.some.inj h
  have hstart : Q.lastLink.path.start = u := by
    have ht : Q.terminal = u := by
      simpa [AltPath.terminal?] using Option.some.inj hQt
    rw [← ht]
    change Q.lastLink.path.start = Q.lastLink.exit
    simp [Link.exit, hdir]
  have hne : Q.lastLink.path.start ≠ Q.lastLink.path.finish :=
    Q.lastLink.nontrivial
  rcases _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      Q.lastLink.path Q.lastLink.path.start_mem_support hne with ⟨y, hy⟩
  rcases hQ.2.1 Q.lastLink Q.lastLink_mem_links hdir with
    ⟨p, hpZ, hpSub⟩
  refine ⟨y, ?_⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨p, hpZ, hpSub.2 (hstart ▸ hy)⟩

theorem FiniteTrace.reducing_endpoints_ne
    {Z : Set Γ.DPath} (hZfin : Γ.HasFiniteCharacter Z)
    (Q : FiniteTrace Γ.graph) (hQ : IsAlternating Z (.finite Q))
    {v u : V} (hv : v ∈ Γ.terminalFrontier Z)
    (hQi : (AltPath.finite Q).initial = v)
    (hu : u ∈ Γ.initialSet Z)
    (hQt : (AltPath.finite Q).terminal? = some u) :
    v ≠ u := by
  have hvin := Q.reducing_start_hasIncoming hQ hv hQi
  have huout := Q.reducing_terminal_hasOutgoing hQ hu hQt
  have hvniso := not_isolated_of_hasIncoming hQ.1 hvin
  have huniso := not_isolated_of_hasOutgoing hQ.1 huout
  have hvbal : edgeBalance (familyEdges Z) v = -1 :=
    (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hQ.1 hZfin).1 hv |>.resolve_left hvniso
  have hubal : edgeBalance (familyEdges Z) u = 1 :=
    (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
      hQ.1 hZfin).1 hu |>.resolve_left huniso
  intro hvu
  subst u
  omega

/-- Exact boundary delta for the path part of a concrete finite reducing
switch.  The unchanged ISO data remember unaffected singleton components;
the signed trace balance removes precisely the old initial endpoint `u` and
the old terminal endpoint `v`. -/
theorem Cyclowarp.pathPart_frontiers_eq_sdiff_of_finite_reducing
    {Z : Set Γ.DPath} (hZfin : Γ.HasFiniteCharacter Z)
    (Q : FiniteTrace Γ.graph) (hQ : IsSwitchingAlternating Z (.finite Q))
    {v u : V} (hv : v ∈ Γ.terminalFrontier Z)
    (hQi : (AltPath.finite Q).initial = v)
    (hu : u ∈ Γ.initialSet Z)
    (hQt : (AltPath.finite Q).terminal? = some u)
    (C : Cyclowarp Γ)
    (hEdges : C.edges = (Cyclowarp.application Z (.finite Q)).edges)
    (hIso : C.isolated = (Cyclowarp.application Z (.finite Q)).isolated)
    (hCfin : Γ.HasFiniteCharacter C.pathPart) :
    Γ.initialSet C.pathPart = Γ.initialSet Z \ {u} ∧
      Γ.terminalFrontier C.pathPart = Γ.terminalFrontier Z \ {v} := by
  classical
  have hvin := Q.reducing_start_hasIncoming hQ.1 hv hQi
  have huout := Q.reducing_terminal_hasOutgoing hQ.1 hu hQt
  have hvniso := not_isolated_of_hasIncoming hQ.1.1 hvin
  have huniso := not_isolated_of_hasOutgoing hQ.1.1 huout
  have hvbal : edgeBalance (familyEdges Z) v = -1 :=
    (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hQ.1.1 hZfin).1 hv |>.resolve_left hvniso
  have hubal : edgeBalance (familyEdges Z) u = 1 :=
    (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
      hQ.1.1 hZfin).1 hu |>.resolve_left huniso
  have hvu : v ≠ u := Q.reducing_endpoints_ne hZfin hQ.1 hv hQi hu hQt
  have huv : u ≠ v := hvu.symm
  have hinitial : Q.initial = v := hQi
  have hterminal : Q.terminal = u := by
    simpa [AltPath.terminal?] using Option.some.inj hQt
  have hbalance : ∀ x,
      edgeBalance C.edges x = edgeBalance (familyEdges Z) x +
        propInt (x = v) - propInt (x = u) := by
    intro x
    rw [hEdges, Cyclowarp.application_edges,
      Q.hasReducingBalanceDelta hQ, hinitial, hterminal]
  have hIso' : C.isolated = isolatedVertices Z := by
    simpa [Cyclowarp.application_isolated] using hIso
  constructor
  · ext x
    rw [C.mem_initialSet_pathPart_iff_isolated_or_edgeBalance_eq_one hCfin]
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one hQ.1.1 hZfin,
      hIso', hbalance]
    by_cases hxv : x = v
    · subst x
      simp [propInt, hvniso, hvbal, hvu]
    · by_cases hxu : x = u
      · subst x
        simp [propInt, huniso, hubal, hvu, huv]
      · simp [propInt, hxv, hxu]
  · ext x
    rw [C.mem_terminalFrontier_pathPart_iff_isolated_or_edgeBalance_eq_neg_one
      hCfin]
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hQ.1.1 hZfin, hIso', hbalance]
    by_cases hxv : x = v
    · subst x
      simp [propInt, hvniso, hvbal, hvu]
    · by_cases hxu : x = u
      · subst x
        simp [propInt, huniso, hubal, hvu, huv]
      · simp [propInt, hxv, hxu]


end Alternating
end Erdos599
