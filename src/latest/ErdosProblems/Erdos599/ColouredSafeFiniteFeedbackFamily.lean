/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFiniteAuxiliaryRemoval
import ErdosProblems.Erdos599.ColouredSafeTrivialRows
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual matching paths for the finite feedback argument

An injection from safe terminals to exposed nonterminal sources gives
pairwise disjoint one-edge reference paths when those edges are present.
The finite auxiliary-removal obstruction then proves Hall's inequality.
Removing the adjacency hypothesis by an ambient graph lift is separate.
-/

noncomputable section

namespace Erdos599.Alternating.ColouredSafeFiniteFeedbackFamily

open Set DirectedPath ColouredSafeReverseReachability FiniteColouredOccurrenceWord

universe u

variable {V : Type u} {Gamma : DWeb V}

def edgePath {a b : V} (hne : a ≠ b) (h : Gamma.graph.Adj a b) :
    FinitePath Gamma.graph where
  start := a
  finish := b
  walk := .cons h .nil
  isPath := by simpa [Walk.IsPath] using hne

@[simp] theorem edgePath_support {a b : V} (hne : a ≠ b) (h : Gamma.graph.Adj a b) :
    (edgePath hne h).support = {a, b} := by
  ext x
  simp [edgePath, FinitePath.support]

@[simp] theorem edgePath_edges {a b : V} (hne : a ≠ b) (h : Gamma.graph.Adj a b) :
    (edgePath hne h).edgeSet = {(a, b)} := by
  simp [edgePath, FinitePath.edgeSet]

variable {S N : Set V}

def matchingPath (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) (t : N) : Gamma.DPath :=
  Sum.inl (edgePath
    (fun he ↦ Set.disjoint_left.mp hSN (he ▸ (f t).2) t.2) (hadj t))

def matchingFamily (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) : Set Gamma.DPath :=
  Set.range (matchingPath hSN f hadj)

@[simp] theorem matchingPath_support (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) (t : N) :
    (matchingPath hSN f hadj t).support = {(f t).1, t.1} :=
  edgePath_support _ _

@[simp] theorem matchingPath_edges (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) (t : N) :
    (matchingPath hSN f hadj t).edgeSet = {((f t).1, t.1)} :=
  edgePath_edges _ _

theorem matchingFamily_isWarp (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) :
    Gamma.IsWarp (matchingFamily hSN f hadj) := by
  rintro _ ⟨t, rfl⟩ _ ⟨r, rfl⟩ hne
  change Disjoint (matchingPath hSN f hadj t).support (matchingPath hSN f hadj r).support
  rw [matchingPath_support, matchingPath_support]
  apply Set.disjoint_left.mpr
  intro x hx ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ht
  rcases hx with hx | hx <;> rcases ht with ht | ht
  · exact hne (congrArg (matchingPath hSN f hadj)
      (f.injective (Subtype.ext (hx.symm.trans ht))))
  · exact Set.disjoint_left.mp hSN (hx ▸ (f t).2) (ht ▸ r.2)
  · exact Set.disjoint_left.mp hSN (ht ▸ (f r).2) (hx ▸ t.2)
  · exact hne (congrArg (matchingPath hSN f hadj) (Subtype.ext (hx.symm.trans ht)))

theorem matchingFamily_finiteCharacter (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) :
    Gamma.HasFiniteCharacter (matchingFamily hSN f hadj) := by
  rintro _ ⟨t, rfl⟩
  exact ⟨_, rfl⟩

theorem matchingFamily_vertexSet (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) :
    Gamma.vertexSet (matchingFamily hSN f hadj) =
      Set.range (fun t : N ↦ (f t).1) ∪ N := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, hx⟩
    rw [matchingPath_support] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨t, hx.symm⟩
    · exact Or.inr (Set.mem_singleton_iff.mp hx ▸ t.2)
  · rintro (⟨t, rfl⟩ | hx)
    · exact ⟨matchingPath hSN f hadj t, ⟨t, rfl⟩,
        by simp only [matchingPath_support, Set.mem_insert_iff, true_or]⟩
    · exact ⟨matchingPath hSN f hadj ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩,
        by simp only [matchingPath_support, Set.mem_insert_iff, Set.mem_singleton_iff,
          or_true]⟩

theorem matchingFamily_initialSet (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) :
    Gamma.initialSet (matchingFamily hSN f hadj) =
      Set.range (fun t : N ↦ (f t).1) := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, hx⟩
    exact ⟨t, hx⟩
  · rintro ⟨t, rfl⟩
    exact ⟨matchingPath hSN f hadj t, ⟨t, rfl⟩, rfl⟩

theorem matchingFamily_terminalFrontier (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) :
    Gamma.terminalFrontier (matchingFamily hSN f hadj) = N := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, hx⟩
    exact Option.some.inj hx ▸ t.2
  · intro hx
    exact ⟨matchingPath hSN f hadj ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩

theorem matchingFamily_edges (hSN : Disjoint S N) (f : N ↪ S)
    (hadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1) :
    familyEdges (matchingFamily hSN f hadj) =
      Set.range (fun t : N ↦ ((f t).1, t.1)) := by
  ext e
  simp only [familyEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, he⟩
    rw [matchingPath_edges, Set.mem_singleton_iff] at he
    exact ⟨t, he.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨matchingPath hSN f hadj t, ⟨t, rfl⟩, by simp⟩

variable {W Y : Set Gamma.DPath}

/-- A finite Hall deficit constructs an actual auxiliary matching reference
with an uncovered designated source. The original carriers may be infinite. -/
theorem exists_auxiliaryReference_of_deficit
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hNfinite : (safeTerminalUnion J).Finite)
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W)
    (hadj : ∀ s ∈ J, ∀ t ∈ safeTerminalUnion J, Gamma.graph.Adj s.1 t)
    (hsmall : (safeTerminalUnion J).ncard < J.ncard) :
    ∃ C : Set Gamma.DPath,
      Gamma.IsWarp (Y ∪ C) ∧ Gamma.HasFiniteCharacter (Y ∪ C) ∧
      (Gamma.vertexSet C).Finite ∧
      Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C) ∧
      (Gamma.initialSet (Y ∪ C) ⊆ Gamma.initialSet W) ∧
      (Gamma.terminalFrontier W ∩ Gamma.vertexSet (Y ∪ C) ⊆
        Gamma.terminalFrontier (Y ∪ C)) ∧
      (∀ {x y}, (x, y) ∈ familyEdges C → x ∈ Subtype.val '' J) ∧
      (Gamma.vertexSet C ⊆ Subtype.val '' J ∪ safeTerminalUnion J) ∧
      (safeTerminalUnion J ⊆ Gamma.vertexSet C) ∧
      ∃ s ∈ J, s.1 ∉ Gamma.vertexSet (Y ∪ C) := by
  classical
  let S : Set V := Subtype.val '' J
  let N : Set V := safeTerminalUnion J
  have hS : S.Finite := hJ.image _
  have hNT : N ⊆ Gamma.terminalFrontier W := by
    intro t ht
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_hsJ, hts⟩ := Set.mem_iUnion.mp hs
    exact hts.1.1
  have hN : N.Finite := hNfinite
  have hSI : S ⊆ Gamma.initialSet W := by
    rintro _ ⟨s, _hs, rfl⟩
    exact s.2.1
  have hSoff : Disjoint S (Gamma.vertexSet Y) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨s, _hs, rfl⟩ hy
    exact s.2.2 hy
  have hNoff : Disjoint N (Gamma.vertexSet Y) := by
    apply Set.disjoint_left.mpr
    intro t ht hy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_hsJ, hts⟩ := Set.mem_iUnion.mp hs
    exact hts.1.2 hy
  have hSnon : Disjoint S (Gamma.terminalFrontier W) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ ht
    exact hnonterminal s hs ht
  have hSN : Disjoint S N := hSnon.mono_right hNT
  have hdeficit : N.ncard < S.ncard := by
    rw [Set.ncard_image_of_injective J Subtype.val_injective]
    exact hsmall
  let : Fintype S := hS.fintype
  let : Fintype N := hN.fintype
  obtain ⟨f⟩ : Nonempty (N ↪ S) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Set.fintypeCard_eq_ncard] using hdeficit.le)
  have hfadj : ∀ t : N, Gamma.graph.Adj (f t).1 t.1 := by
    intro t
    obtain ⟨s, hsJ, hsf⟩ := (f t).2
    rw [← hsf]
    exact hadj s hsJ t.1 t.2
  let C := matchingFamily hSN f hfadj
  let R := Set.range (fun t : N ↦ (f t).1)
  have hRS : R ⊆ S := by
    rintro _ ⟨t, rfl⟩
    exact (f t).2
  have hCV : Gamma.vertexSet C = R ∪ N := matchingFamily_vertexSet hSN f hfadj
  have hCI : Gamma.initialSet C = R := matchingFamily_initialSet hSN f hfadj
  have hCT : Gamma.terminalFrontier C = N := matchingFamily_terminalFrontier hSN f hfadj
  have hYCdis : Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C) := by
    rw [hCV, Set.disjoint_union_right]
    exact ⟨(hSoff.mono_left hRS).symm, hNoff.symm⟩
  have hC : Gamma.IsWarp C := matchingFamily_isWarp hSN f hfadj
  have hYC : Gamma.IsWarp (Y ∪ C) := by
    intro p hp q hq hne
    change Disjoint p.support q.support
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact hY hp hq hne
    · exact Set.disjoint_left.mpr fun x hx hy ↦
        Set.disjoint_left.mp hYCdis ⟨p, hp, hx⟩ ⟨q, hq, hy⟩
    · exact Set.disjoint_left.mpr fun x hx hy ↦
        Set.disjoint_left.mp hYCdis ⟨q, hq, hy⟩ ⟨p, hp, hx⟩
    · exact hC hp hq hne
  have hYCfin : Gamma.HasFiniteCharacter (Y ∪ C) := by
    intro p hp
    rcases hp with hp | hp
    · exact hYfin hp
    · exact matchingFamily_finiteCharacter hSN f hfadj hp
  have hCfinite : (Gamma.vertexSet C).Finite := by
    rw [hCV]
    exact (Set.finite_range _).union hN
  have hYCsource : Gamma.initialSet (Y ∪ C) ⊆ Gamma.initialSet W := by
    rw [DWeb.initialSet_union, hCI]
    exact Set.union_subset hsource (hRS.trans hSI)
  have hYCterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet (Y ∪ C) ⊆
      Gamma.terminalFrontier (Y ∪ C) := by
    rw [DWeb.vertexSet_union, DWeb.terminalFrontier_union, hCV, hCT]
    rintro x ⟨ht, hy | hr | hn⟩
    · exact Or.inl (hterminal ⟨ht, hy⟩)
    · exact False.elim (Set.disjoint_left.mp hSnon (hRS hr) ht)
    · exact Or.inr hn
  have htails : ∀ {x y}, (x, y) ∈ familyEdges C → x ∈ Subtype.val '' J := by
    intro x y he
    rw [matchingFamily_edges] at he
    obtain ⟨t, he⟩ := he
    have heq : (f t).1 = x := congrArg Prod.fst he
    exact heq ▸ (f t).2
  have hcover : safeTerminalUnion J ⊆ Gamma.vertexSet C := by
    rw [hCV]
    exact Set.subset_union_right
  have huncovered : ∃ s ∈ J, s.1 ∉ Gamma.vertexSet (Y ∪ C) := by
    by_contra hnot
    have hcovered : S ⊆ Gamma.vertexSet (Y ∪ C) := by
      rintro _ ⟨s, hsJ, rfl⟩
      by_contra hsOff
      exact hnot ⟨s, hsJ, hsOff⟩
    have hSR : S ⊆ R := by
      intro s hs
      have hc := hcovered hs
      rw [DWeb.vertexSet_union, hCV] at hc
      rcases hc with hy | hr | hn
      · exact False.elim (Set.disjoint_left.mp hSoff hs hy)
      · exact hr
      · exact False.elim (Set.disjoint_left.mp hSN hs hn)
    have hcount : S.ncard ≤ N.ncard := by
      calc
        S.ncard ≤ R.ncard := Set.ncard_le_ncard hSR (Set.finite_range _)
        _ = N.ncard := by
          change (Set.range (Subtype.val ∘ f)).ncard = N.ncard
          rw [Set.ncard_range_of_injective (Subtype.val_injective.comp f.injective)]
          exact Nat.card_coe_set_eq N
    exact (not_le_of_gt hdeficit) hcount
  refine ⟨C, hYC, hYCfin, hCfinite, hYCdis, hYCsource, hYCterminal, htails,
    ?_, hcover, huncovered⟩
  rw [hCV]
  exact Set.union_subset_union_left N hRS

/-- Finite-carrier Hall for nonterminal sources, provided the auxiliary
matching edges can be drawn in the ambient graph. -/
theorem hall_nonterminal_of_auxiliaryAdj
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hWV : (Gamma.vertexSet W).Finite) (hYV : (Gamma.vertexSet Y).Finite)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W)
    (hadj : ∀ s ∈ J, ∀ t ∈ safeTerminalUnion J, Gamma.graph.Adj s.1 t) :
    J.ncard ≤ (safeTerminalUnion J).ncard := by
  by_contra hnot
  have hN : (safeTerminalUnion J).Finite := by
    apply hWV.subset
    intro t ht
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_hsJ, hts⟩ := Set.mem_iUnion.mp hs
    exact terminalFrontier_subset_vertexSet W hts.1.1
  obtain ⟨C, hYC, hYCfin, hCVfinite, hdisjoint, hsource', hterminal', htails,
    _hCV, hcover, s, hsJ, hsOff⟩ := exists_auxiliaryReference_of_deficit
      hY hYfin hsource hterminal hJ hN hnonterminal hadj (Nat.lt_of_not_ge hnot)
  have hYCV : (Gamma.vertexSet (Y ∪ C)).Finite := by
    rw [DWeb.vertexSet_union]
    exact hYV.union hCVfinite
  exact hsOff (ColouredSafeFiniteAuxiliaryRemoval.no_uncoveredSource_of_finite_auxiliary_cover
    hW hY hWfin hYfin hYC hYCfin hWV hYCV hdisjoint hsource' hterminal'
    hnonterminal htails hcover ⟨s, hsJ, rfl⟩)

#print axioms matchingFamily_isWarp
#print axioms matchingFamily_vertexSet
#print axioms matchingFamily_edges
#print axioms exists_auxiliaryReference_of_deficit
#print axioms hall_nonterminal_of_auxiliaryAdj

end Erdos599.Alternating.ColouredSafeFiniteFeedbackFamily
