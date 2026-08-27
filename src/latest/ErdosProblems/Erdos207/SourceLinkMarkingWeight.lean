/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMarking

/-! # Root deletion and product weights for three-mark link coordinates -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceLinkTriangleWeight
    {V : Type*} [DecidableEq V] (f₀ f₁ f₂ : TripleOn V → ℝ≥0) :
    SourceLinkTriangleCoordinate V → ℝ≥0 := Sum.elim f₀ (Sum.elim f₁ f₂)

def sourceLinkMixedWeight
    {V : Type*} [DecidableEq V] (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) :
    SourceLinkCoordinate V → ℝ≥0 := Sum.elim (sourceLinkTriangleWeight f₀ f₁ f₂) fe

theorem disjoint_colored_sdiff_union
    {A : Type*} [DecidableEq A] {I D R S : Finset A}
    (hdis : Disjoint I D) (hR : R ⊆ I) (hS : S ⊆ D) :
    (I \ R) ∪ (D \ S) = (I ∪ D) \ (R ∪ S) := by
  ext T
  have hd := disjoint_left.mp hdis
  simp only [mem_union, mem_sdiff]
  constructor
  · rintro (⟨hTI, hTR⟩ | ⟨hTD, hTS⟩)
    · exact ⟨Or.inl hTI, fun h ↦ h.elim hTR (fun hTS ↦ hd hTI (hS hTS))⟩
    · exact ⟨Or.inr hTD, fun h ↦ h.elim (fun hTR ↦ hd (hR hTR) hTD) hTS⟩
  · rintro ⟨hTI | hTD, hnot⟩
    · exact Or.inl ⟨hTI, fun hTR ↦ hnot (Or.inl hTR)⟩
    · exact Or.inr ⟨hTD, fun hTS ↦ hnot (Or.inr hTS)⟩

theorem sourceLinkTriangleWeight_factor
    {V : Type*} [DecidableEq V] (f₀ f₁ f₂ : TripleOn V → ℝ≥0)
    (H : Finset (SourceLinkTriangleCoordinate V)) :
    setWeight (sourceLinkTriangleWeight f₀ f₁ f₂) H =
      setWeight f₀ H.toLeft * (setWeight f₁ H.toRight.toLeft * setWeight f₂ H.toRight.toRight) := by
  unfold setWeight
  rw [prod_sum_eq_prod_toLeft_mul_prod_toRight,
    prod_sum_eq_prod_toLeft_mul_prod_toRight H.toRight]
  rfl

theorem SourceLinkMarking.root_remainder_base_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A : TripleSystemOn V} {x : SourceLinkMarking V}
    (hx : IsSourceLinkMarking W F e A x) (π : TripleOn V → ℝ≥0)
    {H : Finset (SourceLinkCoordinate V)} (hH : H ⊆ x.coordinates e) :
    setWeight (sourceLinkTriangleWeight π π π) (x.triangleCoordinates \ H.toLeft) =
      setWeight π (x.system \ sourceLinkUnderlyingRoot H) := by
  have hh := subset_disjSum.mp hH
  have hh₀ : H.toLeft.toLeft ⊆ x.initial ∧ H.toLeft.toRight ⊆ x.later.disjSum x.candidate :=
    subset_disjSum.mp hh.1
  have hh₁ := subset_disjSum.mp hh₀.2
  have hd₀ : Disjoint (x.initial \ H.toLeft.toLeft) (x.later \ H.toLeft.toRight.toLeft) :=
    hx.2.1.mono sdiff_subset sdiff_subset
  have hd₁ : Disjoint ((x.initial \ H.toLeft.toLeft) ∪ (x.later \ H.toLeft.toRight.toLeft))
      (x.candidate \ H.toLeft.toRight.toRight) :=
    hx.2.2.1.mono (union_subset_union sdiff_subset sdiff_subset) sdiff_subset
  have heq : ((x.initial \ H.toLeft.toLeft) ∪ (x.later \ H.toLeft.toRight.toLeft)) ∪
      (x.candidate \ H.toLeft.toRight.toRight) = x.system \ sourceLinkUnderlyingRoot H := by
    rw [disjoint_colored_sdiff_union hx.2.1 hh₀.1 hh₁.1]
    exact disjoint_colored_sdiff_union hx.2.2.1 (union_subset_union hh₀.1 hh₁.1) hh₁.2
  rw [sourceLinkTriangleWeight_factor, ← heq]
  simp only [toLeft_sdiff, toRight_sdiff, SourceLinkMarking.triangleCoordinates,
    toLeft_disjSum, toRight_disjSum, setWeight]
  rw [prod_union hd₁, prod_union hd₀, mul_assoc]

theorem SourceLinkMarking.root_remainder_card
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A : TripleSystemOn V} {x : SourceLinkMarking V}
    (hx : IsSourceLinkMarking W F e A x)
    {H : Finset (SourceLinkCoordinate V)} (hH : H ⊆ x.coordinates e) :
    (x.triangleCoordinates \ H.toLeft).card = x.system.card - (sourceLinkUnderlyingRoot H).card := by
  have hh := subset_disjSum.mp hH
  have hh₀ : H.toLeft.toLeft ⊆ x.initial ∧ H.toLeft.toRight ⊆ x.later.disjSum x.candidate :=
    subset_disjSum.mp hh.1
  have hh₁ := subset_disjSum.mp hh₀.2
  have hd₀ := hx.2.1.mono hh₀.1 hh₁.1
  have hd₁ := hx.2.2.1.mono (union_subset_union hh₀.1 hh₁.1) hh₁.2
  have hcard : H.toLeft.card = (sourceLinkUnderlyingRoot H).card := by
    unfold sourceLinkUnderlyingRoot
    rw [card_union_of_disjoint hd₁, card_union_of_disjoint hd₀,
      add_assoc, card_toLeft_add_card_toRight (u := H.toLeft.toRight),
      card_toLeft_add_card_toRight (u := H.toLeft)]
  rw [card_sdiff_of_subset hh.1, hcard]
  congr 1
  simp only [triangleCoordinates, system, card_disjSum,
    card_union_of_disjoint hx.2.2.1, card_union_of_disjoint hx.2.1, add_assoc]

theorem SourceLinkMarking.root_remainder_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A : TripleSystemOn V} {x : SourceLinkMarking V}
    (hx : IsSourceLinkMarking W F e A x)
    (f₀ f₁ f₂ π : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (w : ℝ≥0)
    (h₀ : ∀ T ∈ x.initial, f₀ T ≤ w * π T)
    (h₁ : ∀ T ∈ x.later, f₁ T ≤ w * π T)
    (h₂ : ∀ T ∈ x.candidate, f₂ T ≤ w * π T)
    (he : ∀ f, fe f ≤ 1)
    {H : Finset (SourceLinkCoordinate V)} (hH : H ⊆ x.coordinates e) :
    setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) ≤
      w ^ (x.system.card - (sourceLinkUnderlyingRoot H).card) *
        setWeight π (x.system \ sourceLinkUnderlyingRoot H) := by
  have hp : ∀ a ∈ x.triangleCoordinates,
      sourceLinkTriangleWeight f₀ f₁ f₂ a ≤ w * sourceLinkTriangleWeight π π π a := by
    intro a ha
    rcases a with T | T | T
    · exact h₀ T (by simpa only [triangleCoordinates, inl_mem_disjSum] using ha)
    · exact h₁ T (by simpa only [triangleCoordinates, inr_mem_disjSum, inl_mem_disjSum] using ha)
    · exact h₂ T (by simpa only [triangleCoordinates, inr_mem_disjSum] using ha)
  have hfactor : setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) =
      setWeight (sourceLinkTriangleWeight f₀ f₁ f₂) (x.triangleCoordinates \ H.toLeft) *
        setWeight fe (x.edgeCoordinates e \ H.toRight) := by
    unfold setWeight
    rw [prod_sum_eq_prod_toLeft_mul_prod_toRight]
    simp only [toLeft_sdiff, toRight_sdiff, coordinates, toLeft_disjSum, toRight_disjSum]
    rfl
  rw [hfactor]
  calc
    _ ≤ setWeight (sourceLinkTriangleWeight f₀ f₁ f₂) (x.triangleCoordinates \ H.toLeft) * 1 := by
      gcongr
      exact prod_le_one (fun f _ ↦ zero_le) (fun f _ ↦ he f)
    _ = setWeight (sourceLinkTriangleWeight f₀ f₁ f₂) (x.triangleCoordinates \ H.toLeft) := mul_one _
    _ ≤ setWeight (fun a ↦ w * sourceLinkTriangleWeight π π π a) (x.triangleCoordinates \ H.toLeft) :=
      prod_le_prod' (fun a ha ↦ hp a (mem_sdiff.mp ha).1)
    _ = w ^ (x.triangleCoordinates \ H.toLeft).card *
        setWeight (sourceLinkTriangleWeight π π π) (x.triangleCoordinates \ H.toLeft) := by
      simp only [setWeight, prod_mul_distrib, prod_const]
    _ = _ := by rw [SourceLinkMarking.root_remainder_card hx hH,
      SourceLinkMarking.root_remainder_base_weight hx π hH]

end

end Erdos207
