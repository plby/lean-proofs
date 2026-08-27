/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMarkingWeight

/-! # Disjoint candidate-edge blocks and the distinguished link triangle -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceLinkMarking.root_edges_disjoint_other_candidates
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x)
    (hpack : IsPackingOn x.system) :
    Disjoint (tripleEdgeFinset x.root) ((x.candidate.erase x.root).biUnion tripleEdgeFinset) := by
  apply disjoint_left.mpr
  intro f hf hother
  obtain ⟨T, hT, hfT⟩ := mem_biUnion.mp hother
  have hm := mem_erase.mp hT
  exact hm.1 (hpack.eq_of_common_graph_edge (mem_union_right _ hm.2)
    (SourceLinkMarking.root_mem_system hx) hfT hf)

theorem SourceLinkMarking.edge_coordinates_split
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x)
    (hpack : IsPackingOn x.system) :
    x.edgeCoordinates e = (tripleEdgeFinset x.root).erase e ∪
      (x.candidate.erase x.root).biUnion tripleEdgeFinset := by
  have hd := SourceLinkMarking.root_edges_disjoint_other_candidates hx hpack
  have hnot : e ∉ (x.candidate.erase x.root).biUnion tripleEdgeFinset :=
    fun he ↦ disjoint_left.mp hd hx.2.2.2.2.1 he
  change (x.candidate.biUnion tripleEdgeFinset).erase e = _
  conv_lhs => rw [← insert_erase hx.2.2.2.1]
  rw [biUnion_insert, ← sdiff_singleton_eq_erase, union_sdiff_distrib,
    sdiff_singleton_eq_erase, sdiff_singleton_eq_erase, erase_eq_of_notMem hnot]

theorem SourceLinkMarking.other_candidate_edge_product
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (_hx : IsSourceLinkMarking W F e A x)
    (hpack : IsPackingOn x.system) (fe : Sym2 V → ℝ≥0) :
    setWeight fe ((x.candidate.erase x.root).biUnion tripleEdgeFinset) =
      ∏ T ∈ x.candidate.erase x.root, setWeight fe (tripleEdgeFinset T) := by
  unfold setWeight
  apply prod_biUnion
  intro T hT D hD hTD
  exact hpack.isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset
    (mem_union_right _ (mem_erase.mp hT).2) (mem_union_right _ (mem_erase.mp hD).2) hTD

theorem SourceLinkMarking.full_coordinate_weight_factor
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x)
    (hpack : IsPackingOn x.system) (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) :
    setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e) =
      setWeight f₀ x.initial * setWeight f₁ x.later *
        (f₂ x.root * setWeight fe ((tripleEdgeFinset x.root).erase e)) *
          ∏ T ∈ x.candidate.erase x.root, f₂ T * setWeight fe (tripleEdgeFinset T) := by
  have hd : Disjoint ((tripleEdgeFinset x.root).erase e)
      ((x.candidate.erase x.root).biUnion tripleEdgeFinset) :=
    (SourceLinkMarking.root_edges_disjoint_other_candidates hx hpack).mono
      (erase_subset e _) (Subset.refl _)
  have htri : setWeight (sourceLinkTriangleWeight f₀ f₁ f₂) x.triangleCoordinates =
      setWeight f₀ x.initial * (setWeight f₁ x.later * setWeight f₂ x.candidate) := by
    rw [sourceLinkTriangleWeight_factor]
    simp only [triangleCoordinates, toLeft_disjSum, toRight_disjSum]
  have hfactor : setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e) =
      setWeight (sourceLinkTriangleWeight f₀ f₁ f₂) x.triangleCoordinates * setWeight fe (x.edgeCoordinates e) := by
    unfold setWeight coordinates sourceLinkMixedWeight
    exact prod_sumElim _ _ _ _
  have hefactor : setWeight fe (x.edgeCoordinates e) =
      setWeight fe ((tripleEdgeFinset x.root).erase e) *
        ∏ T ∈ x.candidate.erase x.root, setWeight fe (tripleEdgeFinset T) := by
    rw [SourceLinkMarking.edge_coordinates_split hx hpack]
    change (∏ f ∈ _ ∪ _, fe f) = _
    rw [prod_union hd]
    rw [← SourceLinkMarking.other_candidate_edge_product hx hpack fe]
    rfl
  rw [hfactor, htri, hefactor]
  have hc : setWeight f₂ x.candidate = f₂ x.root * ∏ T ∈ x.candidate.erase x.root, f₂ T :=
    (mul_prod_erase x.candidate f₂ hx.2.2.2.1).symm
  rw [hc, prod_mul_distrib]
  ring

theorem SourceLinkMarking.deleted_root_coordinate_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x)
    (hpack : IsPackingOn x.system) (f₀ f₁ f₂ : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0)
    (he : ∀ f, fe f ≤ 1) (H : Finset (SourceLinkCoordinate V))
    (htri : H.toLeft = {Sum.inr (Sum.inr x.root)}) (hedge : H.toRight ⊆ tripleEdgeFinset x.root) :
    setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) ≤
      setWeight f₀ x.initial * setWeight f₁ x.later *
        ∏ T ∈ x.candidate.erase x.root, f₂ T * setWeight fe (tripleEdgeFinset T) := by
  have hd := SourceLinkMarking.root_edges_disjoint_other_candidates hx hpack
  have heq : x.edgeCoordinates e \ H.toRight =
      ((tripleEdgeFinset x.root).erase e \ H.toRight) ∪
        (x.candidate.erase x.root).biUnion tripleEdgeFinset := by
    rw [SourceLinkMarking.edge_coordinates_split hx hpack, union_sdiff_distrib,
      sdiff_eq_self_of_disjoint (hd.symm.mono (Subset.refl _) hedge)]
  have hdis : Disjoint ((tripleEdgeFinset x.root).erase e \ H.toRight)
      ((x.candidate.erase x.root).biUnion tripleEdgeFinset) :=
    hd.mono (sdiff_subset.trans (erase_subset e _)) (Subset.refl _)
  have hfactor : setWeight (sourceLinkMixedWeight f₀ f₁ f₂ fe) (x.coordinates e \ H) =
      (setWeight f₀ x.initial * (setWeight f₁ x.later * setWeight f₂ (x.candidate.erase x.root))) *
        setWeight fe (x.edgeCoordinates e \ H.toRight) := by
    unfold setWeight
    rw [prod_sum_eq_prod_toLeft_mul_prod_toRight]
    simp only [toLeft_sdiff, toRight_sdiff, coordinates, toLeft_disjSum, toRight_disjSum]
    change setWeight (sourceLinkTriangleWeight f₀ f₁ f₂) (x.triangleCoordinates \ H.toLeft) * _ = _
    have hI : (x.triangleCoordinates \ H.toLeft).toLeft = x.initial := by
      ext T
      simp [triangleCoordinates, htri]
    have hD : (x.triangleCoordinates \ H.toLeft).toRight.toLeft = x.later := by
      ext T
      simp [triangleCoordinates, htri]
    have hC : (x.triangleCoordinates \ H.toLeft).toRight.toRight = x.candidate.erase x.root := by
      ext T
      simp [triangleCoordinates, htri, and_comm]
    rw [sourceLinkTriangleWeight_factor, hI, hD, hC]
    rfl
  have hedgeweight : setWeight fe (x.edgeCoordinates e \ H.toRight) ≤
      ∏ T ∈ x.candidate.erase x.root, setWeight fe (tripleEdgeFinset T) := by
    rw [heq]
    change (∏ f ∈ _ ∪ _, fe f) ≤ _
    rw [prod_union hdis]
    have hb : (∏ f ∈ (tripleEdgeFinset x.root).erase e \ H.toRight, fe f) ≤ 1 :=
      prod_le_one (fun _ _ ↦ zero_le) (fun f _ ↦ he f)
    have hh := SourceLinkMarking.other_candidate_edge_product hx hpack fe
    change _ * setWeight fe ((x.candidate.erase x.root).biUnion tripleEdgeFinset) ≤ _
    rw [hh]
    exact mul_le_of_le_one_left zero_le hb
  rw [hfactor]
  calc
    _ ≤ (setWeight f₀ x.initial * (setWeight f₁ x.later * setWeight f₂ (x.candidate.erase x.root))) *
        ∏ T ∈ x.candidate.erase x.root, setWeight fe (tripleEdgeFinset T) := by gcongr
    _ = _ := by simp only [setWeight, prod_mul_distrib]; ring

end

end Erdos207
