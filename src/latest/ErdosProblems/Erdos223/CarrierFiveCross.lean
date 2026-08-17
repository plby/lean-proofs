/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.CarrierFive
import ErdosProblems.Erdos223.DiameterUnionDecomp

/-!
# Cross pairs in a five-dimensional weak carrier

This file proves the exact obstruction behind the cross-edge defect in a
shifted weak five-dimensional Lenz carrier.  A unit pair between the two
crossed spheres must have one endpoint on the corresponding core circle.
-/

open scoped RealInnerProductSpace

namespace Erdos223.FiveWeakCarrier

noncomputable section

/-- In a five-dimensional inner-product space, two rank-two orthogonal
subspaces cannot both be enlarged by orthogonal new directions. -/
private theorem mem_or_mem_of_complementary_rank_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 5)
    (U V : Submodule ℝ E)
    (hU : Module.finrank ℝ U = 2) (hV : Module.finrank ℝ V = 2)
    (hUV : U ⟂ V)
    {u v : E} (huV : u ∈ Vᗮ) (hvU : v ∈ Uᗮ)
    (huv : inner ℝ u v = 0) :
    u ∈ U ∨ v ∈ V := by
  by_contra hn
  have h : u ∉ U ∧ v ∉ V := not_or.mp hn
  let W : Submodule ℝ E := U ⊔ ℝ ∙ u
  let Z : Submodule ℝ E := V ⊔ ℝ ∙ v
  have hUspanv : U ⟂ ℝ ∙ v := by
    rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le]
    exact Submodule.span_le.2 (by simpa using hvU)
  have hspanuV : ℝ ∙ u ⟂ V := by
    rw [Submodule.isOrtho_iff_le]
    exact Submodule.span_le.2 (by simpa using huV)
  have hspan : ℝ ∙ u ⟂ ℝ ∙ v := by
    rw [Submodule.isOrtho_span]
    simpa using huv
  have hWZ : W ⟂ Z := by
    simp only [W, Z, Submodule.isOrtho_sup_left, Submodule.isOrtho_sup_right]
    exact ⟨⟨hUV, hspanuV⟩, hUspanv, hspan⟩
  have hW : Module.finrank ℝ W = 3 := by
    dsimp [W]
    rw [Submodule.finrank_sup_span_singleton h.1, hU]
  have hZ : Module.finrank ℝ Z = 3 := by
    dsimp [Z]
    rw [Submodule.finrank_sup_span_singleton h.2, hV]
  have hsum := W.finrank_sup_add_finrank_inf_eq Z
  have hinf : W ⊓ Z = ⊥ := hWZ.disjoint.eq_bot
  rw [hinf, hW, hZ] at hsum
  simp at hsum
  have hle : Module.finrank ℝ ↥(W ⊔ Z) ≤
      Module.finrank ℝ ↥(⊤ : Submodule ℝ E) :=
    Submodule.finrank_mono le_top
  rw [hsum, finrank_top, hE] at hle
  omega

namespace Carrier

variable (C : Carrier)

/-- A unit pair between the two crossed spheres has an endpoint on one of
the two core circles. -/
theorem mem_firstCircle_or_mem_secondCircle_of_mem_spheres_of_dist_eq_one
    {x y : Point 5} (hx : x ∈ C.firstSphere) (hy : y ∈ C.secondSphere)
    (hxy : dist x y = 1) :
    x ∈ C.firstCircle ∨ y ∈ C.secondCircle := by
  let U := C.firstPlane.direction
  let V := C.secondPlane.direction
  let u : Point 5 := x -ᵥ C.firstCenter
  let v : Point 5 := y -ᵥ C.secondCenter
  let h : Point 5 := C.secondCenter -ᵥ C.firstCenter
  have huV : u ∈ Vᗮ := by
    have hc : C.secondCenter -ᵥ C.firstCenter ∈ Vᗮ := by
      simpa only [neg_vsub_eq_vsub_rev] using
        Vᗮ.neg_mem C.center_vsub_mem_second_orthogonal
    rw [show u = (x -ᵥ C.secondCenter) +
        (C.secondCenter -ᵥ C.firstCenter) by
      exact (vsub_add_vsub_cancel x C.secondCenter C.firstCenter).symm]
    exact Vᗮ.add_mem hx.1 hc
  have hvU : v ∈ Uᗮ := by
    have hc : C.firstCenter -ᵥ C.secondCenter ∈ Uᗮ := by
      simpa only [neg_vsub_eq_vsub_rev] using
        Uᗮ.neg_mem C.center_vsub_mem_first_orthogonal
    rw [show v = (y -ᵥ C.firstCenter) +
        (C.firstCenter -ᵥ C.secondCenter) by
      exact (vsub_add_vsub_cancel y C.firstCenter C.secondCenter).symm]
    exact Uᗮ.add_mem hy.1 hc
  have hs1 : ‖u - h‖ ^ 2 = C.firstSphereRadius ^ 2 := by
    rw [show u - h = x -ᵥ C.secondCenter by
      simp only [u, h, vsub_eq_sub]
      abel]
    simpa [dist_eq_norm_vsub] using congrArg (fun z : ℝ => z ^ 2) hx.2
  have hs2 : ‖v + h‖ ^ 2 = C.secondSphereRadius ^ 2 := by
    rw [show v + h = y -ᵥ C.firstCenter by
      simp only [v, h, vsub_eq_sub]
      abel]
    simpa [dist_eq_norm_vsub] using congrArg (fun z : ℝ => z ^ 2) hy.2
  have hd : ‖(u - v) - h‖ ^ 2 = 1 := by
    rw [show (u - v) - h = x -ᵥ y by
      simp only [u, v, h, vsub_eq_sub]
      abel]
    calc
      ‖x -ᵥ y‖ ^ 2 = dist x y ^ 2 := by rw [dist_eq_norm_vsub]
      _ = 1 := by rw [hxy]; norm_num
  have hh : ‖h‖ ^ 2 = dist C.firstCenter C.secondCenter ^ 2 := by
    dsimp [h]
    rw [norm_sub_rev, ← dist_eq_norm]
  have huv : inner ℝ u v = 0 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_left] at hd
    rw [norm_sub_sq_real] at hs1
    rw [norm_add_sq_real] at hs2
    rw [hh] at hd hs1 hs2
    nlinarith [C.firstSphereRadius_sq, C.secondSphereRadius_sq,
      C.first_cross_radius_sq]
  rcases mem_or_mem_of_complementary_rank_two (by simp) U V
      C.first_finrank C.second_finrank C.direction_isOrtho huV hvU huv with
    hu | hv
  · left
    refine ⟨?_, ?_⟩
    · exact
        (AffineSubspace.vsub_right_mem_direction_iff_mem C.firstCenter_mem x).mp hu
    · have hs1' := hs1
      rw [norm_sub_sq_real, hh] at hs1'
      have huh : inner ℝ u h = 0 := by
        rw [real_inner_comm]
        exact ((Submodule.mem_orthogonal' _ _).mp
          C.center_vsub_mem_first_orthogonal) _ hu
      rw [huh, C.firstSphereRadius_sq] at hs1'
      have hunonneg : 0 ≤ ‖u‖ := norm_nonneg _
      change ‖u‖ = C.firstRadius
      nlinarith [C.firstRadius_nonneg]
  · right
    refine ⟨?_, ?_⟩
    · exact
        (AffineSubspace.vsub_right_mem_direction_iff_mem C.secondCenter_mem y).mp hv
    · have hs2' := hs2
      rw [norm_add_sq_real, hh] at hs2'
      have hvh : inner ℝ v h = 0 := by
        have hhV : h ∈ Vᗮ := by
          simpa only [h, neg_vsub_eq_vsub_rev] using
            Vᗮ.neg_mem C.center_vsub_mem_second_orthogonal
        rw [real_inner_comm]
        exact ((Submodule.mem_orthogonal' _ _).mp hhV) _ hv
      rw [hvh, C.secondSphereRadius_sq] at hs2'
      have hvnonneg : 0 ≤ ‖v‖ := norm_nonneg _
      change ‖v‖ = C.secondRadius
      nlinarith [C.secondRadius_nonneg]

/-- Exact characterization of unit pairs between the crossed spheres. -/
theorem dist_eq_one_iff_mem_firstCircle_or_mem_secondCircle
    {x y : Point 5} (hx : x ∈ C.firstSphere) (hy : y ∈ C.secondSphere) :
    dist x y = 1 ↔ x ∈ C.firstCircle ∨ y ∈ C.secondCircle := by
  constructor
  · exact C.mem_firstCircle_or_mem_secondCircle_of_mem_spheres_of_dist_eq_one hx hy
  · rintro (hxCircle | hyCircle)
    · exact C.dist_eq_one_of_mem_firstCircle_mem_secondSphere hxCircle hy
    · exact C.dist_eq_one_of_mem_firstSphere_mem_secondCircle hx hyCircle

/-- Points of a first-sphere block which are off its core circle. -/
def firstOffCircle (S : Finset (Point 5)) : Finset (Point 5) := by
  classical
  exact S.filter fun x => x ∉ C.firstCircle

/-- Points of a second-sphere block which are off its core circle. -/
def secondOffCircle (T : Finset (Point 5)) : Finset (Point 5) := by
  classical
  exact T.filter fun y => y ∉ C.secondCircle

@[simp] theorem mem_firstOffCircle {S : Finset (Point 5)} {x : Point 5} :
    x ∈ C.firstOffCircle S ↔ x ∈ S ∧ x ∉ C.firstCircle := by
  simp [firstOffCircle]

@[simp] theorem mem_secondOffCircle {T : Finset (Point 5)} {y : Point 5} :
    y ∈ C.secondOffCircle T ↔ y ∈ T ∧ y ∉ C.secondCircle := by
  simp [secondOffCircle]

/-- Exact cross-edge accounting: the missing cross pairs are precisely the
products of the two off-circle sets. -/
theorem crossDiameterCount_add_offProduct
    (S T : Finset (Point 5))
    (hS : ∀ x ∈ S, x ∈ C.firstSphere)
    (hT : ∀ y ∈ T, y ∈ C.secondSphere) :
    ((S.product T).filter fun e => dist e.1 e.2 = 1).card +
      (C.firstOffCircle S).card * (C.secondOffCircle T).card =
        S.card * T.card := by
  classical
  let P : Point 5 × Point 5 → Prop := fun e => dist e.1 e.2 = 1
  have hnot (e : Point 5 × Point 5) (he : e ∈ S.product T) :
      ¬ P e ↔ e.1 ∉ C.firstCircle ∧ e.2 ∉ C.secondCircle := by
    have heST := Finset.mem_product.mp he
    have hx := hS e.1 heST.1
    have hy := hT e.2 heST.2
    simpa only [P, not_or] using
      not_congr (C.dist_eq_one_iff_mem_firstCircle_or_mem_secondCircle hx hy)
  have hoff : ((S.product T).filter fun e => ¬ P e).card =
      (C.firstOffCircle S).card * (C.secondOffCircle T).card := by
    have heq : (S.product T).filter (fun e => ¬ P e) =
        (S.product T).filter
          (fun e => e.1 ∉ C.firstCircle ∧ e.2 ∉ C.secondCircle) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hn⟩
        exact ⟨he, (hnot e he).mp hn⟩
      · rintro ⟨he, hn⟩
        exact ⟨he, (hnot e he).mpr hn⟩
    rw [heq]
    have hprod := Finset.filter_product (s := S) (t := T)
      (fun x => x ∉ C.firstCircle) (fun y => y ∉ C.secondCircle)
    have hcard := congrArg Finset.card hprod
    simpa [firstOffCircle, secondOffCircle, Finset.card_product] using hcard
  have hsplit := Finset.card_filter_add_card_filter_not (s := S.product T) P
  rw [hoff] at hsplit
  calc
    ((S.product T).filter fun e => dist e.1 e.2 = 1).card +
        (C.firstOffCircle S).card * (C.secondOffCircle T).card =
        (S.product T).card := by simpa only [P] using hsplit
    _ = S.card * T.card := Finset.card_product S T

/-- Exact total-edge accounting for two disjoint blocks on the crossed
spheres. -/
theorem diameterPairCount_union_add_offProduct
    (S T : Finset (Point 5)) (hdisj : Disjoint S T)
    (hS : ∀ x ∈ S, x ∈ C.firstSphere)
    (hT : ∀ y ∈ T, y ∈ C.secondSphere) :
    diameterPairCount (S ∪ T) +
        (C.firstOffCircle S).card * (C.secondOffCircle T).card =
      diameterPairCount S + S.card * T.card + diameterPairCount T := by
  rw [diameterPairCount_union_of_disjoint S T hdisj]
  have hcross := C.crossDiameterCount_add_offProduct S T hS hT
  omega

end Carrier

end

end Erdos223.FiveWeakCarrier
