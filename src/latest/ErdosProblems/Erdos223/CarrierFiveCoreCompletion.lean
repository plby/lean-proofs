/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.CarrierFive

/-!
# Three-point completion on the core circles

Three distinct points of a core circle are affinely independent and determine
the corresponding crossed sphere.  Consequently, a point outside that sphere
has at most two unit neighbors on the core circle.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223.FiveWeakCarrier.Carrier

noncomputable section

variable (C : FiveWeakCarrier.Carrier)

private lemma norm_sub_sq_eq_add_of_orthogonal_core
    {u v : Point 5} (h : inner ℝ u v = 0) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real h

/-- Three independent unit neighbors on the second core circle determine the
first crossed sphere. -/
theorem mem_firstSphere_of_unit_to_secondCircle_triple
    (b : Fin 3 → Point 5) (hb : AffineIndependent ℝ b)
    (hbmem : ∀ i, b i ∈ C.secondCircle)
    (q : Point 5) (hq : ∀ i, dist q (b i) = 1) :
    q ∈ C.firstSphere := by
  let S : Affine.Simplex ℝ (Point 5) 2 := ⟨b, hb⟩
  have hspanle : affineSpan ℝ (Set.range b) ≤ C.secondPlane := by
    apply affineSpan_le.2
    rintro _ ⟨i, rfl⟩
    exact (hbmem i).1
  have hspaneq : affineSpan ℝ (Set.range b) = C.secondPlane := by
    apply hb.affineSpan_eq_of_le_of_card_eq_finrank_add_one hspanle
    rw [C.second_finrank]
    norm_num
  have hdirEq : (affineSpan ℝ (Set.range b)).direction =
      C.secondPlane.direction := by
    rw [hspaneq]
  have hcirc : S.circumcenter = C.secondCenter := by
    symm
    apply S.eq_circumcenter_of_dist_eq (r := C.secondRadius)
    · simpa [S, hspaneq] using C.secondCenter_mem
    · intro i
      simpa [S] using (hbmem i).2
  have hproj : ↑(S.orthogonalProjectionSpan q) = C.secondCenter := by
    rw [← hcirc]
    apply S.orthogonalProjection_eq_circumcenter_of_dist_eq
    intro i
    simpa [S, dist_comm] using hq i
  have hqorth : q -ᵥ C.secondCenter ∈ C.secondPlane.directionᗮ := by
    rw [← hdirEq, ← hproj]
    change q -ᵥ ↑(S.orthogonalProjectionSpan q) ∈
      (affineSpan ℝ (Set.range S.points)).directionᗮ
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range S.points)) q
  refine ⟨hqorth, ?_⟩
  have hbdir : b 0 -ᵥ C.secondCenter ∈ C.secondPlane.direction :=
    AffineSubspace.vsub_mem_direction (hbmem 0).1 C.secondCenter_mem
  have hi : inner ℝ (q -ᵥ C.secondCenter) (b 0 -ᵥ C.secondCenter) = 0 :=
    ((Submodule.mem_orthogonal' _ _).mp hqorth) _ hbdir
  have hn := norm_sub_sq_eq_add_of_orthogonal_core hi
  have hsq : dist q C.secondCenter ^ 2 + C.secondRadius ^ 2 = 1 := by
    calc
      dist q C.secondCenter ^ 2 + C.secondRadius ^ 2 =
          ‖q -ᵥ C.secondCenter‖ ^ 2 + ‖b 0 -ᵥ C.secondCenter‖ ^ 2 := by
        rw [dist_eq_norm_vsub]
        rw [show ‖b 0 -ᵥ C.secondCenter‖ = C.secondRadius by
          simpa [dist_eq_norm_vsub] using (hbmem 0).2]
      _ = ‖(q -ᵥ C.secondCenter) - (b 0 -ᵥ C.secondCenter)‖ ^ 2 := hn.symm
      _ = dist q (b 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hq 0]; norm_num
  have hr : dist q C.secondCenter ^ 2 = C.firstSphereRadius ^ 2 := by
    nlinarith [C.first_cross_radius_sq]
  nlinarith [dist_nonneg (x := q) (y := C.secondCenter),
    C.firstSphereRadius_nonneg]

/-- A point outside the first crossed sphere has at most two unit neighbors
on the second core circle. -/
theorem card_unitNeighbors_secondCircle_le_two
    (T : Finset (Point 5)) (hT : ∀ y ∈ T, y ∈ C.secondCircle)
    (q : Point 5) (hq : q ∉ C.firstSphere) :
    (T.filter fun y => dist q y = 1).card ≤ 2 := by
  classical
  let N := T.filter fun y => dist q y = 1
  by_contra hn
  have hn' : ¬N.card ≤ 2 := by simpa [N] using hn
  have hthree : 3 ≤ N.card := by omega
  obtain ⟨B, hBN, hBcard⟩ := Finset.exists_subset_card_eq hthree
  let e : B ≃ Fin 3 := Finset.equivFinOfCardEq hBcard
  let b : Fin 3 → Point 5 := fun i => (e.symm i).1
  have hbinj : Function.Injective b := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    exact hij
  have hbmem : ∀ i, b i ∈ C.secondCircle := by
    intro i
    have hiB : (e.symm i).1 ∈ B := (e.symm i).2
    have hiN : (e.symm i).1 ∈ N := hBN hiB
    exact hT _ (Finset.mem_filter.mp hiN).1
  have hcos : EuclideanGeometry.Cospherical C.secondCircle := by
    exact ⟨C.secondCenter, C.secondRadius, fun y hy => hy.2⟩
  have hbAI : AffineIndependent ℝ b := by
    apply hcos.affineIndependent
    · rintro _ ⟨i, rfl⟩
      exact hbmem i
    · exact hbinj
  apply hq
  apply C.mem_firstSphere_of_unit_to_secondCircle_triple b hbAI hbmem q
  intro i
  have hiN : (e.symm i).1 ∈ N := hBN (e.symm i).2
  exact (Finset.mem_filter.mp hiN).2

/-- Three independent unit neighbors on the first core circle determine the
second crossed sphere. -/
theorem mem_secondSphere_of_unit_to_firstCircle_triple
    (a : Fin 3 → Point 5) (ha : AffineIndependent ℝ a)
    (hamem : ∀ i, a i ∈ C.firstCircle)
    (q : Point 5) (hq : ∀ i, dist q (a i) = 1) :
    q ∈ C.secondSphere := by
  let S : Affine.Simplex ℝ (Point 5) 2 := ⟨a, ha⟩
  have hspanle : affineSpan ℝ (Set.range a) ≤ C.firstPlane := by
    apply affineSpan_le.2
    rintro _ ⟨i, rfl⟩
    exact (hamem i).1
  have hspaneq : affineSpan ℝ (Set.range a) = C.firstPlane := by
    apply ha.affineSpan_eq_of_le_of_card_eq_finrank_add_one hspanle
    rw [C.first_finrank]
    norm_num
  have hdirEq : (affineSpan ℝ (Set.range a)).direction =
      C.firstPlane.direction := by
    rw [hspaneq]
  have hcirc : S.circumcenter = C.firstCenter := by
    symm
    apply S.eq_circumcenter_of_dist_eq (r := C.firstRadius)
    · simpa [S, hspaneq] using C.firstCenter_mem
    · intro i
      simpa [S] using (hamem i).2
  have hproj : ↑(S.orthogonalProjectionSpan q) = C.firstCenter := by
    rw [← hcirc]
    apply S.orthogonalProjection_eq_circumcenter_of_dist_eq
    intro i
    simpa [S, dist_comm] using hq i
  have hqorth : q -ᵥ C.firstCenter ∈ C.firstPlane.directionᗮ := by
    rw [← hdirEq, ← hproj]
    change q -ᵥ ↑(S.orthogonalProjectionSpan q) ∈
      (affineSpan ℝ (Set.range S.points)).directionᗮ
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range S.points)) q
  refine ⟨hqorth, ?_⟩
  have hadir : a 0 -ᵥ C.firstCenter ∈ C.firstPlane.direction :=
    AffineSubspace.vsub_mem_direction (hamem 0).1 C.firstCenter_mem
  have hi : inner ℝ (q -ᵥ C.firstCenter) (a 0 -ᵥ C.firstCenter) = 0 :=
    ((Submodule.mem_orthogonal' _ _).mp hqorth) _ hadir
  have hn := norm_sub_sq_eq_add_of_orthogonal_core hi
  have hsq : dist q C.firstCenter ^ 2 + C.firstRadius ^ 2 = 1 := by
    calc
      dist q C.firstCenter ^ 2 + C.firstRadius ^ 2 =
          ‖q -ᵥ C.firstCenter‖ ^ 2 + ‖a 0 -ᵥ C.firstCenter‖ ^ 2 := by
        rw [dist_eq_norm_vsub]
        rw [show ‖a 0 -ᵥ C.firstCenter‖ = C.firstRadius by
          simpa [dist_eq_norm_vsub] using (hamem 0).2]
      _ = ‖(q -ᵥ C.firstCenter) - (a 0 -ᵥ C.firstCenter)‖ ^ 2 := hn.symm
      _ = dist q (a 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hq 0]; norm_num
  have hr : dist q C.firstCenter ^ 2 = C.secondSphereRadius ^ 2 := by
    nlinarith [C.second_cross_radius_sq]
  nlinarith [dist_nonneg (x := q) (y := C.firstCenter),
    C.secondSphereRadius_nonneg]

/-- A point outside the second crossed sphere has at most two unit neighbors
on the first core circle. -/
theorem card_unitNeighbors_firstCircle_le_two
    (T : Finset (Point 5)) (hT : ∀ x ∈ T, x ∈ C.firstCircle)
    (q : Point 5) (hq : q ∉ C.secondSphere) :
    (T.filter fun x => dist q x = 1).card ≤ 2 := by
  classical
  let N := T.filter fun x => dist q x = 1
  by_contra hn
  have hn' : ¬N.card ≤ 2 := by simpa [N] using hn
  have hthree : 3 ≤ N.card := by omega
  obtain ⟨B, hBN, hBcard⟩ := Finset.exists_subset_card_eq hthree
  let e : B ≃ Fin 3 := Finset.equivFinOfCardEq hBcard
  let a : Fin 3 → Point 5 := fun i => (e.symm i).1
  have hainj : Function.Injective a := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    exact hij
  have hamem : ∀ i, a i ∈ C.firstCircle := by
    intro i
    have hiB : (e.symm i).1 ∈ B := (e.symm i).2
    have hiN : (e.symm i).1 ∈ N := hBN hiB
    exact hT _ (Finset.mem_filter.mp hiN).1
  have hcos : EuclideanGeometry.Cospherical C.firstCircle := by
    exact ⟨C.firstCenter, C.firstRadius, fun x hx => hx.2⟩
  have haAI : AffineIndependent ℝ a := by
    apply hcos.affineIndependent
    · rintro _ ⟨i, rfl⟩
      exact hamem i
    · exact hainj
  apply hq
  apply C.mem_secondSphere_of_unit_to_firstCircle_triple a haAI hamem q
  intro i
  have hiN : (e.symm i).1 ∈ N := hBN (e.symm i).2
  exact (Finset.mem_filter.mp hiN).2

/-- Summed form of `card_unitNeighbors_secondCircle_le_two`: an exceptional
set outside the first sphere contributes at most two unit pairs per point to
a block on the second core circle. -/
theorem crossDiameterCount_exception_secondCircle_le
    (E T : Finset (Point 5))
    (hT : ∀ y ∈ T, y ∈ C.secondCircle)
    (hE : ∀ q ∈ E, q ∉ C.firstSphere) :
    ((E.product T).filter fun e => dist e.1 e.2 = 1).card ≤
      2 * E.card := by
  classical
  have heq : ((E.product T).filter fun e => dist e.1 e.2 = 1).card =
      ∑ q ∈ E, (T.filter fun y => dist q y = 1).card := by
    calc
      ((E.product T).filter fun e => dist e.1 e.2 = 1).card =
          ∑ a ∈ E.product T, if dist a.1 a.2 = 1 then 1 else 0 := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ q ∈ E, ∑ y ∈ T, if dist q y = 1 then 1 else 0 := by
            exact Finset.sum_product E T
              (fun a : Point 5 × Point 5 => if dist a.1 a.2 = 1 then 1 else 0)
      _ = ∑ q ∈ E, (T.filter fun y => dist q y = 1).card := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [heq]
  calc
    (∑ q ∈ E, (T.filter fun y => dist q y = 1).card) ≤
        ∑ _q ∈ E, 2 := Finset.sum_le_sum fun q hq =>
          C.card_unitNeighbors_secondCircle_le_two T hT q (hE q hq)
    _ = 2 * E.card := by simp [mul_comm]

/-- Symmetric summed exceptional-to-core-circle bound. -/
theorem crossDiameterCount_exception_firstCircle_le
    (E T : Finset (Point 5))
    (hT : ∀ x ∈ T, x ∈ C.firstCircle)
    (hE : ∀ q ∈ E, q ∉ C.secondSphere) :
    ((E.product T).filter fun e => dist e.1 e.2 = 1).card ≤
      2 * E.card := by
  classical
  have heq : ((E.product T).filter fun e => dist e.1 e.2 = 1).card =
      ∑ q ∈ E, (T.filter fun x => dist q x = 1).card := by
    calc
      ((E.product T).filter fun e => dist e.1 e.2 = 1).card =
          ∑ a ∈ E.product T, if dist a.1 a.2 = 1 then 1 else 0 := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ q ∈ E, ∑ x ∈ T, if dist q x = 1 then 1 else 0 := by
            exact Finset.sum_product E T
              (fun a : Point 5 × Point 5 => if dist a.1 a.2 = 1 then 1 else 0)
      _ = ∑ q ∈ E, (T.filter fun x => dist q x = 1).card := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [heq]
  calc
    (∑ q ∈ E, (T.filter fun x => dist q x = 1).card) ≤
        ∑ _q ∈ E, 2 := Finset.sum_le_sum fun q hq =>
          C.card_unitNeighbors_firstCircle_le_two T hT q (hE q hq)
    _ = 2 * E.card := by simp [mul_comm]

end

end Erdos223.FiveWeakCarrier.Carrier
