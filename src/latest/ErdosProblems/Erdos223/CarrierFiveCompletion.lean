/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.CarrierFive

/-!
# Full-rank completion inside a five-dimensional weak carrier

Four affinely independent points on either rank-three carrier sphere determine
that sphere.  Consequently, a point at unit distance from all four belongs to
the opposite rank-two carrier circle.  These lemmas are the sharp completion
input for controlling exceptional vertices in dimension five.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223.FiveWeakCarrier.Carrier

noncomputable section

variable (C : FiveWeakCarrier.Carrier)

private lemma norm_sub_sq_eq_add_of_orthogonal
    {u v : Point 5} (h : inner ℝ u v = 0) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  simpa [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real h

/-- Four affinely independent points on the first carrier sphere determine
that sphere. Any point at unit distance from all four lies on the opposite
carrier circle. -/
theorem mem_secondCircle_of_unit_to_firstSphere_anchor
    (a : Fin 4 → Point 5) (ha : AffineIndependent ℝ a)
    (hamem : ∀ i, a i ∈ C.firstSphere)
    (q : Point 5) (hq : ∀ i, dist q (a i) = 1) :
    q ∈ C.secondCircle := by
  let W : Submodule ℝ (Point 5) := C.secondPlane.directionᗮ
  let P : AffineSubspace ℝ (Point 5) := AffineSubspace.mk' C.secondCenter W
  have hWfin : Module.finrank ℝ W = 3 := by
    change Module.finrank ℝ C.secondPlane.directionᗮ = 3
    have h := C.secondPlane.direction.finrank_add_finrank_orthogonal
    rw [C.second_finrank] at h
    have hambient : Module.finrank ℝ (Point 5) = 5 := by simp
    rw [hambient] at h
    omega
  have haP : ∀ i, a i ∈ P := by
    intro i
    exact (hamem i).1
  have hspanle : affineSpan ℝ (Set.range a) ≤ P := by
    apply affineSpan_le.2
    rintro _ ⟨i, rfl⟩
    exact haP i
  have hspaneq : affineSpan ℝ (Set.range a) = P := by
    apply ha.affineSpan_eq_of_le_of_card_eq_finrank_add_one hspanle
    rw [show P.direction = W by simp [P], hWfin]
    norm_num
  have hdirEq : (affineSpan ℝ (Set.range a)).direction = W := by
    rw [hspaneq]
    simp [P]
  let S : Affine.Simplex ℝ (Point 5) 3 := ⟨a, ha⟩
  have hcirc : S.circumcenter = C.secondCenter := by
    symm
    apply S.eq_circumcenter_of_dist_eq (r := C.firstSphereRadius)
    · simpa [S, hspaneq, P] using (AffineSubspace.self_mem_mk' C.secondCenter W)
    · intro i
      simpa [S] using (hamem i).2
  have hproj : ↑(S.orthogonalProjectionSpan q) = C.secondCenter := by
    rw [← hcirc]
    apply S.orthogonalProjection_eq_circumcenter_of_dist_eq
    intro i
    simpa [S, dist_comm] using hq i
  have hqorth : q -ᵥ C.secondCenter ∈ Wᗮ := by
    rw [← hdirEq, ← hproj]
    change q -ᵥ ↑(S.orthogonalProjectionSpan q) ∈
      (affineSpan ℝ (Set.range S.points)).directionᗮ
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range S.points)) q
  have hqdir : q -ᵥ C.secondCenter ∈ C.secondPlane.direction := by
    change q -ᵥ C.secondCenter ∈ (C.secondPlane.directionᗮ)ᗮ at hqorth
    simpa only [Submodule.orthogonal_orthogonal] using hqorth
  have hqplane : q ∈ C.secondPlane := by
    simpa using AffineSubspace.vadd_mem_of_mem_direction hqdir C.secondCenter_mem
  have hadir : a 0 -ᵥ C.secondCenter ∈ W := (hamem 0).1
  have hi : inner ℝ (q -ᵥ C.secondCenter) (a 0 -ᵥ C.secondCenter) = 0 :=
    ((Submodule.mem_orthogonal' _ _).mp hqorth) _ hadir
  have hn := norm_sub_sq_eq_add_of_orthogonal hi
  have hsq : dist q C.secondCenter ^ 2 + C.firstSphereRadius ^ 2 = 1 := by
    calc
      dist q C.secondCenter ^ 2 + C.firstSphereRadius ^ 2 =
          ‖q -ᵥ C.secondCenter‖ ^ 2 + ‖a 0 -ᵥ C.secondCenter‖ ^ 2 := by
        rw [dist_eq_norm_vsub]
        rw [show ‖a 0 -ᵥ C.secondCenter‖ = C.firstSphereRadius by
          simpa [dist_eq_norm_vsub] using (hamem 0).2]
      _ = ‖(q -ᵥ C.secondCenter) - (a 0 -ᵥ C.secondCenter)‖ ^ 2 := hn.symm
      _ = dist q (a 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hq 0]; norm_num
  refine ⟨hqplane, ?_⟩
  nlinarith [dist_nonneg (x := q) (y := C.secondCenter), C.secondRadius_nonneg,
    C.first_cross_radius_sq]

/-- If a point is not on the second circle, any four of its unit neighbors
on the first sphere are affinely dependent. -/
theorem not_affineIndependent_unit_neighbors_firstSphere
    (a : Fin 4 → Point 5) (hamem : ∀ i, a i ∈ C.firstSphere)
    (q : Point 5) (hqnot : q ∉ C.secondCircle)
    (hq : ∀ i, dist q (a i) = 1) :
    ¬AffineIndependent ℝ a := by
  intro ha
  exact hqnot (C.mem_secondCircle_of_unit_to_firstSphere_anchor a ha hamem q hq)

/-- The unit-neighbor set of a point outside the second circle has affine
dimension at most two inside the first sphere. -/
theorem unitNeighbors_firstSphere_finrank_le_two
    (B : Finset (Point 5)) (hB : ∀ x ∈ B, x ∈ C.firstSphere)
    (q : Point 5) (hqnot : q ∉ C.secondCircle)
    (hq : ∀ x ∈ B, dist q x = 1) :
    Module.finrank ℝ (affineSpan ℝ (B : Set (Point 5))).direction ≤ 2 := by
  classical
  rw [direction_affineSpan]
  by_contra hle
  have hge : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (B : Set (Point 5))) := by omega
  obtain ⟨t, htB, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point 5) (B : Set (Point 5))
  letI : Finite t := (B.finite_toSet.subset htB).to_subtype
  letI : Fintype t := Fintype.ofFinite t
  have hvec : vectorSpan ℝ t = vectorSpan ℝ (B : Set (Point 5)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, hspan]
  have hgeT : 3 ≤ Module.finrank ℝ (vectorSpan ℝ t) := by rwa [hvec]
  have htne : t.Nonempty := by
    by_contra h
    have he : t = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, vectorSpan_empty] at hgeT
    simp at hgeT
  letI : Nonempty t := htne.to_subtype
  have hcardEq : Module.finrank ℝ (vectorSpan ℝ t) + 1 = Fintype.card t := by
    have h := htAI.finrank_vectorSpan_add_one
    have hrange : Set.range (Subtype.val : t → Point 5) = t := Subtype.range_val
    rw [hrange] at h
    exact h
  have hcard : 4 ≤ Fintype.card t := by omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 4) ≤ Fintype.card t by simpa using hcard)
  let a : Fin 4 → Point 5 := fun i ↦ (e i : Point 5)
  have ha : AffineIndependent ℝ a := htAI.comp_embedding e
  have hamem : ∀ i, a i ∈ C.firstSphere := by
    intro i
    exact hB (e i) (htB (e i).property)
  have hqa : ∀ i, dist q (a i) = 1 := by
    intro i
    exact hq (e i) (htB (e i).property)
  exact hqnot (C.mem_secondCircle_of_unit_to_firstSphere_anchor a ha hamem q hqa)

/-- The symmetric full-rank completion lemma for the second carrier sphere. -/
theorem mem_firstCircle_of_unit_to_secondSphere_anchor
    (b : Fin 4 → Point 5) (hb : AffineIndependent ℝ b)
    (hbmem : ∀ i, b i ∈ C.secondSphere)
    (q : Point 5) (hq : ∀ i, dist q (b i) = 1) :
    q ∈ C.firstCircle := by
  let W : Submodule ℝ (Point 5) := C.firstPlane.directionᗮ
  let P : AffineSubspace ℝ (Point 5) := AffineSubspace.mk' C.firstCenter W
  have hWfin : Module.finrank ℝ W = 3 := by
    change Module.finrank ℝ C.firstPlane.directionᗮ = 3
    have h := C.firstPlane.direction.finrank_add_finrank_orthogonal
    rw [C.first_finrank] at h
    have hambient : Module.finrank ℝ (Point 5) = 5 := by simp
    rw [hambient] at h
    omega
  have hbP : ∀ i, b i ∈ P := by
    intro i
    exact (hbmem i).1
  have hspanle : affineSpan ℝ (Set.range b) ≤ P := by
    apply affineSpan_le.2
    rintro _ ⟨i, rfl⟩
    exact hbP i
  have hspaneq : affineSpan ℝ (Set.range b) = P := by
    apply hb.affineSpan_eq_of_le_of_card_eq_finrank_add_one hspanle
    rw [show P.direction = W by simp [P], hWfin]
    norm_num
  have hdirEq : (affineSpan ℝ (Set.range b)).direction = W := by
    rw [hspaneq]
    simp [P]
  let S : Affine.Simplex ℝ (Point 5) 3 := ⟨b, hb⟩
  have hcirc : S.circumcenter = C.firstCenter := by
    symm
    apply S.eq_circumcenter_of_dist_eq (r := C.secondSphereRadius)
    · simpa [S, hspaneq, P] using (AffineSubspace.self_mem_mk' C.firstCenter W)
    · intro i
      simpa [S] using (hbmem i).2
  have hproj : ↑(S.orthogonalProjectionSpan q) = C.firstCenter := by
    rw [← hcirc]
    apply S.orthogonalProjection_eq_circumcenter_of_dist_eq
    intro i
    simpa [S, dist_comm] using hq i
  have hqorth : q -ᵥ C.firstCenter ∈ Wᗮ := by
    rw [← hdirEq, ← hproj]
    change q -ᵥ ↑(S.orthogonalProjectionSpan q) ∈
      (affineSpan ℝ (Set.range S.points)).directionᗮ
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range S.points)) q
  have hqdir : q -ᵥ C.firstCenter ∈ C.firstPlane.direction := by
    change q -ᵥ C.firstCenter ∈ (C.firstPlane.directionᗮ)ᗮ at hqorth
    simpa only [Submodule.orthogonal_orthogonal] using hqorth
  have hqplane : q ∈ C.firstPlane := by
    simpa using AffineSubspace.vadd_mem_of_mem_direction hqdir C.firstCenter_mem
  have hbdir : b 0 -ᵥ C.firstCenter ∈ W := (hbmem 0).1
  have hi : inner ℝ (q -ᵥ C.firstCenter) (b 0 -ᵥ C.firstCenter) = 0 :=
    ((Submodule.mem_orthogonal' _ _).mp hqorth) _ hbdir
  have hn := norm_sub_sq_eq_add_of_orthogonal hi
  have hsq : dist q C.firstCenter ^ 2 + C.secondSphereRadius ^ 2 = 1 := by
    calc
      dist q C.firstCenter ^ 2 + C.secondSphereRadius ^ 2 =
          ‖q -ᵥ C.firstCenter‖ ^ 2 + ‖b 0 -ᵥ C.firstCenter‖ ^ 2 := by
        rw [dist_eq_norm_vsub]
        rw [show ‖b 0 -ᵥ C.firstCenter‖ = C.secondSphereRadius by
          simpa [dist_eq_norm_vsub] using (hbmem 0).2]
      _ = ‖(q -ᵥ C.firstCenter) - (b 0 -ᵥ C.firstCenter)‖ ^ 2 := hn.symm
      _ = dist q (b 0) ^ 2 := by
        rw [dist_eq_norm_vsub]
        congr 2
        simp [vsub_eq_sub]
      _ = 1 := by rw [hq 0]; norm_num
  refine ⟨hqplane, ?_⟩
  nlinarith [dist_nonneg (x := q) (y := C.firstCenter), C.firstRadius_nonneg,
    C.second_cross_radius_sq]

/-- If a point is not on the first circle, any four of its unit neighbors
on the second sphere are affinely dependent. -/
theorem not_affineIndependent_unit_neighbors_secondSphere
    (b : Fin 4 → Point 5) (hbmem : ∀ i, b i ∈ C.secondSphere)
    (q : Point 5) (hqnot : q ∉ C.firstCircle)
    (hq : ∀ i, dist q (b i) = 1) :
    ¬AffineIndependent ℝ b := by
  intro hb
  exact hqnot (C.mem_firstCircle_of_unit_to_secondSphere_anchor b hb hbmem q hq)

/-- The symmetric affine-rank bound for unit neighbors on the second sphere. -/
theorem unitNeighbors_secondSphere_finrank_le_two
    (B : Finset (Point 5)) (hB : ∀ x ∈ B, x ∈ C.secondSphere)
    (q : Point 5) (hqnot : q ∉ C.firstCircle)
    (hq : ∀ x ∈ B, dist q x = 1) :
    Module.finrank ℝ (affineSpan ℝ (B : Set (Point 5))).direction ≤ 2 := by
  classical
  rw [direction_affineSpan]
  by_contra hle
  have hge : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (B : Set (Point 5))) := by omega
  obtain ⟨t, htB, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point 5) (B : Set (Point 5))
  letI : Finite t := (B.finite_toSet.subset htB).to_subtype
  letI : Fintype t := Fintype.ofFinite t
  have hvec : vectorSpan ℝ t = vectorSpan ℝ (B : Set (Point 5)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, hspan]
  have hgeT : 3 ≤ Module.finrank ℝ (vectorSpan ℝ t) := by rwa [hvec]
  have htne : t.Nonempty := by
    by_contra h
    have he : t = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, vectorSpan_empty] at hgeT
    simp at hgeT
  letI : Nonempty t := htne.to_subtype
  have hcardEq : Module.finrank ℝ (vectorSpan ℝ t) + 1 = Fintype.card t := by
    have h := htAI.finrank_vectorSpan_add_one
    have hrange : Set.range (Subtype.val : t → Point 5) = t := Subtype.range_val
    rw [hrange] at h
    exact h
  have hcard : 4 ≤ Fintype.card t := by omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 4) ≤ Fintype.card t by simpa using hcard)
  let b : Fin 4 → Point 5 := fun i ↦ (e i : Point 5)
  have hb : AffineIndependent ℝ b := htAI.comp_embedding e
  have hbmem : ∀ i, b i ∈ C.secondSphere := by
    intro i
    exact hB (e i) (htB (e i).property)
  have hqb : ∀ i, dist q (b i) = 1 := by
    intro i
    exact hq (e i) (htB (e i).property)
  exact hqnot (C.mem_firstCircle_of_unit_to_secondSphere_anchor b hb hbmem q hqb)

end

end Erdos223.FiveWeakCarrier.Carrier
