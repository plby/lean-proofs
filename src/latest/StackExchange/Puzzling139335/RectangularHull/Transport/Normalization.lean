import StackExchange.Puzzling139335.RectangularHull.Frames

/-!
# Affine normalization of a rectangle

The two nonzero orthogonal edges of a frame form a basis of the plane.
Their basis equivalence, followed by translation to the origin of the
frame, gives a continuous affine equivalence taking the unit square onto
the filled rectangle.
-/

open Module Set

namespace Puzzling139335.RectangularHull

noncomputable section

lemma Frame.edges_linearIndependent (R : Frame) :
    LinearIndependent ℝ ![R.first, R.second] := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro i
    fin_cases i
    · exact R.first_ne_zero
    · exact R.second_ne_zero
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact R.orthogonal
    · change inner ℝ R.second R.first = 0
      rw [real_inner_comm]
      exact R.orthogonal
    · exact (hij rfl).elim

/-- The frame edges form a basis of the Euclidean plane. -/
def Frame.edgeBasis (R : Frame) : Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank R.edges_linearIndependent (by
    simp [Plane, finrank_euclideanSpace])

@[simp] lemma Frame.edgeBasis_zero (R : Frame) : R.edgeBasis 0 = R.first := by
  rw [edgeBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

@[simp] lemma Frame.edgeBasis_one (R : Frame) : R.edgeBasis 1 = R.second := by
  rw [edgeBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- The linear map that uses a point's two coordinates as frame coefficients. -/
def Frame.edgeEquiv (R : Frame) : Plane ≃ₗ[ℝ] Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans R.edgeBasis.equivFun.symm

lemma Frame.edgeEquiv_apply (R : Frame) (p : Plane) :
    R.edgeEquiv p = p 0 • R.first + p 1 • R.second := by
  simp [edgeEquiv, Basis.equivFun_symm_apply, Fin.sum_univ_two]

/-- An affine homeomorphism taking the unit square to the frame's rectangle. -/
def Frame.fromUnitSquare (R : Frame) : Plane ≃ᴬ[ℝ] Plane :=
  AffineEquiv.toContinuousAffineEquiv
    (R.edgeEquiv.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ Plane R.origin))

lemma Frame.fromUnitSquare_apply (R : Frame) (p : Plane) :
    R.fromUnitSquare p = R.origin + p 0 • R.first + p 1 • R.second := by
  change R.origin + R.edgeEquiv p = _
  rw [edgeEquiv_apply, add_assoc]

lemma Frame.fromUnitSquare_image (R : Frame) :
    R.fromUnitSquare '' unitSquare = R.carrier := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact R.mem_carrier_iff.mpr
      ⟨p 0, hp.1, p 1, hp.2, R.fromUnitSquare_apply p⟩
  · intro hx
    rcases R.mem_carrier_iff.mp hx with ⟨t, ht, u, hu, htu⟩
    refine ⟨!₂[t, u], ?_, ?_⟩
    · exact ⟨ht, hu⟩
    · simpa [fromUnitSquare_apply] using htu.symm

lemma Frame.fromUnitSquare_mem_carrier_iff (R : Frame) (p : Plane) :
    R.fromUnitSquare p ∈ R.carrier ↔ p ∈ unitSquare := by
  rw [← R.fromUnitSquare_image]
  exact R.fromUnitSquare.injective.mem_set_image

lemma Frame.toUnitSquare_image (R : Frame) :
    R.fromUnitSquare.symm '' R.carrier = unitSquare := by
  rw [← R.fromUnitSquare_image]
  exact Function.LeftInverse.image_image R.fromUnitSquare.symm_apply_apply unitSquare

lemma Frame.toUnitSquare_mem_unitSquare_iff (R : Frame) (p : Plane) :
    R.fromUnitSquare.symm p ∈ unitSquare ↔ p ∈ R.carrier := by
  rw [← R.fromUnitSquare_mem_carrier_iff]
  simp

@[simp] lemma Frame.fromUnitSquare_corner_zero (R : Frame) :
    R.fromUnitSquare (corner 0) = R.origin := by
  simp [fromUnitSquare_apply, corner]

@[simp] lemma Frame.fromUnitSquare_corner_one (R : Frame) :
    R.fromUnitSquare (corner 1) = R.origin + R.first := by
  simp [fromUnitSquare_apply, corner]

@[simp] lemma Frame.fromUnitSquare_corner_two (R : Frame) :
    R.fromUnitSquare (corner 2) = R.origin + R.first + R.second := by
  simp [fromUnitSquare_apply, corner]

@[simp] lemma Frame.fromUnitSquare_corner_three (R : Frame) :
    R.fromUnitSquare (corner 3) = R.origin + R.second := by
  simp [fromUnitSquare_apply, corner]

lemma Frame.fromUnitSquare_image_corners (R : Frame) :
    R.fromUnitSquare '' Set.range corner = R.vertices := by
  ext x
  simp only [Set.mem_image, Set.mem_range, vertices, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨corner 0, ⟨0, rfl⟩, R.fromUnitSquare_corner_zero⟩
    · exact ⟨corner 1, ⟨1, rfl⟩, R.fromUnitSquare_corner_one⟩
    · exact ⟨corner 2, ⟨2, rfl⟩, R.fromUnitSquare_corner_two⟩
    · exact ⟨corner 3, ⟨3, rfl⟩, R.fromUnitSquare_corner_three⟩

lemma Frame.toUnitSquare_image_vertices (R : Frame) :
    R.fromUnitSquare.symm '' R.vertices = Set.range corner := by
  rw [← R.fromUnitSquare_image_corners]
  exact Function.LeftInverse.image_image R.fromUnitSquare.symm_apply_apply (Set.range corner)

@[simp] lemma Frame.fromUnitSquare_squareCenter (R : Frame) :
    R.fromUnitSquare squareCenter = R.center := by
  simp [fromUnitSquare_apply, center, smul_add, add_assoc]

lemma Frame.fromUnitSquare_image_interior (R : Frame) :
    R.fromUnitSquare '' interior unitSquare = interior R.carrier := by
  change R.fromUnitSquare.toHomeomorph '' interior unitSquare = _
  rw [Homeomorph.image_interior]
  exact congrArg interior R.fromUnitSquare_image

lemma Frame.fromUnitSquare_image_frontier (R : Frame) :
    R.fromUnitSquare '' frontier unitSquare = frontier R.carrier := by
  change R.fromUnitSquare.toHomeomorph '' frontier unitSquare = _
  rw [Homeomorph.image_frontier]
  exact congrArg frontier R.fromUnitSquare_image

lemma Frame.toUnitSquare_image_interior (R : Frame) :
    R.fromUnitSquare.symm '' interior R.carrier = interior unitSquare := by
  change R.fromUnitSquare.symm.toHomeomorph '' interior R.carrier = _
  rw [Homeomorph.image_interior]
  exact congrArg interior R.toUnitSquare_image

lemma Frame.toUnitSquare_image_frontier (R : Frame) :
    R.fromUnitSquare.symm '' frontier R.carrier = frontier unitSquare := by
  change R.fromUnitSquare.symm.toHomeomorph '' frontier R.carrier = _
  rw [Homeomorph.image_frontier]
  exact congrArg frontier R.toUnitSquare_image

/-- Normalization takes any set with this rectangular hull to one with square hull. -/
lemma Frame.convexHull_toUnitSquare_image (R : Frame) {P : Set Plane}
    (hP : convexHull ℝ P = R.carrier) :
    convexHull ℝ (R.fromUnitSquare.symm '' P) = unitSquare := by
  calc
    convexHull ℝ (R.fromUnitSquare.symm '' P) =
        R.fromUnitSquare.symm '' convexHull ℝ P :=
      (R.fromUnitSquare.symm.toAffineEquiv.toAffineMap.image_convexHull P).symm
    _ = R.fromUnitSquare.symm '' R.carrier := by rw [hP]
    _ = unitSquare := R.toUnitSquare_image

lemma Frame.toUnitSquare_image_subset_unitSquare (R : Frame) {P : Set Plane}
    (hP : convexHull ℝ P = R.carrier) :
    R.fromUnitSquare.symm '' P ⊆ unitSquare := by
  rw [← R.toUnitSquare_image]
  exact Set.image_mono (R.subset_carrier_of_convexHull_eq hP)

lemma Frame.corners_subset_toUnitSquare_image (R : Frame) {P : Set Plane}
    (hP : convexHull ℝ P = R.carrier) :
    Set.range corner ⊆ R.fromUnitSquare.symm '' P := by
  rw [← R.toUnitSquare_image_vertices]
  exact Set.image_mono (R.vertices_subset_of_convexHull_eq hP)

end

end Puzzling139335.RectangularHull
