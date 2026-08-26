import ErdosProblems.Erdos633b.Parallelogram

/-! Construct the actual affine map and rigid motion between congruent triangles. -/

namespace Erdos633b.Triangle

noncomputable def vertexMap (T S : Triangle) : Plane →ᵃ[ℝ] Plane :=
  (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (S.edgeVector 1)).toAffineMap.comp (T.coord 1)) +
    (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (S.edgeVector 2)).toAffineMap.comp (T.coord 2)) +
      AffineMap.const ℝ Plane (S.points 0)

theorem vertexMap_apply (T S : Triangle) (p : Plane) :
    T.vertexMap S p = S.latticeShift (T.coord 1 p) (T.coord 2 p) + S.points 0 := rfl

theorem vertexMap_vertex (T S : Triangle) (i : Fin 3) :
    T.vertexMap S (T.points i) = S.points i := by
  fin_cases i <;> simp [vertexMap_apply, coord_vertex, latticeShift, edgeVector]

theorem vertexMap_coords (T S : Triangle) (p : Plane) :
    S.coord 1 (T.vertexMap S p) = T.coord 1 p ∧
      S.coord 2 (T.vertexMap S p) = T.coord 2 p := by
  rw [vertexMap_apply, coord_shift_one, coord_shift_two]
  simp [coord_vertex]

theorem vertexMap_inverse (T S : Triangle) (p : Plane) : S.vertexMap T (T.vertexMap S p) = p := by
  rw [vertexMap_apply, (T.vertexMap_coords S p).1, (T.vertexMap_coords S p).2, T.reconstruct p]

theorem vertexMap_bijective (T S : Triangle) : Function.Bijective (T.vertexMap S) :=
  ⟨Function.LeftInverse.injective (T.vertexMap_inverse S),
    Function.RightInverse.surjective (S.vertexMap_inverse T)⟩

theorem sub_eq_latticeShift (T : Triangle) (p q : Plane) :
    p - q = T.latticeShift (T.coord 1 p - T.coord 1 q) (T.coord 2 p - T.coord 2 q) := by
  calc
    _ = (T.latticeShift (T.coord 1 p) (T.coord 2 p) + T.points 0) -
        (T.latticeShift (T.coord 1 q) (T.coord 2 q) + T.points 0) := by
      rw [T.reconstruct p, T.reconstruct q]
    _ = _ := by simp only [latticeShift]; module

theorem vertexMap_sub (T S : Triangle) (p q : Plane) :
    T.vertexMap S p - T.vertexMap S q =
      S.latticeShift (T.coord 1 p - T.coord 1 q) (T.coord 2 p - T.coord 2 q) := by
  rw [vertexMap_apply, vertexMap_apply]
  simp only [latticeShift]
  module

theorem edgeVector_sub (T : Triangle) (i j : Fin 3) :
    T.edgeVector i - T.edgeVector j = T.points i - T.points j := by
  simp only [edgeVector]
  abel

theorem edge_gram_of_distances (T S : Triangle)
    (h : ∀ i j, dist (T.points i) (T.points j) = dist (S.points i) (S.points j)) :
    ‖T.edgeVector 1‖ = ‖S.edgeVector 1‖ ∧ ‖T.edgeVector 2‖ = ‖S.edgeVector 2‖ ∧
      inner ℝ (T.edgeVector 1) (T.edgeVector 2) = inner ℝ (S.edgeVector 1) (S.edgeVector 2) := by
  have h1 : ‖T.edgeVector 1‖ = ‖S.edgeVector 1‖ := by
    simpa only [edgeVector, dist_eq_norm] using h 1 0
  have h2 : ‖T.edgeVector 2‖ = ‖S.edgeVector 2‖ := by
    simpa only [edgeVector, dist_eq_norm] using h 2 0
  have h12 : ‖T.edgeVector 1 - T.edgeVector 2‖ = ‖S.edgeVector 1 - S.edgeVector 2‖ := by
    simpa only [edgeVector_sub, dist_eq_norm] using h 1 2
  refine ⟨h1, h2, ?_⟩
  have hT := norm_sub_sq_real (T.edgeVector 1) (T.edgeVector 2)
  have hS := norm_sub_sq_real (S.edgeVector 1) (S.edgeVector 2)
  rw [h1, h2, h12] at hT
  linarith

theorem norm_latticeShift_eq_of_distances (T S : Triangle)
    (h : ∀ i j, dist (T.points i) (T.points j) = dist (S.points i) (S.points j)) (x y : ℝ) :
    ‖T.latticeShift x y‖ = ‖S.latticeShift x y‖ := by
  obtain ⟨h1, h2, h12⟩ := T.edge_gram_of_distances S h
  have hsq : ‖T.latticeShift x y‖ ^ 2 = ‖S.latticeShift x y‖ ^ 2 := by
    simp only [latticeShift, norm_add_sq_real, norm_smul, real_inner_smul_left,
      inner_smul_right, h1, h2, h12]
  nlinarith [norm_nonneg (T.latticeShift x y), norm_nonneg (S.latticeShift x y)]

theorem vertexMap_dist (T S : Triangle)
    (h : ∀ i j, dist (T.points i) (T.points j) = dist (S.points i) (S.points j)) (p q : Plane) :
    dist (T.vertexMap S p) (T.vertexMap S q) = dist p q := by
  rw [dist_eq_norm, vertexMap_sub, ← norm_latticeShift_eq_of_distances T S h,
    ← sub_eq_latticeShift, ← dist_eq_norm]

/-- The affine vertex map is a rigid motion when all corresponding distances agree. -/
noncomputable def vertexIsometry (T S : Triangle)
    (h : ∀ i j, dist (T.points i) (T.points j) = dist (S.points i) (S.points j)) :
    Plane ≃ᵃⁱ[ℝ] Plane where
  toAffineEquiv := AffineEquiv.ofBijective (T.vertexMap_bijective S)
  norm_map v := by
    change ‖(T.vertexMap S).linear v‖ = ‖v‖
    have hv : (T.vertexMap S).linear v = T.vertexMap S v - T.vertexMap S 0 := by
      simpa using (T.vertexMap S).linearMap_vsub v 0
    rw [hv, ← dist_eq_norm, vertexMap_dist T S h, dist_zero_right]

theorem move_vertexIsometry (T S : Triangle)
    (h : ∀ i j, dist (T.points i) (T.points j) = dist (S.points i) (S.points j)) :
    T.move (T.vertexIsometry S h) = S := by
  apply Affine.Simplex.ext
  intro i
  change T.vertexMap S (T.points i) = S.points i
  exact vertexMap_vertex T S i

end Erdos633b.Triangle
