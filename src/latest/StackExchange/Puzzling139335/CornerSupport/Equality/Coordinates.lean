import StackExchange.Puzzling139335.CornerSupport.Frames

/-!
# Coordinate signs from a bisector support inequality

In an orthonormal planar basis, projection at most minus the norm onto the
sum of the basis vectors forces both coordinates to be nonpositive. The
opposite bisector similarly forces both coordinates to be nonnegative.
-/

open Set

namespace Puzzling139335.CornerSupport.Equality

/-- A support bound in the direction of the basis sum forces two
nonpositive coordinates. -/
theorem coords_nonpos_of_sum_projection (B : OrthonormalBasis (Fin 2) ℝ Plane)
    (δ : Plane) (hproj : inner ℝ (B 0 + B 1) δ ≤ -‖δ‖) :
    inner ℝ (B 0) δ ≤ 0 ∧ inner ℝ (B 1) δ ≤ 0 := by
  have hparseval : (inner ℝ (B 0) δ) ^ 2 + (inner ℝ (B 1) δ) ^ 2 = ‖δ‖ ^ 2 := by
    simpa [Fin.sum_univ_two] using B.sum_sq_inner_right δ
  rw [inner_add_left] at hproj
  have hsum : inner ℝ (B 0) δ + inner ℝ (B 1) δ ≤ 0 := by
    linarith [norm_nonneg δ]
  have hsq : ‖δ‖ ^ 2 ≤ (-(inner ℝ (B 0) δ + inner ℝ (B 1) δ)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg δ) (by linarith)).mpr (by linarith)
  have hprod : 0 ≤ inner ℝ (B 0) δ * inner ℝ (B 1) δ := by
    nlinarith
  rcases mul_nonneg_iff.mp hprod with hnonneg | hnonpos
  · constructor <;> linarith [hnonneg.1, hnonneg.2]
  · exact hnonpos

/-- A support bound in the direction opposite to the basis sum forces two
nonnegative coordinates. -/
theorem coords_nonneg_of_neg_sum_projection (B : OrthonormalBasis (Fin 2) ℝ Plane)
    (δ : Plane) (hproj : inner ℝ (-(B 0 + B 1)) δ ≤ -‖δ‖) :
    0 ≤ inner ℝ (B 0) δ ∧ 0 ≤ inner ℝ (B 1) δ := by
  have hneg : inner ℝ (B 0 + B 1) (-δ) ≤ -‖-δ‖ := by
    simpa only [inner_neg_left, inner_neg_right, norm_neg] using hproj
  simpa only [inner_neg_right, neg_nonpos] using
    coords_nonpos_of_sum_projection B (-δ) hneg

/-- A corner with outward bisector equal to the basis sum bounds every
point's two coordinates above by those of the corner. -/
theorem coords_nonpos_of_bisector_eq_sum {P : Set Plane} {v x : Plane}
    (h : SupportCorner P v) (B : OrthonormalBasis (Fin 2) ℝ Plane)
    (hsum : h.bisector = B 0 + B 1) (hx : x ∈ P) :
    inner ℝ (B 0) (x - v) ≤ 0 ∧ inner ℝ (B 1) (x - v) ≤ 0 := by
  apply coords_nonpos_of_sum_projection B (x - v)
  rw [← hsum]
  exact h.bisector_projection hx

/-- The opposite outward bisector bounds both coordinates below by those
of the corner. -/
theorem coords_nonneg_of_bisector_eq_neg_sum {P : Set Plane} {v x : Plane}
    (h : SupportCorner P v) (B : OrthonormalBasis (Fin 2) ℝ Plane)
    (hsum : h.bisector = -(B 0 + B 1)) (hx : x ∈ P) :
    0 ≤ inner ℝ (B 0) (x - v) ∧ 0 ≤ inner ℝ (B 1) (x - v) := by
  apply coords_nonneg_of_neg_sum_projection B (x - v)
  rw [← hsum]
  exact h.bisector_projection hx

end Puzzling139335.CornerSupport.Equality
