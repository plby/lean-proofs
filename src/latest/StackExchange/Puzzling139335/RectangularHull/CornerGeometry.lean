import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Topology

/-!
# Coordinate geometry at corners of the square

These elementary lemmas identify a square corner occurring in a finite
convex hull, and show that perpendicular edges pointing into one square
quadrant must follow its two coordinate axes.
-/

open Set

namespace Puzzling139335.RectangularHull

theorem convex_unitSquare : Convex ℝ unitSquare := by
  exact ((convex_Icc (0 : ℝ) 1).linear_preimage
      (EuclideanSpace.proj (0 : Fin 2)).toLinearMap).inter
    ((convex_Icc (0 : ℝ) 1).linear_preimage
      (EuclideanSpace.proj (1 : Fin 2)).toLinearMap)

private theorem zero_of_strict_average_zero {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : a * x + b * y = 0) : x = 0 := by
  have hax : 0 ≤ a * x := mul_nonneg ha.le hx
  have hby : 0 ≤ b * y := mul_nonneg hb.le hy
  have hzero : a * x = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt ha)

private theorem one_of_strict_average_one {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : x ≤ 1) (hy : y ≤ 1) (h : a * x + b * y = 1) : x = 1 := by
  have hz : a * (1 - x) + b * (1 - y) = 0 := by nlinarith only [hab, h]
  have := zero_of_strict_average_zero ha hb (sub_nonneg.mpr hx) (sub_nonneg.mpr hy) hz
  linarith

/-- Every square corner is an extreme point of the square. -/
theorem corner_mem_extremePoints (j : Fin 4) :
    corner j ∈ unitSquare.extremePoints ℝ := by
  refine ⟨corner_mem_unitSquare j, ?_⟩
  intro p hp q hq hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hzero : a * p 0 + b * q 0 = corner j 0 := congrArg (fun z : Plane => z 0) heq
  have hone : a * p 1 + b * q 1 = corner j 1 := congrArg (fun z : Plane => z 1) heq
  ext i
  fin_cases i
  · by_cases hj : j = 1 ∨ j = 2
    · simp only [corner, hj, if_true, Matrix.cons_val_zero] at hzero ⊢
      exact one_of_strict_average_one ha hb hab hp.1.2 hq.1.2 hzero
    · simp only [corner, hj, if_false, Matrix.cons_val_zero] at hzero ⊢
      exact zero_of_strict_average_zero ha hb hp.1.1 hq.1.1 hzero
  · by_cases hj : j = 2 ∨ j = 3
    · simp only [corner, hj, if_true, Matrix.cons_val_one, Matrix.cons_val_zero] at hone ⊢
      exact one_of_strict_average_one ha hb hab hp.2.2 hq.2.2 hone
    · simp only [corner, hj, if_false, Matrix.cons_val_one, Matrix.cons_val_zero] at hone ⊢
      exact zero_of_strict_average_zero ha hb hp.2.1 hq.2.1 hone

/-- A square corner in a convex hull contained in the square already
belongs to the generating set. -/
theorem corner_mem_of_mem_convexHull {P : Set Plane} (hP : P ⊆ unitSquare)
    {j : Fin 4} (hj : corner j ∈ convexHull ℝ P) : corner j ∈ P := by
  have hsub : convexHull ℝ P ⊆ unitSquare := convexHull_min hP convex_unitSquare
  exact extremePoints_convexHull_subset
    (inter_extremePoints_subset_extremePoints_of_subset hsub
      ⟨hj, corner_mem_extremePoints j⟩)

/-- Two nonzero perpendicular vectors in the closed positive quadrant
are positive vectors on the two different coordinate axes. -/
theorem orthogonal_nonnegative_axis_vectors {u v : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) (hu0 : 0 ≤ u 0) (hu1 : 0 ≤ u 1)
    (hv0 : 0 ≤ v 0) (hv1 : 0 ≤ v 1) (huv : inner ℝ u v = 0) :
    (0 < u 0 ∧ u 1 = 0 ∧ v 0 = 0 ∧ 0 < v 1) ∨
      (u 0 = 0 ∧ 0 < u 1 ∧ 0 < v 0 ∧ v 1 = 0) := by
  rw [Schoenflies.Plane.inner_eq] at huv
  have hp0 : u 0 * v 0 = 0 := by
    nlinarith only [huv, mul_nonneg hu0 hv0, mul_nonneg hu1 hv1]
  have hp1 : u 1 * v 1 = 0 := by
    nlinarith only [huv, mul_nonneg hu0 hv0, mul_nonneg hu1 hv1]
  have hupos : 0 < u 0 ∨ 0 < u 1 := by
    by_contra h
    push Not at h
    apply hu
    ext i
    fin_cases i <;> simp <;> linarith
  rcases hupos with hux | huy
  · have hvx : v 0 = 0 := (mul_eq_zero.mp hp0).resolve_left (ne_of_gt hux)
    have hvy : 0 < v 1 := by
      by_contra h
      apply hv
      ext i
      fin_cases i
      · simpa using hvx
      · simp
        linarith
    have huyzero : u 1 = 0 := (mul_eq_zero.mp hp1).resolve_right (ne_of_gt hvy)
    exact Or.inl ⟨hux, huyzero, hvx, hvy⟩
  · have hvy : v 1 = 0 := (mul_eq_zero.mp hp1).resolve_left (ne_of_gt huy)
    have hvx : 0 < v 0 := by
      by_contra h
      apply hv
      ext i
      fin_cases i
      · simp
        linarith
      · simpa using hvy
    have huxzero : u 0 = 0 := (mul_eq_zero.mp hp0).resolve_right (ne_of_gt hvx)
    exact Or.inr ⟨huxzero, huy, hvx, hvy⟩

/-- If the two coordinate products are nonnegative, perpendicular nonzero
vectors must use different coordinate axes. -/
theorem orthogonal_nonnegative_products_axis_vectors {u v : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) (h0 : 0 ≤ u 0 * v 0)
    (h1 : 0 ≤ u 1 * v 1) (huv : inner ℝ u v = 0) :
    (u 0 = 0 ∧ v 1 = 0) ∨ (u 1 = 0 ∧ v 0 = 0) := by
  rw [Schoenflies.Plane.inner_eq] at huv
  have hp0 : u 0 * v 0 = 0 := by linarith
  have hp1 : u 1 * v 1 = 0 := by linarith
  by_cases hu0 : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro hu1
      apply hu
      ext i
      fin_cases i <;> simp [hu0, hu1]
    exact Or.inl ⟨hu0, (mul_eq_zero.mp hp1).resolve_left hu1⟩
  · have hv0 : v 0 = 0 := (mul_eq_zero.mp hp0).resolve_left hu0
    have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i <;> simp [hv0, hv1]
    exact Or.inr ⟨(mul_eq_zero.mp hp1).resolve_right hv1, hv0⟩

/-- Perpendicular nonzero edges based at a square corner and directed into
the square are parallel to its sides. -/
theorem orthogonal_edges_at_corner_axis {u v : Plane} (j : Fin 4)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : inner ℝ u v = 0)
    (huS : corner j + u ∈ unitSquare) (hvS : corner j + v ∈ unitSquare) :
    (u 0 = 0 ∧ v 1 = 0) ∨ (u 1 = 0 ∧ v 0 = 0) := by
  apply orthogonal_nonnegative_products_axis_vectors hu hv ?_ ?_ huv
  · by_cases hj : j = 1 ∨ j = 2
    · have hu0 : u 0 ≤ 0 := by
        have := huS.1.2
        simp only [corner, hj, if_true, PiLp.add_apply, Matrix.cons_val_zero] at this
        linarith
      have hv0 : v 0 ≤ 0 := by
        have := hvS.1.2
        simp only [corner, hj, if_true, PiLp.add_apply, Matrix.cons_val_zero] at this
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos hu0 hv0
    · have hu0 : 0 ≤ u 0 := by
        have := huS.1.1
        simpa only [corner, hj, if_false, PiLp.add_apply,
          Matrix.cons_val_zero, zero_add] using this
      have hv0 : 0 ≤ v 0 := by
        have := hvS.1.1
        simpa only [corner, hj, if_false, PiLp.add_apply,
          Matrix.cons_val_zero, zero_add] using this
      exact mul_nonneg hu0 hv0
  · by_cases hj : j = 2 ∨ j = 3
    · have hu1 : u 1 ≤ 0 := by
        have := huS.2.2
        simp only [corner, hj, if_true, PiLp.add_apply,
          Matrix.cons_val_one, Matrix.cons_val_zero] at this
        linarith
      have hv1 : v 1 ≤ 0 := by
        have := hvS.2.2
        simp only [corner, hj, if_true, PiLp.add_apply,
          Matrix.cons_val_one, Matrix.cons_val_zero] at this
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos hu1 hv1
    · have hu1 : 0 ≤ u 1 := by
        have := huS.2.1
        simpa only [corner, hj, if_false, PiLp.add_apply,
          Matrix.cons_val_one, Matrix.cons_val_zero, zero_add] using this
      have hv1 : 0 ≤ v 1 := by
        have := hvS.2.1
        simpa only [corner, hj, if_false, PiLp.add_apply,
          Matrix.cons_val_one, Matrix.cons_val_zero, zero_add] using this
      exact mul_nonneg hu1 hv1

end Puzzling139335.RectangularHull
