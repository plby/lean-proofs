import StackExchange.Puzzling139335.UnitPairs.TriangleHull
import Mathlib.Analysis.Convex.Topology

/-!
# The closed halfplanes and faces of a triangle

The determinant inequalities hold on the whole convex hull.  Equality in
one of them identifies an actual side segment of a nondegenerate triangle.
-/

open Set
open Puzzling139335.UnitPairs

namespace Puzzling139335.N8

theorem sideDet_smul_add (a b x y : Plane) {u v : ℝ} (huv : u + v = 1) :
    sideDet a b (u • x + v • y) = u * sideDet a b x + v * sideDet a b y := by
  simp only [sideDet, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination ((b 0 - a 0) * a 1 - (b 1 - a 1) * a 0) * huv

theorem convex_sideDet_mul_nonneg (a b c : Plane) :
    Convex ℝ {x | 0 ≤ sideDet a b c * sideDet a b x} := by
  intro x hx y hy u v hu hv huv
  change 0 ≤ sideDet a b c * sideDet a b (u • x + v • y)
  rw [sideDet_smul_add a b x y huv]
  calc
    0 ≤ u * (sideDet a b c * sideDet a b x) +
        v * (sideDet a b c * sideDet a b y) :=
      add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)
    _ = sideDet a b c * (u * sideDet a b x + v * sideDet a b y) := by ring

theorem sideDet_mul_nonneg_of_mem_convexHull_triangle {a b c x : Plane}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) :
    0 ≤ sideDet a b c * sideDet a b x := by
  apply convexHull_min (t := {y | 0 ≤ sideDet a b c * sideDet a b y})
    ?_ (convex_sideDet_mul_nonneg a b c) hx
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  change 0 ≤ sideDet a b c * sideDet a b y
  rcases hy with ha | hb | hc
  · rw [ha]
    simp [sideDet]
  · rw [hb]
    have hzero : sideDet a b b = 0 := by unfold sideDet; ring
    simp [hzero]
  · rw [hc]
    exact mul_self_nonneg _

theorem convexHull_triangle_cyclic (a b c : Plane) :
    convexHull ℝ ({b, c, a} : Set Plane) =
      convexHull ℝ ({a, b, c} : Set Plane) := by
  congr 1
  ext x
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto

theorem triangle_barycentric_eq (a b c x : Plane)
    (hnonzero : sideDet a b c ≠ 0) :
    (sideDet b c x / sideDet a b c) • a +
      (sideDet c a x / sideDet a b c) • b +
      (sideDet a b x / sideDet a b c) • c = x := by
  ext i
  fin_cases i <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  · change sideDet b c x / sideDet a b c * a 0 +
        sideDet c a x / sideDet a b c * b 0 +
        sideDet a b x / sideDet a b c * c 0 = x 0
    field_simp [hnonzero]
    unfold sideDet
    ring
  · change sideDet b c x / sideDet a b c * a 1 +
        sideDet c a x / sideDet a b c * b 1 +
        sideDet a b x / sideDet a b c * c 1 = x 1
    field_simp [hnonzero]
    unfold sideDet
    ring

/-- A zero inward determinant identifies the corresponding closed side. -/
theorem mem_segment_of_mem_convexHull_triangle_of_sideDet_eq_zero
    {a b c x : Plane} (hnonzero : sideDet a b c ≠ 0)
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Plane))
    (hzero : sideDet a b x = 0) : x ∈ segment ℝ a b := by
  have hx' : x ∈ convexHull ℝ ({b, c, a} : Set Plane) := by
    rwa [convexHull_triangle_cyclic]
  have hx'' : x ∈ convexHull ℝ ({c, a, b} : Set Plane) := by
    rwa [convexHull_triangle_cyclic]
  have hbc := sideDet_mul_nonneg_of_mem_convexHull_triangle hx'
  have hca := sideDet_mul_nonneg_of_mem_convexHull_triangle hx''
  simp only [sideDet_cyclic] at hbc hca
  have hwa : 0 ≤ sideDet b c x / sideDet a b c := by
    apply div_nonneg_iff.mpr
    simpa only [and_comm] using mul_nonneg_iff.mp hbc
  have hwb : 0 ≤ sideDet c a x / sideDet a b c := by
    apply div_nonneg_iff.mpr
    simpa only [and_comm] using mul_nonneg_iff.mp hca
  refine ⟨_, _, hwa, hwb, ?_, ?_⟩
  · rw [← add_div]
    have hsum := sideDet_sum a b c x
    rw [hzero, add_zero] at hsum
    rw [hsum, div_self hnonzero]
  · simpa only [hzero, zero_div, zero_smul, add_zero] using
      triangle_barycentric_eq a b c x hnonzero

theorem isClosed_convexHull_triangle (a b c : Plane) :
    IsClosed (convexHull ℝ ({a, b, c} : Set Plane)) := by
  exact ((finite_singleton c).insert b |>.insert a).isClosed_convexHull ℝ

end Puzzling139335.N8
