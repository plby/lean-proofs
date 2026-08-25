import StackExchange.Puzzling139335.UnitPairs.Defs
import Mathlib.Analysis.Convex.Combination

/-!
# A triangle as the intersection of its inward halfplanes

The signed determinants give explicit barycentric coordinates.  Their
nonnegativity proves membership without any regularity assumption on a tile.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.UnitPairs

theorem sideDet_cyclic (a b c : Plane) :
    sideDet b c a = sideDet a b c := by
  unfold sideDet
  ring

theorem sideDet_sum (a b c x : Plane) :
    sideDet b c x + sideDet c a x + sideDet a b x = sideDet a b c := by
  unfold sideDet
  ring

private theorem div_nonneg_of_mul_nonneg {u v : ℝ} (h : 0 ≤ v * u) :
    0 ≤ u / v := by
  apply div_nonneg_iff.mpr
  simpa only [and_comm] using mul_nonneg_iff.mp h

/-- The three inward closed halfplanes of a nondegenerate triangle intersect
in its convex hull.  The orientation of the triangle is unrestricted. -/
theorem mem_convexHull_triangle_of_sideDet {a b c x : Plane}
    (hnonzero : sideDet a b c ≠ 0)
    (hab : 0 ≤ sideDet a b c * sideDet a b x)
    (hbc : 0 ≤ sideDet b c a * sideDet b c x)
    (hca : 0 ≤ sideDet c a b * sideDet c a x) :
    x ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  let w : Fin 3 → ℝ :=
    ![sideDet b c x / sideDet a b c,
      sideDet c a x / sideDet a b c,
      sideDet a b x / sideDet a b c]
  let z : Fin 3 → Plane := ![a, b, c]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · apply div_nonneg_of_mul_nonneg
      simpa only [sideDet_cyclic] using hbc
    · apply div_nonneg_of_mul_nonneg
      simpa only [sideDet_cyclic] using hca
    · exact div_nonneg_of_mul_nonneg hab
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 3)), w i = 1 := by
    simp only [w, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    rw [← add_div, ← add_div, ← add_assoc, sideDet_sum, div_self hnonzero]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      z i ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
    intro i _
    apply subset_convexHull
    fin_cases i <;> simp [z]
  have hx : (∑ i ∈ (Finset.univ : Finset (Fin 3)), w i • z i) = x := by
    ext i
    fin_cases i <;>
      simp only [w, z, Fin.sum_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    · change sideDet b c x / sideDet a b c * a 0 +
        (sideDet c a x / sideDet a b c * b 0 +
          sideDet a b x / sideDet a b c * c 0) = x 0
      field_simp [hnonzero]
      unfold sideDet
      ring
    · change sideDet b c x / sideDet a b c * a 1 +
        (sideDet c a x / sideDet a b c * b 1 +
          sideDet a b x / sideDet a b c * c 1) = x 1
      field_simp [hnonzero]
      unfold sideDet
      ring
  rw [← hx]
  exact (convex_convexHull ℝ ({a, b, c} : Set Plane)).sum_mem hw hsum hz

/-- A unit equilateral triangle has signed doubled area with square `3 / 4`. -/
theorem sideDet_sq_of_equidistant {a b c : Plane}
    (hab : dist a b = 1) (hbc : dist b c = 1) (hca : dist c a = 1) :
    sideDet a b c ^ 2 = (3 / 4 : ℝ) := by
  have hu : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 = 1 := by
    rw [← plane_dist_sq, dist_comm, hab]
    norm_num
  have hv : (c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2 = 1 := by
    rw [← plane_dist_sq, hca]
    norm_num
  have huv : (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 = 1 := by
    rw [← plane_dist_sq, hbc]
    norm_num
  have hdot :
      (b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1) = (1 / 2 : ℝ) := by
    nlinarith [hu, hv, huv]
  calc
    sideDet a b c ^ 2 =
        ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) *
          ((c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2) -
        ((b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1)) ^ 2 := by
      unfold sideDet
      ring
    _ = (3 / 4 : ℝ) := by rw [hu, hv, hdot]; norm_num

theorem sideDet_ne_zero_of_equidistant {a b c : Plane}
    (hab : dist a b = 1) (hbc : dist b c = 1) (hca : dist c a = 1) :
    sideDet a b c ≠ 0 := by
  intro hzero
  have hs := sideDet_sq_of_equidistant hab hbc hca
  rw [hzero] at hs
  norm_num at hs

end Puzzling139335.UnitPairs
