import StackExchange.Puzzling139335.UnitPairs.TriangleHull
import StackExchange.Puzzling139335.Basic

/-!
# The square center inside an equilateral triangle on a square side

Strict inward determinant inequalities give an open neighborhood in a
triangle.  The coordinate calculation below uses only squared unit lengths,
so no choice of a square root or orientation is needed.
-/

open Set
open Puzzling139335.UnitPairs

namespace Puzzling139335.N8

theorem continuous_sideDet (a b : Plane) : Continuous (sideDet a b) := by
  exact (continuous_const.mul ((EuclideanSpace.proj 1).continuous.sub
    continuous_const)).sub (continuous_const.mul
      ((EuclideanSpace.proj 0).continuous.sub continuous_const))

/-- Strict membership in the three inward halfplanes puts a point in the
ordinary planar interior of the triangle. -/
theorem mem_interior_convexHull_triangle_of_sideDet {a b c x : Plane}
    (hnonzero : sideDet a b c ≠ 0)
    (hab : 0 < sideDet a b c * sideDet a b x)
    (hbc : 0 < sideDet b c a * sideDet b c x)
    (hca : 0 < sideDet c a b * sideDet c a x) :
    x ∈ interior (convexHull ℝ ({a, b, c} : Set Plane)) := by
  let U : Set Plane := {y | 0 < sideDet a b c * sideDet a b y} ∩
    {y | 0 < sideDet b c a * sideDet b c y} ∩
    {y | 0 < sideDet c a b * sideDet c a y}
  have hopen : IsOpen U := by
    exact ((isOpen_lt continuous_const
      (continuous_const.mul (continuous_sideDet a b))).inter
      (isOpen_lt continuous_const
        (continuous_const.mul (continuous_sideDet b c)))).inter
      (isOpen_lt continuous_const
        (continuous_const.mul (continuous_sideDet c a)))
  have hsub : U ⊆ convexHull ℝ ({a, b, c} : Set Plane) := by
    rintro y ⟨⟨hyab, hybc⟩, hyca⟩
    exact mem_convexHull_triangle_of_sideDet hnonzero
      hyab.le hybc.le hyca.le
  apply interior_mono hsub
  rw [hopen.interior_eq]
  exact ⟨⟨hab, hbc⟩, hca⟩

/-- The inward apex of a unit equilateral triangle on the bottom square
side has horizontal coordinate `1/2` and height strictly greater than `1/2`. -/
theorem equilateral_bottom_apex {c : Plane} (hc : c ∈ unitSquare)
    (hbc : dist (corner 1) c = 1) (hca : dist c (corner 0) = 1) :
    c 0 = (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < c 1 := by
  have hbc' : (1 - c 0) ^ 2 + c 1 ^ 2 = 1 := by
    have h := plane_dist_sq (corner 1) c
    rw [hbc] at h
    norm_num [corner, Fin.ext_iff] at h
    nlinarith [h]
  have hca' : c 0 ^ 2 + c 1 ^ 2 = 1 := by
    have h := plane_dist_sq c (corner 0)
    rw [hca] at h
    norm_num [corner, Fin.ext_iff] at h
    linarith
  have hx : c 0 = (1 / 2 : ℝ) := by nlinarith [hbc', hca']
  refine ⟨hx, ?_⟩
  nlinarith [hca', hc.2.1]

/-- An equilateral unit triangle placed on the bottom side and contained in
the square contains a neighborhood of the square center. -/
theorem squareCenter_mem_interior_triangle_bottom {c : Plane}
    (hc : c ∈ unitSquare)
    (hbc : dist (corner 1) c = 1) (hca : dist c (corner 0) = 1) :
    squareCenter ∈ interior
      (convexHull ℝ ({corner 0, corner 1, c} : Set Plane)) := by
  obtain ⟨hx, hy⟩ := equilateral_bottom_apex hc hbc hca
  apply mem_interior_convexHull_triangle_of_sideDet
  · norm_num [sideDet, corner, Fin.ext_iff]
    linarith
  · norm_num [sideDet, corner, squareCenter, Fin.ext_iff]
    linarith
  · norm_num [sideDet, corner, squareCenter, Fin.ext_iff]
    rw [hx]
    nlinarith
  · norm_num [sideDet, corner, squareCenter, Fin.ext_iff]
    rw [hx]
    nlinarith

/-- The same center conclusion for any two square corners at unit distance;
the order of the side endpoints is unrestricted. -/
theorem squareCenter_mem_interior_triangle_of_square_corners (i j : Fin 4)
    {c : Plane} (hc : c ∈ unitSquare)
    (hab : dist (corner i) (corner j) = 1)
    (hbc : dist (corner j) c = 1) (hca : dist c (corner i) = 1) :
    squareCenter ∈ interior
      (convexHull ℝ ({corner i, corner j, c} : Set Plane)) := by
  have hab' : dist (corner i) (corner j) ^ 2 = 1 := by rw [hab]; norm_num
  have hbc' : dist (corner j) c ^ 2 = 1 := by rw [hbc]; norm_num
  have hca' : dist c (corner i) ^ 2 = 1 := by rw [hca]; norm_num
  have hx0 := hc.1.1
  have hx1 := hc.1.2
  have hy0 := hc.2.1
  have hy1 := hc.2.2
  apply mem_interior_convexHull_triangle_of_sideDet
    (sideDet_ne_zero_of_equidistant hab hbc hca)
  all_goals
    fin_cases i <;> fin_cases j <;>
      norm_num [plane_dist_sq, corner, Fin.ext_iff] at hab'
  all_goals
    norm_num [plane_dist_sq, sideDet, corner, squareCenter, Fin.ext_iff]
      at hbc' hca' ⊢
  all_goals nlinarith

/-- Every pair of consecutive square corners is one unit apart. -/
private theorem triangle_base_dist (i : Fin 4) :
    dist (corner i) (corner (i + 1)) = 1 := by
  apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
  fin_cases i <;>
    norm_num [plane_dist_sq, corner, Fin.ext_iff, Fin.val_add]

/-- Counterclockwise adjacent-side form of the center theorem. -/
theorem squareCenter_mem_interior_triangle_of_adjacent_corners (i : Fin 4)
    {c : Plane} (hc : c ∈ unitSquare)
    (hbc : dist (corner (i + 1)) c = 1) (hca : dist c (corner i) = 1) :
    squareCenter ∈ interior
      (convexHull ℝ ({corner i, corner (i + 1), c} : Set Plane)) := by
  exact squareCenter_mem_interior_triangle_of_square_corners i (i + 1) hc
    (triangle_base_dist i) hbc hca

/-- The counterclockwise square sides have the square on their nonnegative
determinant side. -/
theorem sideDet_adjacent_corners_nonneg (i : Fin 4) {c : Plane}
    (hc : c ∈ unitSquare) : 0 ≤ sideDet (corner i) (corner (i + 1)) c := by
  fin_cases i <;>
    norm_num [sideDet, corner, Fin.ext_iff, Fin.val_add]
  all_goals linarith [hc.1.1, hc.1.2, hc.2.1, hc.2.2]

/-- A given square side has only one equilateral unit apex inside the square. -/
theorem equilateral_apex_unique (i : Fin 4) {c d : Plane}
    (hc : c ∈ unitSquare) (hd : d ∈ unitSquare)
    (hbc : dist (corner (i + 1)) c = 1) (hca : dist c (corner i) = 1)
    (hbd : dist (corner (i + 1)) d = 1) (hda : dist d (corner i) = 1) :
    c = d := by
  have hcDet := sideDet_sq_of_equidistant (triangle_base_dist i) hbc hca
  have hdDet := sideDet_sq_of_equidistant (triangle_base_dist i) hbd hda
  have heqDet : sideDet (corner i) (corner (i + 1)) c =
      sideDet (corner i) (corner (i + 1)) d :=
    (sq_eq_sq₀ (sideDet_adjacent_corners_nonneg i hc)
      (sideDet_adjacent_corners_nonneg i hd)).mp (hcDet.trans hdDet.symm)
  have hbc' : dist (corner (i + 1)) c ^ 2 = 1 := by rw [hbc]; norm_num
  have hca' : dist c (corner i) ^ 2 = 1 := by rw [hca]; norm_num
  have hbd' : dist (corner (i + 1)) d ^ 2 = 1 := by rw [hbd]; norm_num
  have hda' : dist d (corner i) ^ 2 = 1 := by rw [hda]; norm_num
  ext k
  fin_cases i <;> fin_cases k <;>
    norm_num [plane_dist_sq, sideDet, corner, Fin.ext_iff, Fin.val_add]
      at heqDet hbc' hca' hbd' hda' ⊢
  all_goals nlinarith

end Puzzling139335.N8
