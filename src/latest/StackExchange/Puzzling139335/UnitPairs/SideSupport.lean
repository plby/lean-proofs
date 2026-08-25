import StackExchange.Puzzling139335.UnitPairs.Defs
import StackExchange.Puzzling139335.PlaneIsometries

/-!
# A placed unit side is a supporting line

The signed determinant detects which side of a line contains a point.
An actual placement of the entire set in the square, taking a unit pair
to corners, puts the entire set on the same side of that pair's line.
No supporting-line assumption is added to the placement hypothesis.
-/

open Set
open Puzzling139335.PlaneIsometries

namespace Puzzling139335.UnitPairs

theorem sideDet_directCoordinates (c s : ℝ) (t a b x : Plane) :
    sideDet (directCoordinates c s t a) (directCoordinates c s t b)
      (directCoordinates c s t x) = (c ^ 2 + s ^ 2) * sideDet a b x := by
  simp only [sideDet, directCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem sideDet_reversingCoordinates (c s : ℝ) (t a b x : Plane) :
    sideDet (reversingCoordinates c s t a) (reversingCoordinates c s t b)
      (reversingCoordinates c s t x) = -(c ^ 2 + s ^ 2) * sideDet a b x := by
  simp only [sideDet, reversingCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The product of the two signed determinants is invariant even when
the affine isometry reverses orientation. -/
theorem sideDet_mul_affineIsometry (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b c x : Plane) :
    sideDet (e a) (e b) (e c) * sideDet (e a) (e b) (e x) =
      sideDet a b c * sideDet a b x := by
  obtain ⟨u, v, huv, he | he⟩ := affine_coordinate_classification e
  · have hdet (p q r : Plane) : sideDet (e p) (e q) (e r) = sideDet p q r := by
      rw [he p, he q, he r, sideDet_directCoordinates, huv, one_mul]
    rw [hdet, hdet]
  · have hdet (p q r : Plane) : sideDet (e p) (e q) (e r) = -sideDet p q r := by
      rw [he p, he q, he r, sideDet_reversingCoordinates, huv]
      ring
    rw [hdet, hdet, neg_mul_neg]

/-- A pair of square corners at distance one bounds a supporting line of
the square.  This is checked directly for all ordered corner pairs. -/
theorem sideDet_mul_nonneg_of_square_corners (i j : Fin 4) {c x : Plane}
    (hd : dist (corner i) (corner j) = 1)
    (hc : c ∈ unitSquare) (hx : x ∈ unitSquare) :
    0 ≤ sideDet (corner i) (corner j) c * sideDet (corner i) (corner j) x := by
  have hd' : dist (corner i) (corner j) ^ 2 = 1 := by rw [hd]; norm_num
  rw [plane_dist_sq] at hd'
  have h₀ : 0 ≤ c 0 * x 0 := mul_nonneg hc.1.1 hx.1.1
  have h₁ : 0 ≤ c 1 * x 1 := mul_nonneg hc.2.1 hx.2.1
  have h₂ : 0 ≤ (1 - c 0) * (1 - x 0) :=
    mul_nonneg (sub_nonneg.mpr hc.1.2) (sub_nonneg.mpr hx.1.2)
  have h₃ : 0 ≤ (1 - c 1) * (1 - x 1) :=
    mul_nonneg (sub_nonneg.mpr hc.2.2) (sub_nonneg.mpr hx.2.2)
  fin_cases i <;> fin_cases j <;> norm_num [corner, Fin.ext_iff] at hd'
  all_goals norm_num [corner, sideDet, Fin.ext_iff]
  all_goals nlinarith

/-- Every two points of a set are on the same closed side of an intrinsic
unit pair whenever that pair has an actual square-side placement. -/
theorem IsUnitSidePair.sideDet_mul_nonneg {P : Set Plane} {a b c x : Plane}
    (hab : IsUnitSidePair P a b) (hc : c ∈ P) (hx : x ∈ P) :
    0 ≤ sideDet a b c * sideDet a b x := by
  obtain ⟨_, _, hd, e, i, j, he, hea, heb⟩ := hab
  have hed : dist (corner i) (corner j) = 1 := by
    rw [← hea, ← heb, e.isometry.dist_eq]
    exact hd
  have h := sideDet_mul_nonneg_of_square_corners i j hed
    (he (mem_image_of_mem e hc)) (he (mem_image_of_mem e hx))
  rwa [← hea, ← heb, sideDet_mul_affineIsometry] at h

end Puzzling139335.UnitPairs
