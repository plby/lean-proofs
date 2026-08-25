import StackExchange.Puzzling139335.PlaneIsometries
import StackExchange.Puzzling139335.SquareGeometry
import StackExchange.Puzzling139335.N7Geometry.Defs

/-!
# The actual third placement after the repeated pair is normalized

The source's two known points are the bottom square corners.  A third
source point lies in the lower half-square and is sent to the bottom-right
corner by a placement sending the source bottom-right corner to the
top-right corner.  Fitting the source bottom-left point determines the
orientation of that placement.  The resulting narrow support cone follows
from square containment of the actual image, not from an angle hypothesis.
-/

open Set

namespace Puzzling139335.N7

open PlaneIsometries

noncomputable section

/-- The reflection placing the source pair on the right square side. -/
def thirdMap (c s : ℝ) (p : Plane) : Plane :=
  !₂[1 - s + s * p 0 + c * p 1, 1 - c + c * p 0 - s * p 1]

theorem source_parameters_unit (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1) :
    (1 - b 0) ^ 2 + b 1 ^ 2 = 1 := by
  have hd : dist b (corner 1) ^ 2 = 1 := by
    calc
      dist b (corner 1) ^ 2 = dist (e b) (e (corner 1)) ^ 2 := by
        rw [e.isometry.dist_eq]
      _ = 1 := by rw [ha, hb, plane_dist_sq]; norm_num [corner, Fin.ext_iff]
  norm_num [plane_dist_sq, corner, Fin.ext_iff] at hd
  nlinarith only [hd]

theorem source_parameters_positive (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (hbsquare : b ∈ unitSquare) (hhalf : b 1 ≤ (1 / 2 : ℝ))
    (hne : b ≠ corner 0)
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1) :
    0 < b 1 ∧ 0 < 1 - b 0 := by
  have hunit := source_parameters_unit e ha hb
  rcases hbsquare with ⟨⟨hx0, hx1⟩, ⟨hy0, _⟩⟩
  have hspos : 0 < b 1 := by
    by_contra hs
    have hy : b 1 = 0 := by linarith only [hy0, hs]
    have hx : b 0 = 0 := by nlinarith only [hunit, hy, hx0, hx1]
    apply hne
    ext k
    fin_cases k <;> simp [corner, Fin.ext_iff, hx, hy]
  refine ⟨hspos, ?_⟩
  have hc0 : 0 ≤ 1 - b 0 := sub_nonneg.mpr hx1
  by_contra hc
  have hceq : 1 - b 0 = 0 := by linarith only [hc0, hc]
  nlinarith only [hunit, hceq, hy0, hhalf]

private theorem direct_parameters {a t c s : ℝ}
    (hat : a ^ 2 + t ^ 2 = 1) (hcs : c ^ 2 + s ^ 2 = 1)
    (hprod : t * c - a * s = 1) : a = -s ∧ t = c := by
  have hsum : (a + s) ^ 2 + (t - c) ^ 2 = 0 := by
    nlinarith only [hat, hcs, hprod]
  have ha : (a + s) ^ 2 = 0 := by
    nlinarith only [hsum, sq_nonneg (t - c), sq_nonneg (a + s)]
  have ht : (t - c) ^ 2 = 0 := by
    nlinarith only [hsum, sq_nonneg (t - c), sq_nonneg (a + s)]
  exact ⟨add_eq_zero_iff_eq_neg.mp (sq_eq_zero_iff.mp ha), sub_eq_zero.mp (sq_eq_zero_iff.mp ht)⟩

private theorem reversing_parameters {a t c s : ℝ}
    (hat : a ^ 2 + t ^ 2 = 1) (hcs : c ^ 2 + s ^ 2 = 1)
    (hprod : t * c + a * s = 1) : a = s ∧ t = c := by
  have hsum : (a - s) ^ 2 + (t - c) ^ 2 = 0 := by
    nlinarith only [hat, hcs, hprod]
  have ha : (a - s) ^ 2 = 0 := by
    nlinarith only [hsum, sq_nonneg (t - c), sq_nonneg (a - s)]
  have ht : (t - c) ^ 2 = 0 := by
    nlinarith only [hsum, sq_nonneg (t - c), sq_nonneg (a - s)]
  exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp ha), sub_eq_zero.mp (sq_eq_zero_iff.mp ht)⟩

/-- The endpoint images and the fit of the third source point force the
orientation-reversing formula. -/
theorem third_placement_formula (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (hbsquare : b ∈ unitSquare) (hhalf : b 1 ≤ (1 / 2 : ℝ))
    (hne : b ≠ corner 0)
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1)
    (hzero : e (corner 0) ∈ unitSquare) :
    ∀ p, e p = thirdMap (1 - b 0) (b 1) p := by
  have hunit := source_parameters_unit e ha hb
  have hspos := (source_parameters_positive e hbsquare hhalf hne ha hb).1
  have hezero : e 0 ∈ unitSquare := by
    have hcorner : corner 0 = (0 : Plane) := by
      ext k
      fin_cases k <;> norm_num [corner, Fin.ext_iff]
    simpa only [hcorner] using hzero
  obtain ⟨a, t, hat, hform | hform⟩ := affine_coordinate_classification e
  · have hx := congrArg (fun p : Plane => p 0) (hform (corner 1))
    have hy := congrArg (fun p : Plane => p 1) (hform (corner 1))
    have hby := congrArg (fun p : Plane => p 1) (hform b)
    rw [ha] at hx hy
    norm_num [directCoordinates, corner, Fin.ext_iff] at hx hy
    norm_num [hb, directCoordinates, corner, Fin.ext_iff] at hby
    have hprod : t * (1 - b 0) - a * b 1 = 1 := by
      nlinarith only [hy, hby]
    have hap := (direct_parameters hat hunit hprod).1
    have hfit := hezero.1.2
    exfalso
    linarith only [hx, hap, hfit, hspos]
  · have hx := congrArg (fun p : Plane => p 0) (hform (corner 1))
    have hy := congrArg (fun p : Plane => p 1) (hform (corner 1))
    have hby := congrArg (fun p : Plane => p 1) (hform b)
    rw [ha] at hx hy
    norm_num [reversingCoordinates, corner, Fin.ext_iff] at hx hy
    norm_num [hb, reversingCoordinates, corner, Fin.ext_iff] at hby
    have hprod : t * (1 - b 0) + a * b 1 = 1 := by
      nlinarith only [hy, hby]
    obtain ⟨hap, htp⟩ := reversing_parameters hat hunit hprod
    have hxzero : e 0 0 = 1 - b 1 := by linarith only [hx, hap]
    have hyzero : e 0 1 = b 0 := by linarith only [hy, htp]
    intro p
    rw [hform, hap, htp]
    ext k
    fin_cases k <;> simp [reversingCoordinates, thirdMap, hxzero, hyzero] <;> ring

/-- The narrow cone at the source bottom-right point follows directly
from fitting the actual third image in the square. -/
theorem third_placement_support {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (hbsquare : b ∈ unitSquare) (hhalf : b 1 ≤ (1 / 2 : ℝ))
    (hne : b ≠ corner 0)
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1)
    (hzero : e (corner 0) ∈ unitSquare) (hfit : e '' P ⊆ unitSquare) :
    ∀ p ∈ P, (1 - b 0) * p 1 ≤ b 1 * (1 - p 0) := by
  intro p hp
  have hxp := (hfit (mem_image_of_mem e hp)).1.2
  rw [third_placement_formula e hbsquare hhalf hne ha hb hzero] at hxp
  change 1 - b 1 + b 1 * p 0 + (1 - b 0) * p 1 ≤ 1 at hxp
  nlinarith only [hxp]

/-- The endpoint reaching height one half fixes the cosine parameter to
the value used in the checked final obstruction. -/
theorem source_cosine_of_half_height (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (hbsquare : b ∈ unitSquare) (hheight : b 1 = (1 / 2 : ℝ))
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1) :
    1 - b 0 = N7Geometry.c := by
  have hunit := source_parameters_unit e ha hb
  have hc0 : 0 ≤ 1 - b 0 := sub_nonneg.mpr hbsquare.1.2
  have hc30 : 0 ≤ N7Geometry.c := by
    dsimp [N7Geometry.c]
    positivity
  apply (sq_eq_sq₀ hc0 hc30).mp
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  dsimp [N7Geometry.c]
  nlinarith only [hunit, hheight, hsqrt]

/-- At the forced endpoint height, the actual placement is exactly the
map `N7Geometry.T`; equality is proved point by point. -/
theorem third_placement_eq_T (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (hbsquare : b ∈ unitSquare) (hheight : b 1 = (1 / 2 : ℝ))
    (hne : b ≠ corner 0)
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1)
    (hzero : e (corner 0) ∈ unitSquare) : ∀ p, e p = N7Geometry.T p := by
  have hhalf : b 1 ≤ (1 / 2 : ℝ) := hheight.le
  have hcos := source_cosine_of_half_height e hbsquare hheight ha hb
  intro p
  rw [third_placement_formula e hbsquare hhalf hne ha hb hzero, hcos, hheight]
  ext k
  fin_cases k <;> simp [thirdMap, N7Geometry.T, N7Geometry.u] <;> ring

end

end Puzzling139335.N7
