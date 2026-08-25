import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Uniqueness of a non-axis-aligned rectangle's left-side contact

The source box is closed under mixing the coordinates of two points.  If two
image points lie on the left side of the square, the two mixed points have
nonnegative first coordinates whose sum is zero.  Nonzero matrix coefficients
then force the original source coordinates to agree.
-/

namespace Puzzling139335.RectangularHull

open Set PlaneIsometries

def axisBox (h : ℝ) : Set Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) h}

/-- Two zero values and nonnegative values at the two mixed coordinate pairs
force equality of both coordinates when neither coefficient vanishes. -/
theorem affine_cross_contact_unique {a b t x y x' y' : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : a * x + b * y + t = 0) (hq : a * x' + b * y' + t = 0)
    (hcross1 : 0 ≤ a * x + b * y' + t)
    (hcross2 : 0 ≤ a * x' + b * y + t) : x = x' ∧ y = y' := by
  have hcrosszero : a * x + b * y' + t = 0 := by
    linarith only [hp, hq, hcross1, hcross2]
  have hax : a * (x - x') = 0 := by nlinarith only [hcrosszero, hq]
  have hby : b * (y - y') = 0 := by nlinarith only [hp, hcrosszero]
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left ha),
    sub_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left hb)⟩

/-- A fitted rectangle with two nonzero first-row matrix coefficients meets
the square's left side in at most one point.  The statement also covers
degenerate or empty source boxes, so no height-positivity assumption is needed. -/
theorem affine_axisBox_left_contact_unique (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hfit : e '' axisBox h ⊆ unitSquare)
    (ha : linearMatrix e 0 0 ≠ 0) (hb : linearMatrix e 0 1 ≠ 0)
    {p q : Plane} (hp : p ∈ e '' axisBox h) (hq : q ∈ e '' axisBox h)
    (hp0 : p 0 = 0) (hq0 : q 0 = 0) : p = q := by
  rcases hp with ⟨x, hx, rfl⟩
  rcases hq with ⟨y, hy, rfl⟩
  have hcoord (r : Plane) : (e r) 0 =
      linearMatrix e 0 0 * r 0 + linearMatrix e 0 1 * r 1 + (e 0) 0 := by
    simpa using congrArg (fun z : Plane => z 0) (affine_apply_eq_matrix_coordinates e r)
  have hmix1 : !₂[x 0, y 1] ∈ axisBox h := ⟨hx.1, hy.2⟩
  have hmix2 : !₂[y 0, x 1] ∈ axisBox h := ⟨hy.1, hx.2⟩
  have hcross1 : 0 ≤ (e !₂[x 0, y 1]) 0 :=
    (hfit (mem_image_of_mem e hmix1)).1.1
  have hcross2 : 0 ≤ (e !₂[y 0, x 1]) 0 :=
    (hfit (mem_image_of_mem e hmix2)).1.1
  rw [hcoord] at hp0 hq0 hcross1 hcross2
  obtain ⟨hx_eq, hy_eq⟩ := affine_cross_contact_unique ha hb hp0 hq0
    (by simpa using hcross1) (by simpa using hcross2)
  exact congrArg e (plane_ext hx_eq hy_eq)

theorem affine_axisBox_left_contact_subsingleton (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hfit : e '' axisBox h ⊆ unitSquare)
    (ha : linearMatrix e 0 0 ≠ 0) (hb : linearMatrix e 0 1 ≠ 0) :
    (e '' axisBox h ∩ {p : Plane | p 0 = 0}).Subsingleton := by
  intro p hp q hq
  exact affine_axisBox_left_contact_unique e hfit ha hb hp.1 hq.1 hp.2 hq.2

end Puzzling139335.RectangularHull
