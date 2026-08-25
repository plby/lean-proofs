import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Defs

/-!
# Oblique supporting faces of sets symmetric in both coordinate axes

An endpoint maximizing a normal with nonzero coordinate must lie on the
corresponding side of each symmetry axis.  Reflection and box containment
then bound the segment's coordinate spans by half the box dimensions.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

def horizontalAbout (cy : ℝ) (p : Plane) : Plane := !₂[p 0, 2 * cy - p 1]

def verticalAbout (cx : ℝ) (p : Plane) : Plane := !₂[2 * cx - p 0, p 1]

private theorem abs_sub_le_half_width {a b c l r n : ℝ}
    (hn : n ≠ 0) (ha : 0 ≤ n * (a - c)) (hb : 0 ≤ n * (b - c))
    (haL : l ≤ a) (haR : a ≤ r) (hbL : l ≤ b) (hbR : b ≤ r)
    (haL' : l ≤ 2 * c - a) (haR' : 2 * c - a ≤ r)
    (hbL' : l ≤ 2 * c - b) (hbR' : 2 * c - b ≤ r) :
    |a - b| ≤ (r - l) / 2 := by
  rcases lt_or_gt_of_ne hn with hn | hn
  · have ha' : a ≤ c := by nlinarith [ha]
    have hb' : b ≤ c := by nlinarith [hb]
    rw [abs_le]
    constructor <;> linarith
  · have ha' : c ≤ a := by nlinarith [ha]
    have hb' : c ≤ b := by nlinarith [hb]
    rw [abs_le]
    constructor <;> linarith

/-- A nonvertical supporting normal and vertical symmetry halve the possible
horizontal span of an actual supporting segment. -/
theorem SupportsSegment.abs_horizontal_span_le_half {K : Set Plane}
    {nx ny cx l r : ℝ} {a b : Plane} (h : SupportsSegment K nx ny a b)
    (hnx : nx ≠ 0) (hsym : MapsTo (verticalAbout cx) K K)
    (hbox : ∀ p ∈ K, l ≤ p 0 ∧ p 0 ≤ r) :
    |a 0 - b 0| ≤ (r - l) / 2 := by
  have hsa := h.left_support (verticalAbout cx a) (hsym h.left_mem)
  have hsb := h.right_support (verticalAbout cx b) (hsym h.right_mem)
  simp only [supportValue, verticalAbout, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hsa hsb
  have ha : 0 ≤ nx * (a 0 - cx) := by nlinarith only [hsa]
  have hb : 0 ≤ nx * (b 0 - cx) := by nlinarith only [hsb]
  have hba := hbox a h.left_mem
  have hbb := hbox b h.right_mem
  have hba' := hbox (verticalAbout cx a) (hsym h.left_mem)
  have hbb' := hbox (verticalAbout cx b) (hsym h.right_mem)
  exact abs_sub_le_half_width hnx ha hb hba.1 hba.2 hbb.1 hbb.2
    hba'.1 hba'.2 hbb'.1 hbb'.2

/-- A nonhorizontal supporting normal and horizontal symmetry halve the
possible vertical span of an actual supporting segment. -/
theorem SupportsSegment.abs_vertical_span_le_half {K : Set Plane}
    {nx ny cy l r : ℝ} {a b : Plane} (h : SupportsSegment K nx ny a b)
    (hny : ny ≠ 0) (hsym : MapsTo (horizontalAbout cy) K K)
    (hbox : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ r) :
    |a 1 - b 1| ≤ (r - l) / 2 := by
  have hsa := h.left_support (horizontalAbout cy a) (hsym h.left_mem)
  have hsb := h.right_support (horizontalAbout cy b) (hsym h.right_mem)
  simp only [supportValue, horizontalAbout, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hsa hsb
  have ha : 0 ≤ ny * (a 1 - cy) := by nlinarith only [hsa]
  have hb : 0 ≤ ny * (b 1 - cy) := by nlinarith only [hsb]
  have hba := hbox a h.left_mem
  have hbb := hbox b h.right_mem
  have hba' := hbox (horizontalAbout cy a) (hsym h.left_mem)
  have hbb' := hbox (horizontalAbout cy b) (hsym h.right_mem)
  exact abs_sub_le_half_width hny ha hb hba.1 hba.2 hbb.1 hbb.2
    hba'.1 hba'.2 hbb'.1 hbb'.2

/-- No set inside the unit square, symmetric in a horizontal and a vertical
line, has an oblique supporting segment of unit length.  Convexity and a
strict height bound are not needed for this special obstruction. -/
theorem no_unit_oblique_support_of_axis_symmetries {K : Set Plane}
    {nx ny cx cy : ℝ} {a b : Plane} (h : SupportsSegment K nx ny a b)
    (hnx : nx ≠ 0) (hny : ny ≠ 0)
    (hV : MapsTo (verticalAbout cx) K K)
    (hH : MapsTo (horizontalAbout cy) K K)
    (hK : K ⊆ unitSquare) (hlen : dist a b = 1) : False := by
  have hx := h.abs_horizontal_span_le_half hnx hV
    (fun p hp => (hK hp).1)
  have hy := h.abs_vertical_span_le_half hny hH
    (fun p hp => (hK hp).2)
  have hx2 : (a 0 - b 0) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hh : 0 ≤ |a 0 - b 0| := abs_nonneg _
    have hs := sq_abs (a 0 - b 0)
    norm_num at hx
    nlinarith
  have hy2 : (a 1 - b 1) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hh : 0 ≤ |a 1 - b 1| := abs_nonneg _
    have hs := sq_abs (a 1 - b 1)
    norm_num at hy
    nlinarith
  have hd := plane_dist_sq a b
  rw [hlen] at hd
  nlinarith [hx2, hy2]

end Puzzling139335.N4MiddleInvolutions.FaceBounds
