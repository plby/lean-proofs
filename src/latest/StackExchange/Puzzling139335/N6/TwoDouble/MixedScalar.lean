import StackExchange.Puzzling139335.AcuteCorner.Cone

/-!
# Scalar obstructions for the mixed six-incidence configuration

The normalized relative rotation is used explicitly. Its two square fits
force both singleton images away from the left side, and force an acute
support cone at the bottom-right corner. The scalar product of the opposite
corners of the lower half-square then locates the source vertex at one of
those endpoints. The exceptional midpoint placement is excluded by a strict
endpoint-height inequality.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.MixedScalar

noncomputable section

/-- The relative proper motion between the two singleton copies. -/
def rotation (s c : ℝ) (p : Plane) : Plane :=
  !₂[1 + s - s * p 0 - c * p 1, 1 - c + c * p 0 - s * p 1]

/-- The midpoint of the left side of the normalized square. -/
def leftMidpoint : Plane := !₂[(0 : ℝ), (1 / 2 : ℝ)]

@[simp] theorem rotation_zero (s c : ℝ) (p : Plane) :
    rotation s c p 0 = 1 + s - s * p 0 - c * p 1 := rfl

@[simp] theorem rotation_one (s c : ℝ) (p : Plane) :
    rotation s c p 1 = 1 - c + c * p 0 - s * p 1 := rfl

@[simp] theorem leftMidpoint_zero : leftMidpoint 0 = 0 := rfl

@[simp] theorem leftMidpoint_one : leftMidpoint 1 = (1 / 2 : ℝ) := rfl

/-- Two of the four coordinate inequalities of the rotated square fit. -/
theorem rotation_constraints {s c : ℝ} {p : Plane}
    (hfit : rotation s c p ∈ unitSquare) :
    s ≤ s * p 0 + c * p 1 ∧ c - 1 ≤ c * p 0 - s * p 1 := by
  change (0 ≤ 1 + s - s * p 0 - c * p 1 ∧
      1 + s - s * p 0 - c * p 1 ≤ 1) ∧
    (0 ≤ 1 - c + c * p 0 - s * p 1 ∧
      1 - c + c * p 0 - s * p 1 ≤ 1) at hfit
  constructor <;> linarith only [hfit.1.2, hfit.2.1]

/-- The two linear constraints combine to eliminate the second coordinate. -/
theorem coordinate_lower_bound {s c x y : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1)
    (hfirst : s ≤ s * x + c * y) (hsecond : c - 1 ≤ c * x - s * y) :
    1 - c ≤ x := by
  calc
    1 - c = s * s + c * (c - 1) := by nlinarith only [hcircle]
    _ ≤ s * (s * x + c * y) + c * (c * x - s * y) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hs)
        (mul_le_mul_of_nonneg_left hsecond hc)
    _ = (s ^ 2 + c ^ 2) * x := by ring
    _ = x := by rw [hcircle, one_mul]

/-- The rotated square fit forces a uniform lower bound on the source's
first coordinate; no hypothesis on the source point's square fit is needed. -/
theorem rotation_fit_lower_bound {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) {p : Plane}
    (hfit : rotation s c p ∈ unitSquare) : 1 - c ≤ p 0 := by
  obtain ⟨hfirst, hsecond⟩ := rotation_constraints hfit
  exact coordinate_lower_bound hs hc hcircle hfirst hsecond

/-- Every point of the rotated square has the same lower bound. This gives
the separation of the second singleton directly, without conjugation. -/
theorem rotation_image_lower_bound {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    {p : Plane} (hp : p ∈ unitSquare) : 1 - c ≤ rotation s c p 0 := by
  change (0 ≤ p 0 ∧ p 0 ≤ 1) ∧ (0 ≤ p 1 ∧ p 1 ≤ 1) at hp
  have hfirst := mul_le_mul_of_nonneg_left hp.1.2 hs
  have hsecond := mul_le_mul_of_nonneg_left hp.2.2 hc
  change 1 - c ≤ 1 + s - s * p 0 - c * p 1
  linarith only [hfirst, hsecond]

/-- A nonzero first-quadrant sine gives strictly positive separation. -/
theorem one_sub_cos_pos {s c : ℝ} (hs : 0 < s) (_hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) : 0 < 1 - c := by
  have hss : 0 < s ^ 2 := sq_pos_of_pos hs
  nlinarith only [hss, hcircle]

theorem rotation_fit_first_pos {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) {p : Plane}
    (hfit : rotation s c p ∈ unitSquare) : 0 < p 0 :=
  lt_of_lt_of_le (one_sub_cos_pos hs hc hcircle)
    (rotation_fit_lower_bound hs.le hc hcircle hfit)

theorem rotation_image_first_pos {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) {p : Plane}
    (hp : p ∈ unitSquare) : 0 < rotation s c p 0 :=
  lt_of_lt_of_le (one_sub_cos_pos hs hc hcircle)
    (rotation_image_lower_bound hs.le hc hp)

/-- The visual scalar product of opposite corners in a rectangle is
nonpositive at every point of that rectangle. -/
theorem rectangle_dot_nonpos {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hyhalf : y ≤ 1 / 2) :
    -x * (1 - x) + y * (y - 1 / 2) ≤ 0 := by
  nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx1),
    mul_nonneg hy0 (sub_nonneg.mpr hyhalf)]

theorem rectangle_visual_dot_nonpos {p : Plane} (hp : p ∈ unitSquare)
    (hyhalf : p 1 ≤ 1 / 2) :
    AcuteCorner.dot (corner 1 - p) (leftMidpoint - p) ≤ 0 := by
  calc
    AcuteCorner.dot (corner 1 - p) (leftMidpoint - p) =
        -p 0 * (1 - p 0) + p 1 * (p 1 - 1 / 2) := by
      simp [AcuteCorner.dot, corner, leftMidpoint]
      ring
    _ ≤ 0 := rectangle_dot_nonpos hp.1.1 hp.1.2 hp.2.1 hyhalf

/-- A nonzero vector in the acute cone between `(0,1)` and `(-c,s)`
has positive second coordinate. -/
theorem acute_cone_second_pos {s c x y : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hx : x ≤ 0) (hcone : 0 ≤ s * x + c * y) (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < y := by
  have hsx : s * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hx
  have hcy : 0 ≤ c * y := by linarith only [hcone, hsx]
  have hy : 0 ≤ y := (mul_nonneg_iff_of_pos_left hc).mp hcy
  by_contra hnot
  have hyzero : y = 0 := le_antisymm (le_of_not_gt hnot) hy
  have hxzero : x = 0 := by
    have hsx' : 0 ≤ s * x := by simpa only [hyzero, mul_zero, add_zero] using hcone
    exact le_antisymm hx ((mul_nonneg_iff_of_pos_left hs).mp hsx')
  rcases hne with hne | hne
  · exact hne hxzero
  · exact hne hyzero

/-- Two nonzero vectors in this explicit cone have strictly positive
scalar product. No abstract angle assumption is used. -/
theorem acute_cone_dot_pos {s c x y u v : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hx : x ≤ 0) (hu : u ≤ 0)
    (hxy : 0 ≤ s * x + c * y) (huv : 0 ≤ s * u + c * v)
    (hxyne : x ≠ 0 ∨ y ≠ 0) (huvne : u ≠ 0 ∨ v ≠ 0) :
    0 < x * u + y * v := by
  have hy := acute_cone_second_pos hs hc hx hxy hxyne
  have hv := acute_cone_second_pos hs hc hu huv huvne
  exact add_pos_of_nonneg_of_pos (mul_nonneg_of_nonpos_of_nonpos hx hu)
    (mul_pos hy hv)

private theorem point_ne_corner_coordinates {p : Plane} (hp : p ≠ corner 1) :
    p 0 - 1 ≠ 0 ∨ p 1 ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  apply hp
  ext i
  fin_cases i
  · simpa [corner] using sub_eq_zero.mp h.1
  · simpa [corner] using h.2

/-- Two square containments give the strict acute-cone product for any two
points other than the bottom-right corner. -/
theorem two_square_fits_dot_pos {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    {p q : Plane} (hp : p ∈ unitSquare) (hq : q ∈ unitSquare)
    (hFp : rotation s c p ∈ unitSquare) (hFq : rotation s c q ∈ unitSquare)
    (hpne : p ≠ corner 1) (hqne : q ≠ corner 1) :
    0 < AcuteCorner.dot (p - corner 1) (q - corner 1) := by
  have hpcone : 0 ≤ s * (p 0 - 1) + c * p 1 := by
    linarith only [(rotation_constraints hFp).1]
  have hqcone : 0 ≤ s * (q 0 - 1) + c * q 1 := by
    linarith only [(rotation_constraints hFq).1]
  have h := acute_cone_dot_pos hs hc (sub_nonpos.mpr hp.1.2)
    (sub_nonpos.mpr hq.1.2) hpcone hqcone
    (point_ne_corner_coordinates hpne) (point_ne_corner_coordinates hqne)
  simpa [AcuteCorner.dot, corner] using h

/-- In an actual lower-half-square source placement, the vertex sent to the
acute bottom-right corner must be one of the two opposite rectangle corners.
The supporting cone is derived from the two square fits. -/
theorem source_vertex_is_endpoint {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    {P : Set Plane} (hP : P ⊆ unitSquare) (hhalf : ∀ p ∈ P, p 1 ≤ 1 / 2)
    (ha : corner 1 ∈ P) (hM : leftMidpoint ∈ P) {b : Plane} (hb : b ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heb : e b = corner 1)
    (hefit : e '' P ⊆ unitSquare)
    (hFfit : rotation s c '' (e '' P) ⊆ unitSquare) :
    b = corner 1 ∨ b = leftMidpoint := by
  by_contra h
  simp only [not_or] at h
  have heane : e (corner 1) ≠ corner 1 := by
    intro heq
    exact h.1 (e.injective (heb.trans heq.symm))
  have heMne : e leftMidpoint ≠ corner 1 := by
    intro heq
    exact h.2 (e.injective (heb.trans heq.symm))
  have hea := mem_image_of_mem e ha
  have heM := mem_image_of_mem e hM
  have hpos := two_square_fits_dot_pos hs hc (hefit hea) (hefit heM)
    (hFfit (mem_image_of_mem (rotation s c) hea))
    (hFfit (mem_image_of_mem (rotation s c) heM)) heane heMne
  have hinvariant := AcuteCorner.affine_dot_sub e (corner 1) leftMidpoint b
  rw [heb] at hinvariant
  rw [hinvariant] at hpos
  exact (not_lt_of_ge (rectangle_visual_dot_nonpos (hP hb) (hhalf b hb))) hpos

/-- The remaining midpoint placement overflows the unit square: the
unit-circle identity and the source slope bound force height greater than one. -/
theorem endpoint_overflow {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hcircle : s ^ 2 + c ^ 2 = 1) (hslope : s ≤ c / 2) :
    1 < c + s / 2 := by
  have hfactor : 0 < c - 3 * s / 4 := by linarith only [hc, hslope]
  have hproduct := mul_pos hs hfactor
  have hheight : 0 < c + s / 2 := by linarith only [hs, hc]
  by_contra hnot
  have hsquare := mul_self_le_mul_self hheight.le (le_of_not_gt hnot)
  nlinarith only [hcircle, hproduct, hsquare]

/-- The explicitly located oblique endpoint cannot lie in the square. -/
theorem oblique_endpoint_not_mem_square {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hcircle : s ^ 2 + c ^ 2 = 1) (hslope : s ≤ c / 2) :
    (!₂[1 - c / 2 + s, s / 2 + c] : Plane) ∉ unitSquare := by
  intro hp
  have h := endpoint_overflow hs hc hcircle hslope
  have hy : s / 2 + c ≤ 1 := hp.2.2
  linarith only [h, hy]

/-- The vertical alternative puts an endpoint on the forbidden left side. -/
theorem vertical_endpoint_not_fit {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) :
    rotation s c leftMidpoint ∉ unitSquare := by
  intro hfit
  have h := rotation_fit_first_pos hs hc hcircle hfit
  norm_num only [leftMidpoint_zero] at h

/-- The only nonnegative unit-circle point below both endpoint bounds is
the vertical axis point. -/
theorem unit_circle_cap_rigidity {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) (hslope : s ≤ c / 2)
    (hheight : c + s / 2 ≤ 1) : s = 0 ∧ c = 1 := by
  have hs0 : s = 0 := by
    by_contra hne
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hne)
    have hcpos : 0 < c := by linarith only [hspos, hslope]
    exact (not_le_of_gt (endpoint_overflow hspos hcpos hcircle hslope)) hheight
  exact ⟨hs0, by nlinarith only [hcircle, hc, hs0]⟩

/-- The midpoint of the bottom side. -/
def bottomMidpoint : Plane := !₂[(1 / 2 : ℝ), (0 : ℝ)]

/-- Fitting the three vertices of the right triangle with legs `1` and
`1/2`, with its short-leg endpoint at the bottom-right square corner,
forces one of two axis alignments. This uses actual affine isometries and
does not assume either leg is a boundary segment. -/
theorem midpoint_placement_axes (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (heM : e leftMidpoint = corner 1)
    (her : e 0 ∈ unitSquare) (hea : e (corner 1) ∈ unitSquare) :
    e (corner 1) = leftMidpoint ∨ e 0 = bottomMidpoint := by
  obtain ⟨k, l, hkl, he | he⟩ := PlaneIsometries.affine_coordinate_classification e
  · have hMformula := he leftMidpoint
    rw [heM] at hMformula
    have hM0 : 1 = -(l / 2) + e 0 0 := by
      simpa [PlaneIsometries.directCoordinates, leftMidpoint, corner, div_eq_mul_inv]
        using congrArg (fun p : Plane => p 0) hMformula
    have hM1 : 0 = k / 2 + e 0 1 := by
      simpa [PlaneIsometries.directCoordinates, leftMidpoint, corner, div_eq_mul_inv]
        using congrArg (fun p : Plane => p 1) hMformula
    have ha0 : e (corner 1) 0 = k + e 0 0 := by
      simpa [PlaneIsometries.directCoordinates, corner]
        using congrArg (fun p : Plane => p 0) (he (corner 1))
    have ha1 : e (corner 1) 1 = l + e 0 1 := by
      simpa [PlaneIsometries.directCoordinates, corner]
        using congrArg (fun p : Plane => p 1) (he (corner 1))
    have hk0 : 0 ≤ -k := by linarith only [hM1, her.2.1]
    have hl0 : 0 ≤ -l := by linarith only [hM0, her.1.2]
    have hslope : -l ≤ -k / 2 := by linarith only [ha1, hM1, hea.2.1]
    have hheight : -k + -l / 2 ≤ 1 := by linarith only [ha0, hM0, hea.1.1]
    obtain ⟨hl, hk⟩ := unit_circle_cap_rigidity hl0 hk0
      (by nlinarith only [hkl]) hslope hheight
    left
    ext i
    fin_cases i
    · change e (corner 1) 0 = 0
      linarith only [ha0, hM0, hl, hk]
    · change e (corner 1) 1 = 1 / 2
      linarith only [ha1, hM1, hl, hk]
  · have hMformula := he leftMidpoint
    rw [heM] at hMformula
    have hM0 : 1 = l / 2 + e 0 0 := by
      simpa [PlaneIsometries.reversingCoordinates, leftMidpoint, corner, div_eq_mul_inv]
        using congrArg (fun p : Plane => p 0) hMformula
    have hM1 : 0 = -(k / 2) + e 0 1 := by
      simpa [PlaneIsometries.reversingCoordinates, leftMidpoint, corner, div_eq_mul_inv]
        using congrArg (fun p : Plane => p 1) hMformula
    have ha0 : e (corner 1) 0 = k + e 0 0 := by
      simpa [PlaneIsometries.reversingCoordinates, corner]
        using congrArg (fun p : Plane => p 0) (he (corner 1))
    have ha1 : e (corner 1) 1 = l + e 0 1 := by
      simpa [PlaneIsometries.reversingCoordinates, corner]
        using congrArg (fun p : Plane => p 1) (he (corner 1))
    have hk0 : 0 ≤ k := by linarith only [hM1, her.2.1]
    have hl0 : 0 ≤ l := by linarith only [hM0, her.1.2]
    have hslope : k ≤ l / 2 := by linarith only [ha0, hM0, hea.1.2]
    have hheight : l + k / 2 ≤ 1 := by linarith only [ha1, hM1, hea.2.2]
    obtain ⟨hk, hl⟩ := unit_circle_cap_rigidity hk0 hl0 hkl hslope hheight
    right
    ext i
    fin_cases i
    · change e 0 0 = 1 / 2
      linarith only [hM0, hk, hl]
    · change e 0 1 = 0
      linarith only [hM1, hk, hl]

/-- The second axis alignment also violates the rotated square fit. -/
theorem bottom_midpoint_not_fit {s c : ℝ} (hs : 0 < s) :
    rotation s c bottomMidpoint ∉ unitSquare := by
  intro hfit
  have hfirst := (rotation_constraints hfit).1
  simp [bottomMidpoint] at hfirst
  linarith only [hs, hfirst]

/-- The exceptional source midpoint is impossible using just three actual
source points and the two square fits. No supporting-ray classification is
required. -/
theorem midpoint_source_vertex_impossible {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) {P : Set Plane}
    (hr : (0 : Plane) ∈ P) (ha : corner 1 ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heM : e leftMidpoint = corner 1)
    (hefit : e '' P ⊆ unitSquare)
    (hFfit : rotation s c '' (e '' P) ⊆ unitSquare) : False := by
  have her := mem_image_of_mem e hr
  have hea := mem_image_of_mem e ha
  rcases midpoint_placement_axes e heM (hefit her) (hefit hea) with heaxis | heaxis
  · have hfit := hFfit (mem_image_of_mem (rotation s c) hea)
    rw [heaxis] at hfit
    exact vertical_endpoint_not_fit hs hc hcircle hfit
  · have hfit := hFfit (mem_image_of_mem (rotation s c) her)
    rw [heaxis] at hfit
    exact bottom_midpoint_not_fit hs hfit

/-- Complete scalar and affine-placement exclusion of the normalized
mixed-singleton case, once the source's left midpoint has been established.
All support information is derived from concrete square containments. -/
theorem no_normalized_mixed_placement {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hcircle : s ^ 2 + c ^ 2 = 1)
    {P : Set Plane} (hP : P ⊆ unitSquare) (hhalf : ∀ p ∈ P, p 1 ≤ 1 / 2)
    (hr : (0 : Plane) ∈ P) (ha : corner 1 ∈ P) (hM : leftMidpoint ∈ P)
    {b : Plane} (hb : b ∈ P) (hbne : b ≠ corner 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heb : e b = corner 1)
    (hefit : e '' P ⊆ unitSquare)
    (hFfit : rotation s c '' (e '' P) ⊆ unitSquare) : False := by
  have hbM : b = leftMidpoint :=
    (source_vertex_is_endpoint hs hc hP hhalf ha hM hb e heb hefit hFfit).resolve_left hbne
  subst b
  exact midpoint_source_vertex_impossible hs hc.le hcircle hr ha e heb hefit hFfit

end

end Puzzling139335.N6.TwoDouble.MixedScalar
