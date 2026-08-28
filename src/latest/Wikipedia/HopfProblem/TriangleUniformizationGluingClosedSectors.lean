import Wikipedia.HopfProblem.SpecialPeriodsTriangleTiling

/-!
# Closed cyclic sectors and their boundary-inclusive exclusions

The closed circular double has weak excluded sectors for the two cyclic
factors. Positive imaginary part separates these weak exclusions strictly:
each lies in the other factor's open sector. This retains the strict
ping-pong separation needed when a group word takes a closed boundary
point back to the closed polygon.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The closed cyclic sector at the order-three vertex. -/
def closedFirstSector : Set ℍ := {z | z.re ≤ -(1 / 2) ∧ 1 ≤ ‖(z : ℂ)‖}

/-- The closed cyclic sector at the order-four vertex. -/
def closedSecondSector : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖}

/-- The complement of the open first sector, including its boundary. -/
def firstWeakExcluded : Set ℍ := {z | -(1 / 2) ≤ z.re ∨ ‖(z : ℂ)‖ ≤ 1}

/-- The complement of the open second sector, including its boundary. -/
def secondWeakExcluded : Set ℍ :=
  {z | z.re ≤ stripLeft ∨ ‖(z : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight}

/-- The closed polygon obtained by doubling across the circular side. -/
def circularDoubleRegion : Set ℍ := closedFirstSector ∩ closedSecondSector

theorem closedFirstSector_isClosed : IsClosed closedFirstSector :=
  (isClosed_le continuous_re continuous_const).inter
    (isClosed_le continuous_const continuous_coe.norm)

theorem closedSecondSector_isClosed : IsClosed closedSecondSector :=
  (isClosed_le continuous_const continuous_re).inter
    (isClosed_le continuous_const (continuous_coe.sub continuous_const).norm)

theorem circularDoubleRegion_isClosed : IsClosed circularDoubleRegion :=
  closedFirstSector_isClosed.inter closedSecondSector_isClosed

theorem firstSector_subset_closedFirstSector : firstSector ⊆ closedFirstSector :=
  fun _ hz => ⟨hz.1.le, hz.2.le⟩

theorem secondSector_subset_closedSecondSector : secondSector ⊆ closedSecondSector :=
  fun _ hz => ⟨hz.1.le, hz.2.le⟩

theorem circularDoubleInterior_subset_circularDoubleRegion :
    circularDoubleInterior ⊆ circularDoubleRegion :=
  fun _ hz => ⟨firstSector_subset_closedFirstSector hz.1,
    secondSector_subset_closedSecondSector hz.2⟩

theorem firstExcluded_subset_firstWeakExcluded : firstExcluded ⊆ firstWeakExcluded := by
  intro z hz
  exact hz.imp le_of_lt le_of_lt

theorem secondExcluded_subset_secondWeakExcluded : secondExcluded ⊆ secondWeakExcluded := by
  intro z hz
  exact hz.imp le_of_lt le_of_lt

/-- Even the circular boundary of the first exclusion lies strictly to
the right of `Re z = -1`, because upper-half-plane points are not real. -/
theorem firstWeakExcluded_subset_pingPongOne : firstWeakExcluded ⊆ pingPongOne := by
  intro z hz
  change -1 < z.re
  rcases hz with hx | hn
  · linarith
  · have habs : |z.re| < ‖(z : ℂ)‖ :=
      Complex.abs_re_lt_norm.mpr z.im_ne_zero
    linarith [neg_le_abs z.re]

/-- The weak second exclusion is likewise strictly to the left of the
separating line, including along its circular boundary. -/
theorem secondWeakExcluded_subset_pingPongTwo : secondWeakExcluded ⊆ pingPongTwo := by
  intro z hz
  change z.re < -1
  rcases hz with hx | hn
  · exact hx.trans_lt stripLeft_lt_neg_one
  · have him : ((z : ℂ) - (stripLeft : ℂ)).im ≠ 0 := by
      simpa using z.im_ne_zero
    have habs := Complex.abs_re_lt_norm.mpr him
    have hr := le_abs_self (((z : ℂ) - (stripLeft : ℂ)).re)
    simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at habs hr
    linarith [stripLeft_add_stripRight]

theorem firstWeakExcluded_subset_secondSector : firstWeakExcluded ⊆ secondSector :=
  firstWeakExcluded_subset_pingPongOne.trans pingPongOne_subset_secondSector

theorem secondWeakExcluded_subset_firstSector : secondWeakExcluded ⊆ firstSector :=
  secondWeakExcluded_subset_pingPongTwo.trans pingPongTwo_subset_firstSector

theorem weakExcluded_disjoint : Disjoint firstWeakExcluded secondWeakExcluded :=
  pingPong_disjoint.mono firstWeakExcluded_subset_pingPongOne
    secondWeakExcluded_subset_pingPongTwo

theorem circularDoubleRegion_disjoint_firstExcluded :
    Disjoint circularDoubleRegion firstExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact (not_lt_of_ge hz.1.1) hx
  · exact (not_lt_of_ge hz.1.2) hn

theorem circularDoubleRegion_disjoint_secondExcluded :
    Disjoint circularDoubleRegion secondExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact (not_lt_of_ge hz.2.1) hx
  · exact (not_lt_of_ge hz.2.2) hn


/-- Every nonidentity first-generator power sends the closed first
sector to its weak exclusion; here the first power crosses the vertical side. -/
theorem generatorOne_closedFirstSector :
    MapsTo (fun z : ℍ => generatorOneSL • z) closedFirstSector firstWeakExcluded := by
  intro z hz
  left
  change -(1 / 2) ≤ (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hn : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2]
  simp only [← neg_div]
  apply (le_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im] at hn ⊢
  nlinarith

private theorem norm_add_one_le_norm_of_re_le_half (z : ℍ) (hz : z.re ≤ -(1 / 2)) :
    ‖(z : ℂ) + 1‖ ≤ ‖(z : ℂ)‖ := by
  have hsq : ‖(z : ℂ) + 1‖ ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

/-- The second power crosses the circular side, with equality allowed. -/
theorem generatorOne_sq_closedFirstSector :
    MapsTo (fun z : ℍ => (generatorOneSL ^ 2 : SL(2, ℝ)) • z)
      closedFirstSector firstWeakExcluded := by
  intro z hz
  right
  rw [generatorOneSL_sq_smul_coe]
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div]
  exact (div_le_one (norm_pos_iff.mpr z.ne_zero)).mpr
    (norm_add_one_le_norm_of_re_le_half z hz.1)

private def secondShift (z : ℍ) : ℂ := (z : ℂ) - (stripLeft : ℂ)

private theorem secondShift_re (z : ℍ) : (secondShift z).re = z.re - stripLeft := by
  simp [secondShift]

private theorem secondShift_add_real_ne_zero (z : ℍ) (a : ℝ) :
    secondShift z + (a : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [secondShift, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    sub_zero, add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem stripLeft_eq_neg_stripRight_sub_one :
    stripLeft = -stripRight - 1 := by
  linarith [stripLeft_add_stripRight]

private theorem width_eq_two_stripRight_add_one : width = 2 * stripRight + 1 := by
  unfold stripRight
  ring

private theorem stripRight_sq_complex : (stripRight : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, stripRight_sq]
  norm_num

private theorem generatorTwo_secondShift (z : ℍ) :
    secondShift (generatorTwoSL • z) =
      (stripRight : ℂ) * (secondShift z - stripRight) /
        (secondShift z + stripRight) := by
  have hd := secondShift_add_real_ne_zero z stripRight
  have hs := stripRight_sq_complex
  unfold secondShift at *
  rw [generatorTwoSL_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one, width_eq_two_stripRight_add_one] at *
  push_cast at *
  have he : (z : ℂ) + (2 * (stripRight : ℂ) + 1) =
      (z : ℂ) - (-(stripRight : ℂ) - 1) + stripRight := by ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem generatorTwo_sq_secondShift (z : ℍ) :
    secondShift ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) ^ 2 / secondShift z := by
  have hz : secondShift z ≠ 0 := by
    simpa using secondShift_add_real_ne_zero z 0
  have hd := secondShift_add_real_ne_zero z stripRight
  have hR : (stripRight : ℂ) ≠ 0 := by
    exact_mod_cast stripRight_pos.ne'
  rw [pow_two, mul_smul, generatorTwo_secondShift, generatorTwo_secondShift]
  field_simp [hz, hd, hR]
  ring

private theorem generatorTwo_cube_secondShift (z : ℍ) :
    secondShift ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) * (secondShift z + stripRight) /
        (secondShift z - stripRight) := by
  have hd : secondShift z - (stripRight : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg, sub_eq_add_neg] using
      secondShift_add_real_ne_zero z (-stripRight)
  have hs := stripRight_sq_complex
  unfold secondShift at *
  rw [generatorTwoSL_cube_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one, width_eq_two_stripRight_add_one] at *
  push_cast at *
  have he : (z : ℂ) + 1 =
      (z : ℂ) - (-(stripRight : ℂ) - 1) - stripRight := by ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem norm_sub_div_add_le_one {r : ℝ} (hr : 0 < r) {u : ℂ}
    (hu : 0 ≤ u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ ≤ 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 ≤ ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero, add_zero]
    nlinarith [mul_nonneg hr.le hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem re_add_div_sub_nonneg {r : ℝ} (hr : 0 < r) {u : ℂ}
    (hu : r ≤ ‖u‖) : 0 ≤ ((u + (r : ℂ)) / (u - (r : ℂ))).re := by
  have hsq : r ^ 2 ≤ Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [Complex.div_re, ← add_div]
  apply div_nonneg ?_ (Complex.normSq_nonneg _)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.add_im, Complex.sub_im, Complex.ofReal_im, add_zero, sub_zero]
  rw [Complex.normSq_apply] at hsq
  nlinarith

private theorem re_neg_sq_div_nonpos {r : ℝ} {u : ℂ}
    (hu : 0 ≤ u.re) : (-(r : ℂ) ^ 2 / u).re ≤ 0 := by
  have hnum : -(r ^ 2) * u.re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg r)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_nonpos_of_nonpos_of_nonneg hnum (Complex.normSq_nonneg u)

private theorem norm_sub_div_add_lt_one {r : ℝ} (hr : 0 < r) {u : ℂ}
    (hu : 0 < u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ < 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 < ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero, add_zero]
    nlinarith [mul_pos hr hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem re_add_div_sub_pos {r : ℝ} (hr : 0 < r) {u : ℂ}
    (hu : r < ‖u‖) : 0 < ((u + (r : ℂ)) / (u - (r : ℂ))).re := by
  have hd : u - (r : ℂ) ≠ 0 := by
    intro h
    have he : u = (r : ℂ) := sub_eq_zero.mp h
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hu
    exact lt_irrefl r hu
  have hsq : r ^ 2 < Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [Complex.div_re, ← add_div]
  apply div_pos ?_ (Complex.normSq_pos.mpr hd)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.add_im, Complex.sub_im, Complex.ofReal_im, add_zero, sub_zero]
  rw [Complex.normSq_apply] at hsq
  nlinarith

private theorem re_neg_sq_div_neg {r : ℝ} (hr : 0 < r) {u : ℂ}
    (hu : 0 < u.re) : (-(r : ℂ) ^ 2 / u).re < 0 := by
  have hd : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hnum : -(r ^ 2) * u.re < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hr)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_neg_of_neg_of_pos hnum (Complex.normSq_pos.mpr hd)


/-- The actual first power in coordinates translated by the second center's real part. -/
theorem generatorTwo_shift (z : ℍ) :
    ((generatorTwoSL • z : ℍ) : ℂ) - (stripLeft : ℂ) =
      (stripRight : ℂ) * ((z : ℂ) - (stripLeft : ℂ) - stripRight) /
        ((z : ℂ) - (stripLeft : ℂ) + stripRight) :=
  generatorTwo_secondShift z

/-- The actual second power in the same translated coordinates. -/
theorem generatorTwo_sq_shift (z : ℍ) :
    (((generatorTwoSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) - (stripLeft : ℂ) =
      -(stripRight : ℂ) ^ 2 / ((z : ℂ) - (stripLeft : ℂ)) :=
  generatorTwo_sq_secondShift z

/-- The actual third power in the same translated coordinates. -/
theorem generatorTwo_cube_shift (z : ℍ) :
    (((generatorTwoSL ^ 3 : SL(2, ℝ)) • z : ℍ) : ℂ) - (stripLeft : ℂ) =
      -(stripRight : ℂ) * ((z : ℂ) - (stripLeft : ℂ) + stripRight) /
        ((z : ℂ) - (stripLeft : ℂ) - stripRight) :=
  generatorTwo_cube_secondShift z

theorem generatorTwo_shift_norm_le (z : ℍ) (hx : stripLeft ≤ z.re) :
    ‖((generatorTwoSL • z : ℍ) : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight := by
  change ‖secondShift (generatorTwoSL • z)‖ ≤ stripRight
  rw [generatorTwo_secondShift, mul_div_assoc, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 ≤ (secondShift z).re := by
    rw [secondShift_re]
    exact sub_nonneg.mpr hx
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_sub_div_add_le_one stripRight_pos hrez) stripRight_pos.le

theorem generatorTwo_shift_norm_lt (z : ℍ) (hx : stripLeft < z.re) :
    ‖((generatorTwoSL • z : ℍ) : ℂ) - (stripLeft : ℂ)‖ < stripRight := by
  change ‖secondShift (generatorTwoSL • z)‖ < stripRight
  rw [generatorTwo_secondShift, mul_div_assoc, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 < (secondShift z).re := by
    rw [secondShift_re]
    exact sub_pos.mpr hx
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (norm_sub_div_add_lt_one stripRight_pos hrez) stripRight_pos

theorem generatorTwo_sq_re_le_stripLeft (z : ℍ) (hx : stripLeft ≤ z.re) :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re ≤ stripLeft := by
  have hrez : 0 ≤ (secondShift z).re := by
    rw [secondShift_re]
    exact sub_nonneg.mpr hx
  have h := re_neg_sq_div_nonpos (r := stripRight) hrez
  rw [← generatorTwo_sq_secondShift z, secondShift_re] at h
  exact sub_nonpos.mp h

theorem generatorTwo_sq_re_lt_stripLeft (z : ℍ) (hx : stripLeft < z.re) :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re < stripLeft := by
  have hrez : 0 < (secondShift z).re := by
    rw [secondShift_re]
    exact sub_pos.mpr hx
  have h := re_neg_sq_div_neg stripRight_pos hrez
  rw [← generatorTwo_sq_secondShift z, secondShift_re] at h
  exact sub_neg.mp h

theorem generatorTwo_cube_re_le_stripLeft (z : ℍ)
    (hn : stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖) :
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z).re ≤ stripLeft := by
  have h : (secondShift ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)).re ≤ 0 := by
    rw [generatorTwo_cube_secondShift, mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr stripRight_pos.le)
      (re_add_div_sub_nonneg stripRight_pos hn)
  rw [secondShift_re] at h
  exact sub_nonpos.mp h

theorem generatorTwo_cube_re_lt_stripLeft (z : ℍ)
    (hn : stripRight < ‖(z : ℂ) - (stripLeft : ℂ)‖) :
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z).re < stripLeft := by
  have h : (secondShift ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)).re < 0 := by
    rw [generatorTwo_cube_secondShift, mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos stripRight_pos)
      (re_add_div_sub_pos stripRight_pos hn)
  rw [secondShift_re] at h
  exact sub_neg.mp h

/-- The first second-generator power enters the weak circular exclusion. -/
theorem generatorTwo_closedSecondSector :
    MapsTo (fun z : ℍ => generatorTwoSL • z) closedSecondSector secondWeakExcluded :=
  fun z hz => Or.inr (generatorTwo_shift_norm_le z hz.1)

/-- The second power enters the weak vertical exclusion. -/
theorem generatorTwo_sq_closedSecondSector :
    MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z)
      closedSecondSector secondWeakExcluded :=
  fun z hz => Or.inl (generatorTwo_sq_re_le_stripLeft z hz.1)

/-- The third power also enters the weak vertical exclusion. -/
theorem generatorTwo_cube_closedSecondSector :
    MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z)
      closedSecondSector secondWeakExcluded :=
  fun z hz => Or.inl (generatorTwo_cube_re_le_stripLeft z hz.2)


end Wikipedia.HopfProblem.SpecialPeriods.Triangle
