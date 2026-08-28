import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingSectors

/-!
# The order-four generator on its cyclic sector

The three nonidentity powers of the actual order-four generator send
the open second sector to its excluded sector. After translating the
elliptic center to the imaginary axis, the maps are the standard
quarter-turn Möbius transformations with radius `stripRight`.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

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

/-- The first power takes the second sector strictly inside its circular boundary. -/
theorem generatorTwo_secondSector :
    MapsTo (fun z : ℍ => generatorTwoSL • z) secondSector secondExcluded := by
  intro z hz
  refine Or.inr ?_
  change ‖secondShift (generatorTwoSL • z)‖ < stripRight
  rw [generatorTwo_secondShift, mul_div_assoc, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 < (secondShift z).re := by
    rw [secondShift_re]
    exact sub_pos.mpr hz.1
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (norm_sub_div_add_lt_one stripRight_pos hrez) stripRight_pos

/-- The second power takes the second sector strictly left of its vertical boundary. -/
theorem generatorTwo_sq_secondSector :
    MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z)
      secondSector secondExcluded := by
  intro z hz
  refine Or.inl ?_
  have hrez : 0 < (secondShift z).re := by
    rw [secondShift_re]
    exact sub_pos.mpr hz.1
  have h := re_neg_sq_div_neg stripRight_pos hrez
  rw [← generatorTwo_sq_secondShift z, secondShift_re] at h
  exact sub_neg.mp h

/-- The third power also takes the second sector strictly left of its vertical boundary. -/
theorem generatorTwo_cube_secondSector :
    MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z)
      secondSector secondExcluded := by
  intro z hz
  refine Or.inl ?_
  have hnorm : stripRight < ‖secondShift z‖ := hz.2
  have h : (secondShift ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)).re < 0 := by
    rw [generatorTwo_cube_secondShift, mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos stripRight_pos)
      (re_add_div_sub_pos stripRight_pos hnorm)
  rw [secondShift_re] at h
  exact sub_neg.mp h

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
