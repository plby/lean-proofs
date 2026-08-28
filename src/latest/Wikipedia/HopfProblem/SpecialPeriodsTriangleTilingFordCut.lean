import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingFordGeometry

/-!
# Moving the right half of the Ford interior to the cyclic-sector polygon

The square of the actual order-three generator takes the right half of
the strict Ford polygon into the circular double. Its two nonidentity
powers cannot take an interior point back into the Ford interior.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

private theorem norm_lt_norm_add_one_of_re_gt_half (z : ℍ)
    (hx : -(1 / 2) < z.re) : ‖(z : ℂ)‖ < ‖(z : ℂ) + 1‖ := by
  have hsq : ‖(z : ℂ)‖ ^ 2 < ‖(z : ℂ) + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

private theorem norm_real_sub_inv_gt {r : ℝ} (hr : 0 < r) (hr2 : r ^ 2 = 1 / 2)
    {u : ℂ} (hu : u ≠ 0) (hx : u.re < r) : r < ‖(r : ℂ) - u⁻¹‖ := by
  have he : (r : ℂ) - u⁻¹ = ((r : ℂ) * u - 1) / u := by
    field_simp
  have hnum : r ^ 2 * Complex.normSq u < Complex.normSq ((r : ℂ) * u - 1) := by
    simp only [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal,
      map_one, mul_one, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_lt_mul_of_pos_left hx hr]
  have hsq : r ^ 2 < ‖(r : ℂ) - u⁻¹‖ ^ 2 := by
    rw [he, Complex.sq_norm, Complex.normSq_div]
    exact (lt_div_iff₀ (Complex.normSq_pos.mpr hu)).mpr hnum
  nlinarith [norm_nonneg ((r : ℂ) - u⁻¹)]

/-- The right half of the strict Ford polygon is carried into the
circular double by the square of the actual first generator. -/
theorem fordInterior_right_mem_circularDoubleInterior (z : ℍ) (hz : z ∈ fordInterior)
    (hx : -(1 / 2) < z.re) :
    (generatorOneSL ^ 2 : SL(2, ℝ)) • z ∈ circularDoubleInterior := by
  have hd : 1 < Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.2]
  have hp : 0 < Complex.normSq (z : ℂ) := zero_lt_one.trans hd
  have hc : 1 < Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hshift : 0 < Complex.normSq (z : ℂ) + 2 * z.re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at hc ⊢
    nlinarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · change ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ)).re < -(1 / 2)
    rw [generatorOneSL_sq_smul_coe]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re,
      Complex.inv_re, UpperHalfPlane.coe_re]
    have hfrac : -(1 / 2 : ℝ) < z.re / Complex.normSq (z : ℂ) :=
      (lt_div_iff₀ hp).mpr (by linarith)
    linarith
  · rw [generatorOneSL_sq_smul_coe]
    have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
      field_simp [z.ne_zero]
      ring
    rw [he, norm_neg, norm_div]
    exact (one_lt_div (norm_pos_iff.mpr z.ne_zero)).mpr
      (norm_lt_norm_add_one_of_re_gt_half z hx)
  · change stripLeft < ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ)).re
    rw [generatorOneSL_sq_smul_coe]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re,
      Complex.inv_re, UpperHalfPlane.coe_re]
    have hfrac : z.re / Complex.normSq (z : ℂ) < stripRight := by
      apply (div_lt_iff₀ hp).mpr
      exact hz.2.1.trans (by simpa only [mul_one] using
        mul_lt_mul_of_pos_left hd stripRight_pos)
    linarith [stripLeft_add_stripRight]
  · rw [generatorOneSL_sq_smul_coe]
    have hL : stripLeft = -stripRight - 1 := by
      linarith [stripLeft_add_stripRight]
    rw [hL]
    push_cast
    have he : (-1 : ℂ) - (z : ℂ)⁻¹ - (-(stripRight : ℂ) - 1) =
        (stripRight : ℂ) - (z : ℂ)⁻¹ := by ring
    rw [he]
    exact norm_real_sub_inv_gt stripRight_pos stripRight_sq z.ne_zero hz.2.1

/-- The first generator sends an interior Ford point inside the unit circle. -/
theorem generatorOne_not_mem_fordInterior (z : ℍ) (hz : z ∈ fordInterior) :
    generatorOneSL • z ∉ fordInterior := by
  intro hw
  have hn := hw.2.2.2
  rw [generatorOneSL_smul_coe, norm_neg, norm_inv] at hn
  exact lt_asymm hn (inv_lt_one_of_one_lt₀ hz.2.2.1)

/-- The square of the first generator sends an interior Ford point inside
the unit circle centered at `-1`. -/
theorem generatorOne_sq_not_mem_fordInterior (z : ℍ) (hz : z ∈ fordInterior) :
    (generatorOneSL ^ 2 : SL(2, ℝ)) • z ∉ fordInterior := by
  intro hw
  have hn := hw.2.2.1
  have he : ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) + 1) =
      -(z : ℂ)⁻¹ := by
    rw [generatorOneSL_sq_smul_coe]
    ring
  rw [he, norm_neg, norm_inv] at hn
  exact lt_asymm hn (inv_lt_one_of_one_lt₀ hz.2.2.2)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
