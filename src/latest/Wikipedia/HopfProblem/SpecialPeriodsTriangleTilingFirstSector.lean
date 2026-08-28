import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingSectors

/-!
# The order-three sector inequalities

The two nonidentity powers of the actual first generator send its open
cyclic sector into the two explicit excluded regions.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem generatorOne_firstSector :
    MapsTo (fun z : ℍ => generatorOneSL • z) firstSector firstExcluded := by
  intro z hz
  left
  change -(1 / 2) < (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hn : 1 < Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2]
  simp only [← neg_div]
  apply (lt_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im] at hn ⊢
  nlinarith

theorem norm_add_one_lt_norm_of_re_lt_half (z : ℍ) (hz : z.re < -(1 / 2)) :
    ‖(z : ℂ) + 1‖ < ‖(z : ℂ)‖ := by
  have hsq : ‖(z : ℂ) + 1‖ ^ 2 < ‖(z : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

theorem generatorOne_sq_firstSector :
    MapsTo (fun z : ℍ => (generatorOneSL ^ 2) • z) firstSector firstExcluded := by
  intro z hz
  right
  change ‖(((generatorOneSL ^ 2) • z : ℍ) : ℂ)‖ < 1
  rw [generatorOneSL_sq_smul_coe]
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr z.ne_zero)).mpr
    (norm_add_one_lt_norm_of_re_lt_half z hz.1)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
