import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedSectors

/-!
# Closed-sector returns for the order-four generator

If a nonidentity power of the order-four generator takes a point of its
closed cyclic sector back into the same sector, the resulting point is
its reflection in the circular side.  For the square, both sector
inequalities force the point to be the elliptic center itself.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

private theorem eq_centerTwo_of_secondSector_boundaries (z : ℍ)
    (hr : z.re = stripLeft)
    (hn : ‖(z : ℂ) - (stripLeft : ℂ)‖ = stripRight) : z = centerTwo := by
  have hs := congrArg (fun r : ℝ => r ^ 2) hn
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hr, sub_self, sub_zero,
    zero_mul, zero_add] at hs
  have hi : z.im = stripRight := by
    nlinarith [z.im_pos, stripRight_pos]
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simpa only [UpperHalfPlane.coe_re, centerTwo_re, stripLeft] using hr
  · simpa only [UpperHalfPlane.coe_im, centerTwo_im, stripRight] using hi

private theorem generatorTwo_smul_cube (z : ℍ) :
    generatorTwoSL • ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) = z := by
  rw [← mul_smul, ← pow_succ']
  change realSLPermutation (generatorTwoSL ^ 4) z = z
  rw [generatorTwoSL_fourth, realSLPermutation_neg_one]
  rfl

/-- A first-power return to the closed sector occurs on the left vertical side. -/
theorem generatorTwo_closedSecond_return (z : ℍ) (hz : z ∈ closedSecondSector)
    (hgz : generatorTwoSL • z ∈ closedSecondSector) :
    generatorTwoSL • z = circleReflection z := by
  have hr : z.re = stripLeft := le_antisymm
    (le_of_not_gt fun h => (not_lt_of_ge hgz.2) (generatorTwo_shift_norm_lt z h)) hz.1
  rw [generatorTwo_reflections, (leftReflection_fixed_iff z).mpr hr]

/-- A square return to the closed sector can occur only at its elliptic vertex. -/
theorem generatorTwo_sq_closedSecond_return_eq_centerTwo (z : ℍ)
    (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ closedSecondSector) :
    z = centerTwo := by
  have hr : z.re = stripLeft := le_antisymm
    (le_of_not_gt fun h => (not_lt_of_ge hgz.1)
      (generatorTwo_sq_re_lt_stripLeft z h)) hz.1
  have hn := hgz.2
  rw [generatorTwo_sq_shift, norm_div, norm_neg, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos stripRight_pos] at hn
  have hp : 0 < ‖(z : ℂ) - (stripLeft : ℂ)‖ := stripRight_pos.trans_le hz.2
  have hle : ‖(z : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight := by
    apply (mul_le_mul_iff_of_pos_left stripRight_pos).mp
    simpa only [pow_two] using (le_div_iff₀ hp).mp hn
  exact eq_centerTwo_of_secondSector_boundaries z hr (le_antisymm hle hz.2)

/-- The square has the same circular-reflection return identity. -/
theorem generatorTwo_sq_closedSecond_return (z : ℍ) (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ closedSecondSector) :
    (generatorTwoSL ^ 2 : SL(2, ℝ)) • z = circleReflection z := by
  obtain rfl := generatorTwo_sq_closedSecond_return_eq_centerTwo z hz hgz
  have hl : leftReflection centerTwo = centerTwo :=
    (leftReflection_fixed_iff centerTwo).mpr centerTwo_re
  have hc : circleReflection centerTwo = centerTwo := by
    have h := generatorTwo_reflections centerTwo
    rw [generatorTwo_fix, hl] at h
    exact h.symm
  simp only [pow_two, mul_smul, generatorTwo_fix, hc]

/-- The third-power return follows by reversing a first-power return. -/
theorem generatorTwo_cube_closedSecond_return (z : ℍ) (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 3 : SL(2, ℝ)) • z ∈ closedSecondSector) :
    (generatorTwoSL ^ 3 : SL(2, ℝ)) • z = circleReflection z := by
  have h := generatorTwo_closedSecond_return
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) hgz
    (by simpa only [generatorTwo_smul_cube] using hz)
  have hc := congrArg circleReflection h
  simpa only [generatorTwo_smul_cube,
    circleReflection_involutive ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)] using hc.symm

/-- The first-power boundary return for the closed circular double. -/
theorem generatorTwo_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hgz : generatorTwoSL • z ∈ circularDoubleRegion) :
    generatorTwoSL • z = circleReflection z :=
  generatorTwo_closedSecond_return z hz.2 hgz.2

/-- The square boundary return for the closed circular double. -/
theorem generatorTwo_sq_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ circularDoubleRegion) :
    (generatorTwoSL ^ 2 : SL(2, ℝ)) • z = circleReflection z :=
  generatorTwo_sq_closedSecond_return z hz.2 hgz.2

/-- The third-power boundary return for the closed circular double. -/
theorem generatorTwo_cube_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hgz : (generatorTwoSL ^ 3 : SL(2, ℝ)) • z ∈ circularDoubleRegion) :
    (generatorTwoSL ^ 3 : SL(2, ℝ)) • z = circleReflection z :=
  generatorTwo_cube_closedSecond_return z hz.2 hgz.2

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
