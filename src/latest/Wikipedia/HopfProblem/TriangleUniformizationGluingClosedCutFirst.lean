import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedSectors

/-!
# Closed-sector returns for the order-three generator

If either nonidentity power of the actual order-three generator takes a
point back into its closed cyclic sector, its value is the circular
reflection of the original point. The proof forces the appropriate
vertical reflection to fix a boundary point using the explicit matrix
formulas. In particular, the result applies to the closed circular double.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

private theorem generatorOne_re_lower_of_one_le_norm (z : ℍ)
    (hn : 1 ≤ ‖(z : ℂ)‖) : -(1 / 2) ≤ (generatorOneSL • z).re := by
  change -(1 / 2) ≤ (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re,
    UpperHalfPlane.coe_re, Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hsq : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  simp only [← neg_div]
  apply (le_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im] at hsq ⊢
  nlinarith

private theorem re_lower_of_one_le_generatorOne_sq_norm (z : ℍ)
    (hn : 1 ≤ ‖(((generatorOneSL ^ 2) • z : ℍ) : ℂ)‖) :
    -(1 / 2) ≤ z.re := by
  rw [generatorOneSL_sq_smul_coe] at hn
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div] at hn
  have hnorm : ‖(z : ℂ)‖ ≤ ‖(z : ℂ) + 1‖ :=
    (one_le_div (norm_pos_iff.mpr z.ne_zero)).mp hn
  have hsq := (sq_le_sq₀ (norm_nonneg (z : ℂ))
    (norm_nonneg ((z : ℂ) + 1))).mpr hnorm
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hsq
  linarith

/-- The square of the order-three generator is the reversed product of
the same two actual reflections. -/
theorem generatorOne_sq_reflections (z : ℍ) :
    (generatorOneSL ^ 2) • z = circleReflection (rightReflection z) := by
  apply UpperHalfPlane.ext
  rw [generatorOneSL_sq_smul_coe, circleReflection_coe, rightReflection_coe]
  simp only [map_sub, map_neg, map_one, Complex.conj_conj]
  rw [show (-1 : ℂ) - (z : ℂ) + 1 = -(z : ℂ) by ring]
  simp [one_div, sub_eq_add_neg]

/-- A return by the first generator to its closed cyclic sector is
exactly the actual circular reflection. -/
theorem generatorOne_closedFirst_return (z : ℍ) (hz : z ∈ closedFirstSector)
    (hw : generatorOneSL • z ∈ closedFirstSector) :
    generatorOneSL • z = circleReflection z := by
  have hx : (generatorOneSL • z).re = -(1 / 2) :=
    le_antisymm hw.1 (generatorOne_re_lower_of_one_le_norm z hz.2)
  have hfix := (rightReflection_fixed_iff (generatorOneSL • z)).mpr hx
  calc
    generatorOneSL • z = rightReflection (generatorOneSL • z) := hfix.symm
    _ = circleReflection z := by
      rw [generatorOne_reflections, rightReflection_involutive]

/-- The analogous return statement for the square of the first generator. -/
theorem generatorOne_sq_closedFirst_return (z : ℍ) (hz : z ∈ closedFirstSector)
    (hw : (generatorOneSL ^ 2) • z ∈ closedFirstSector) :
    (generatorOneSL ^ 2) • z = circleReflection z := by
  have hx : z.re = -(1 / 2) :=
    le_antisymm hz.1 (re_lower_of_one_le_generatorOne_sq_norm z hw.2)
  rw [generatorOne_sq_reflections, (rightReflection_fixed_iff z).mpr hx]

/-- First-generator returns to the actual closed circular double. -/
theorem generatorOne_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hw : generatorOneSL • z ∈ circularDoubleRegion) :
    generatorOneSL • z = circleReflection z :=
  generatorOne_closedFirst_return z hz.1 hw.1

/-- Squared-first-generator returns to the actual closed circular double. -/
theorem generatorOne_sq_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hw : (generatorOneSL ^ 2) • z ∈ circularDoubleRegion) :
    (generatorOneSL ^ 2) • z = circleReflection z :=
  generatorOne_sq_closedFirst_return z hz.1 hw.1

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
