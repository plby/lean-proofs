import Wikipedia.HopfProblem.SpecialPeriodsTriangleMatrices
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCayley
import Wikipedia.HopfProblem.SpecialPeriodsRotations
import Wikipedia.HopfProblem.SpecialPeriodsTriangleLinearization
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRepresentation

/-!
# Actual holomorphic triangle generators and their elliptic centers

The two real determinant-one matrices act on the upper half-plane itself.
Their fixed points and complex derivatives have the source's negative
rotation orientation: `exp (-2πi/3)` and `exp (-2πi/4)`.
This file does not assume that a quotient coordinate or a global period
function already exists.
-/

noncomputable section

open Matrix UpperHalfPlane
open scoped MatrixGroups ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem specialLinear_holomorphic (g : SL(2, ℝ)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => g • z) := by
  exact UpperHalfPlane.contMDiff_smul (g := SpecialLinearGroup.mapGL ℝ g) (by simp)

/-- Every actual real determinant-one matrix acts biholomorphically. -/
def specialLinearBiholomorph (g : SL(2, ℝ)) : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℍ ω where
  toFun := fun z => g • z
  invFun := fun z => g⁻¹ • z
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  contMDiff_toFun := specialLinear_holomorphic g
  contMDiff_invFun := specialLinear_holomorphic g⁻¹

/-- The order-three elliptic point on the source upper half-plane. -/
def centerOne : ℍ := ⟨rho - 1, by
  simpa only [Complex.sub_im, Complex.one_im, sub_zero] using rho_im_pos⟩

/-- The order-four elliptic point on the source upper half-plane. -/
def centerTwo : ℍ :=
  ⟨-((width : ℂ) + 1) / 2 + ((width : ℂ) - 1) / 2 * Complex.I, by
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.neg_im, Complex.add_im,
      Complex.ofReal_im, Complex.one_im, Complex.sub_im, Complex.mul_im,
      Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.I_im, Complex.I_re]
    linarith [one_lt_width]⟩

@[simp] theorem centerOne_val : (centerOne : ℂ) = rho - 1 := rfl

@[simp] theorem centerTwo_val : (centerTwo : ℂ) =
    -((width : ℂ) + 1) / 2 + ((width : ℂ) - 1) / 2 * Complex.I := rfl

theorem centerTwo_re : centerTwo.re = -(width + 1) / 2 := by
  simp [UpperHalfPlane.re, centerTwo]

theorem centerTwo_im : centerTwo.im = (width - 1) / 2 := by
  simp [UpperHalfPlane.im, centerTwo]

theorem width_complex_sq : (width : ℂ) ^ 2 = 2 * width + 1 := by
  exact_mod_cast width_sq

theorem generatorOne_val (z : ℍ) :
    (generatorOneSL • z : ℍ) = ofComplex (-1 / ((z : ℂ) + 1)) := by
  apply UpperHalfPlane.ext
  have he : ((generatorOneSL • z : ℍ) : ℂ) = -1 / ((z : ℂ) + 1) := by
    rw [coe_specialLinearGroup_apply]
    simp [generatorOneSL]
  rw [he]
  have hp : 0 < (-1 / ((z : ℂ) + 1)).im := he ▸ (generatorOneSL • z).im_pos
  simp only [ofComplex_apply_of_im_pos hp]

theorem generatorOne_coe (z : ℍ) :
    ((generatorOneSL • z : ℍ) : ℂ) = -1 / ((z : ℂ) + 1) := by
  rw [coe_specialLinearGroup_apply]
  simp [generatorOneSL]

theorem generatorTwo_coe (z : ℍ) :
    ((generatorTwoSL • z : ℍ) : ℂ) =
      ((z : ℂ) + (width : ℂ) + 1) / (-(z : ℂ) - width) := by
  rw [coe_specialLinearGroup_apply]
  simp [generatorTwoSL, add_assoc, sub_eq_add_neg]

theorem denominatorOne_ne_zero (z : ℍ) : (z : ℂ) + 1 ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.one_im, Complex.zero_im, add_zero,
    UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

theorem denominatorTwo_ne_zero (z : ℍ) : -(z : ℂ) - width ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, sub_zero,
    Complex.zero_im, neg_eq_zero, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

theorem centerTwo_polynomial :
    (centerTwo : ℂ) ^ 2 + ((width : ℂ) + 1) * centerTwo + ((width : ℂ) + 1) = 0 := by
  rw [centerTwo_val]
  calc
    _ = -((width : ℂ) + 1) ^ 2 / 4 + ((width : ℂ) - 1) ^ 2 / 4 * Complex.I ^ 2 +
        ((width : ℂ) + 1) := by ring
    _ = -((width : ℂ) ^ 2 - 2 * width - 1) / 2 := by rw [Complex.I_sq]; ring
    _ = 0 := by rw [width_complex_sq]; ring

@[simp] theorem generatorOne_fix : generatorOneSL • centerOne = centerOne := by
  apply UpperHalfPlane.ext
  rw [generatorOne_coe, centerOne_val]
  have hd : rho ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.zero_im] at hi
    exact (ne_of_gt rho_im_pos) hi
  simp only [sub_add_cancel]
  apply (div_eq_iff hd).mpr
  linear_combination -rho_sq

@[simp] theorem generatorTwo_fix : generatorTwoSL • centerTwo = centerTwo := by
  apply UpperHalfPlane.ext
  rw [generatorTwo_coe]
  apply (div_eq_iff (denominatorTwo_ne_zero centerTwo)).mpr
  linear_combination centerTwo_polynomial

theorem generatorOne_derivative_coefficient : 1 / ((centerOne : ℂ) + 1) ^ 2 = -rho := by
  rw [centerOne_val, sub_add_cancel]
  apply (div_eq_iff (pow_ne_zero 2 (by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.zero_im] at hi
    exact (ne_of_gt rho_im_pos) hi))).mpr
  linear_combination rho_cube

theorem generatorTwo_denominator_sq : (-(centerTwo : ℂ) - width) ^ 2 = Complex.I := by
  rw [centerTwo_val]
  calc
    _ = ((width : ℂ) - 1) ^ 2 / 4 * (1 + 2 * Complex.I + Complex.I ^ 2) := by ring
    _ = Complex.I := by
      rw [Complex.I_sq]
      have hs : ((width : ℂ) - 1) ^ 2 = 2 := by exact_mod_cast width_sub_one_sq
      rw [hs]
      ring

theorem generatorTwo_derivative_coefficient :
    1 / (-(centerTwo : ℂ) - width) ^ 2 = -Complex.I := by
  rw [generatorTwo_denominator_sq]
  simp

theorem generatorOne_multiplier : slMultiplier generatorOneSL centerOne = -rho := by
  simpa [slMultiplier, slDenom, generatorOneSL] using generatorOne_derivative_coefficient

theorem generatorTwo_multiplier : slMultiplier generatorTwoSL centerTwo = -Complex.I := by
  simpa [slMultiplier, slDenom, generatorTwoSL, sub_eq_add_neg] using
    generatorTwo_derivative_coefficient

theorem generatorOne_hasStrictDerivAt :
    HasStrictDerivAt (fun z : ℂ => ((generatorOneSL • ofComplex z : ℍ) : ℂ))
      (-rho) (centerOne : ℂ) := by
  rw [← generatorOne_multiplier]
  exact sl_hasStrictDerivAt_smul _ _

theorem generatorTwo_hasStrictDerivAt :
    HasStrictDerivAt (fun z : ℂ => ((generatorTwoSL • ofComplex z : ℍ) : ℂ))
      (-Complex.I) (centerTwo : ℂ) := by
  rw [← generatorTwo_multiplier]
  exact sl_hasStrictDerivAt_smul _ _

theorem generatorOne_cayley (z : ℍ) :
    cayleyCoordinate centerOne (generatorOneSL • z) =
      -rho * cayleyCoordinate centerOne z := by
  rw [cayleyCoordinate_smul _ _ _ generatorOne_fix, generatorOne_multiplier]

theorem generatorTwo_cayley (z : ℍ) :
    cayleyCoordinate centerTwo (generatorTwoSL • z) =
      -Complex.I * cayleyCoordinate centerTwo z := by
  rw [cayleyCoordinate_smul _ _ _ generatorTwo_fix, generatorTwo_multiplier]

theorem generatorOne_toDisc (z : ℍ) :
    toDisc centerOne (generatorOneSL • z) = discRotateThree (toDisc centerOne z) := by
  apply Subtype.ext
  exact generatorOne_cayley z

theorem generatorTwo_toDisc (z : ℍ) :
    toDisc centerTwo (generatorTwoSL • z) = discRotateFour (toDisc centerTwo z) := by
  apply Subtype.ext
  exact generatorTwo_cayley z

theorem generatorOne_conjugate (z : Disc) :
    cayleyBiholomorph centerOne (generatorOneSL • (cayleyBiholomorph centerOne).symm z) =
      discRotateThree z := by
  change toDisc centerOne (generatorOneSL • fromDisc centerOne z) = _
  rw [generatorOne_toDisc, toDisc_fromDisc]

theorem generatorTwo_conjugate (z : Disc) :
    cayleyBiholomorph centerTwo (generatorTwoSL • (cayleyBiholomorph centerTwo).symm z) =
      discRotateFour z := by
  change toDisc centerTwo (generatorTwoSL • fromDisc centerTwo z) = _
  rw [generatorTwo_toDisc, toDisc_fromDisc]

theorem generatorOne_pow_toDisc (n : ℕ) (z : ℍ) :
    toDisc centerOne (generatorOneSL ^ n • z) = discRotateThree^[n] (toDisc centerOne z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, generatorOne_toDisc, ih, Function.iterate_succ_apply']

theorem generatorTwo_pow_toDisc (n : ℕ) (z : ℍ) :
    toDisc centerTwo (generatorTwoSL ^ n • z) = discRotateFour^[n] (toDisc centerTwo z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, generatorTwo_toDisc, ih, Function.iterate_succ_apply']

theorem generatorOne_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3) (z : ℍ) :
    generatorOneSL ^ n • z = z ↔ z = centerOne := by
  have he : generatorOneSL ^ n • z = z ↔
      toDisc centerOne (generatorOneSL ^ n • z) = toDisc centerOne z :=
    (cayleyBiholomorph centerOne).injective.eq_iff.symm
  rw [he, generatorOne_pow_toDisc, discRotateThree_iterate_fixed_iff n hn hn']
  have hc : toDisc centerOne centerOne = discZero := toDisc_center _
  rw [← hc]
  exact (cayleyBiholomorph centerOne).injective.eq_iff

theorem generatorTwo_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4) (z : ℍ) :
    generatorTwoSL ^ n • z = z ↔ z = centerTwo := by
  have he : generatorTwoSL ^ n • z = z ↔
      toDisc centerTwo (generatorTwoSL ^ n • z) = toDisc centerTwo z :=
    (cayleyBiholomorph centerTwo).injective.eq_iff.symm
  rw [he, generatorTwo_pow_toDisc, discRotateFour_iterate_fixed_iff n hn hn']
  have hc : toDisc centerTwo centerTwo = discZero := toDisc_center _
  rw [← hc]
  exact (cayleyBiholomorph centerTwo).injective.eq_iff

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Holomorphicity of every element of the constructed triangle action,
not just of its two generators. -/
theorem triangleGeometricRepresentation_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (triangleGeometricRepresentation g : ℍ → ℍ) := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_has_SL_lift g
  rw [← hA]
  exact Triangle.specialLinear_holomorphic A

/-- The abstract triangle group acts by actual biholomorphisms. -/
def triangleGeometricBiholomorph (g : TriangleGroup) : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℍ ω where
  toEquiv := triangleGeometricRepresentation g
  contMDiff_toFun := triangleGeometricRepresentation_holomorphic g
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (((triangleGeometricRepresentation g)⁻¹ : Equiv.Perm ℍ) : ℍ → ℍ)
    rw [← map_inv]
    exact triangleGeometricRepresentation_holomorphic g⁻¹

@[simp] theorem triangleGeometricBiholomorph_apply (g : TriangleGroup) (z : ℍ) :
    triangleGeometricBiholomorph g z = triangleGeometricRepresentation g z := rfl

end Wikipedia.HopfProblem.SpecialPeriods
