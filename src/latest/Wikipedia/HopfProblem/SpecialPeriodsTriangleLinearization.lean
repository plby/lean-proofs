import Wikipedia.HopfProblem.SpecialPeriodsTriangleCayley
import Wikipedia.HopfProblem.SpecialPeriodsRotations

/-!
# Linearization at an elliptic fixed point

For an actual real determinant-one matrix fixing an upper-half-plane point,
the centered Cayley coordinate conjugates its action to multiplication by
its complex derivative.  In particular the multiplier has norm one.
-/

noncomputable section

open UpperHalfPlane Matrix
open scoped MatrixGroups ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The automorphy denominator for the actual `SL(2, ℝ)` action. -/
def slDenom (g : SL(2, ℝ)) (z : ℂ) : ℂ := (g 1 0 : ℂ) * z + (g 1 1 : ℂ)

theorem slDenom_ne_zero (g : SL(2, ℝ)) (z : ℍ) : slDenom g z ≠ 0 :=
  UpperHalfPlane.linear_ne_zero z (g.row_ne_zero 1)

theorem sl_fixed_equation (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (g 0 0 : ℂ) * a + (g 0 1 : ℂ) = (a : ℂ) * slDenom g a := by
  have he := congrArg (fun z : ℍ => (z : ℂ)) hfix
  apply (div_eq_iff (slDenom_ne_zero g a)).mp
  simpa only [coe_specialLinearGroup_apply, Algebra.algebraMap_self, RingHom.id_apply,
    slDenom] using he

theorem sl_fixed_conj_equation (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (g 0 0 : ℂ) * starRingEnd ℂ (a : ℂ) + (g 0 1 : ℂ) =
      starRingEnd ℂ (a : ℂ) * slDenom g (starRingEnd ℂ (a : ℂ)) := by
  simpa [slDenom] using congrArg (starRingEnd ℂ) (sl_fixed_equation g a hfix)

theorem sl_fixed_denominator_identity (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) * slDenom g a = 1 := by
  have hdet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast (show g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 from
      (Matrix.det_fin_two g.val).symm.trans g.property)
  have hf := sl_fixed_equation g a hfix
  unfold slDenom at *
  linear_combination (g 1 0 : ℂ) * hf + hdet

theorem sl_fixed_conj_denominator (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (g 0 0 : ℂ) - (g 1 0 : ℂ) * starRingEnd ℂ (a : ℂ) = slDenom g a := by
  have hf := sl_fixed_equation g a hfix
  have him := congrArg Complex.im hf
  simp only [slDenom, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero,
    Complex.add_re, Complex.mul_re, sub_zero] at him
  have hr : g 0 0 = 2 * g 1 0 * (a : ℂ).re + g 1 1 := by
    apply mul_right_cancel₀ (show (a : ℂ).im ≠ 0 from a.im_ne_zero)
    calc
      g 0 0 * (a : ℂ).im =
          (a : ℂ).re * (g 1 0 * (a : ℂ).im) +
            (a : ℂ).im * (g 1 0 * (a : ℂ).re + g 1 1) := him
      _ = (2 * g 1 0 * (a : ℂ).re + g 1 1) * (a : ℂ).im := by ring
  apply Complex.ext <;>
    simp only [slDenom, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im] <;> nlinarith [hr]

theorem sl_fixed_denominator_norm (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    ‖slDenom g a‖ = 1 := by
  have hc : starRingEnd ℂ (slDenom g a) =
      (g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ) := by
    simpa only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj] using
      (congrArg (starRingEnd ℂ) (sl_fixed_conj_denominator g a hfix)).symm
  have hm : starRingEnd ℂ (slDenom g a) * slDenom g a = 1 := by
    rw [hc, sl_fixed_denominator_identity g a hfix]
  have hn := congrArg norm hm
  simp only [norm_mul, Complex.norm_conj, norm_one] at hn
  nlinarith [norm_nonneg (slDenom g a)]

/-- The complex derivative multiplier of the actual determinant-one action. -/
def slMultiplier (g : SL(2, ℝ)) (a : ℍ) : ℂ := 1 / slDenom g a ^ 2

theorem sl_hasStrictDerivAt_smul (g : SL(2, ℝ)) (a : ℍ) :
    HasStrictDerivAt (fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ))
      (slMultiplier g a) (a : ℂ) := by
  have h := UpperHalfPlane.hasStrictDerivAt_smul
    (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp) a
  simpa [MulAction.compHom_smul_def, slMultiplier, slDenom, UpperHalfPlane.denom] using h

theorem sl_deriv_smul (g : SL(2, ℝ)) (a : ℍ) :
    deriv (fun z : ℂ => ((g • ofComplex z : ℍ) : ℂ)) (a : ℂ) = slMultiplier g a :=
  (sl_hasStrictDerivAt_smul g a).hasDerivAt.deriv

theorem slMultiplier_norm (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    ‖slMultiplier g a‖ = 1 := by
  simp [slMultiplier, sl_fixed_denominator_norm g a hfix]

/-- Exact algebraic linearization in the centered Cayley coordinate. -/
theorem cayleyCoordinate_smul (g : SL(2, ℝ)) (a z : ℍ) (hfix : g • a = a) :
    cayleyCoordinate a (g • z) = slMultiplier g a * cayleyCoordinate a z := by
  have hd := slDenom_ne_zero g z
  have ha := slDenom_ne_zero g a
  have hn : ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - (a : ℂ) =
      ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) * ((z : ℂ) - a) / slDenom g z := by
    have hf := sl_fixed_equation g a hfix
    field_simp [hd]
    unfold slDenom at *
    linear_combination hf
  have hnbar : ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z -
        starRingEnd ℂ (a : ℂ) =
      ((g 0 0 : ℂ) - (g 1 0 : ℂ) * starRingEnd ℂ (a : ℂ)) *
        ((z : ℂ) - starRingEnd ℂ (a : ℂ)) / slDenom g z := by
    have hf := sl_fixed_conj_equation g a hfix
    field_simp [hd]
    unfold slDenom at *
    linear_combination hf
  have hcoef : ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) / slDenom g a =
      slMultiplier g a := by
    rw [slMultiplier, div_eq_div_iff ha (pow_ne_zero 2 ha)]
    have hf := sl_fixed_denominator_identity g a hfix
    linear_combination slDenom g a * hf
  unfold cayleyCoordinate
  simp only [coe_specialLinearGroup_apply, Algebra.algebraMap_self, RingHom.id_apply]
  change (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - (a : ℂ)) /
    (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - starRingEnd ℂ (a : ℂ)) = _
  rw [hn, hnbar, div_div_div_cancel_right₀ hd,
    sl_fixed_conj_denominator g a hfix, mul_div_mul_comm, hcoef]

/-- The multiplier in Cayley coordinates is precisely the complex derivative. -/
theorem cayleyCoordinate_smul_deriv (g : SL(2, ℝ)) (a z : ℍ) (hfix : g • a = a) :
    cayleyCoordinate a (g • z) =
      deriv (fun w : ℂ => ((g • ofComplex w : ℍ) : ℂ)) (a : ℂ) * cayleyCoordinate a z := by
  rw [sl_deriv_smul]
  exact cayleyCoordinate_smul g a z hfix

/-- Conjugacy as an equality of points in the actual unit disc. -/
theorem toDisc_smul (g : SL(2, ℝ)) (a z : ℍ) (hfix : g • a = a) :
    toDisc a (g • z) =
      discScalar (slMultiplier g a) (slMultiplier_norm g a hfix) (toDisc a z) := by
  apply Subtype.ext
  exact cayleyCoordinate_smul g a z hfix

/-- The entire conjugated disc map, not just its derivative at zero, is a rotation. -/
theorem cayleyBiholomorph_conjugate (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (fun z : Disc => cayleyBiholomorph a (g • (cayleyBiholomorph a).symm z)) =
      discScalar (slMultiplier g a) (slMultiplier_norm g a hfix) := by
  funext z
  change toDisc a (g • fromDisc a z) = _
  rw [toDisc_smul g a _ hfix, toDisc_fromDisc]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
