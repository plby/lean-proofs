import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycle
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactor

/-!
# The sign of the logarithmic pairing for canonical factors

Uniqueness of the continuous logarithmic lift determines its affine part
for a canonical Appell--Humbert factor. Consequently antisymmetrization of
the actual integer defect is the original integral alternating form, with
a positive sign in the fixed positive-translation convention. This is a
logarithmic calculation, not an assumed Chern-class comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert PeriodTorusTypeOneOne

/-- The normalized logarithm of a canonical factor has its actual affine Hermitian part. -/
theorem canonicalFactorLog_affine (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) (z : ComplexPlane₂) :
    factorLog (integralFactor p E hType) l z =
      factorLog (integralFactor p E hType) l 0 +
        (Real.pi : ℂ) * integralHermitian p E hType z l := by
  let H := integralHermitian p E hType
  let F := integralFactor p E hType
  let c : ComplexPlane₂ → ℂ := fun w => factorLog F l 0 + (Real.pi : ℂ) * H w l
  have hc : Continuous c :=
    continuous_const.add (continuous_const.mul (H.flip l).toContinuousLinearMap.continuous)
  have he (w : ComplexPlane₂) : Complex.exp (factorLog F l w) = Complex.exp (c w) := by
    simp only [c, F, H, Complex.exp_add, factorLog_exp, integralFactor_coe,
      map_zero, LinearMap.zero_apply, mul_zero, zero_add]
    ring
  have h0 : factorLog F l 0 = c 0 := by simp [c]
  exact congrFun (continuous_exp_lift_eq (factorLog F l) c
    (factorLog_holomorphic F l).continuous hc he h0) z

/-- The alternating pairing extracted from the logarithms has exactly the original sign. -/
theorem canonicalFactorLogAlternatingForm_apply (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l m : p.lattice) :
    factorLogAlternatingForm (integralFactor p E hType) l m =
      coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) := by
  have hperiod : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  apply Int.cast_injective (α := ℂ)
  apply mul_right_cancel₀ hperiod
  have hd := factorLogAlternatingForm_log_difference (integralFactor p E hType) l m 0
  simp only [zero_add] at hd
  rw [canonicalFactorLog_affine p E hType m (l : ComplexPlane₂),
    canonicalFactorLog_affine p E hType l (m : ComplexPlane₂)] at hd
  calc
    (factorLogAlternatingForm (integralFactor p E hType) l m : ℂ) *
        (2 * (Real.pi : ℂ) * I) =
      (Real.pi : ℂ) * integralHermitian p E hType l m -
        (Real.pi : ℂ) * integralHermitian p E hType m l := by
      linear_combination hd
    _ = _ := by
      rw [integralHermitian_isHermitian p E hType l m]
      have hImag (w : ℂ) : (Real.pi : ℂ) * w - (Real.pi : ℂ) * star w =
          (w.im : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
      rw [hImag, integralHermitian_lattice_im]
      simp only [Complex.ofReal_intCast]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
