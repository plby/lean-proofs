import Wikipedia.HopfProblem.EllipticPeriodCoordinates

/-!
# Literal real-linear coordinates transverse to the original delta direction

The projection keeps the first complex coordinate and normalizes the
remaining imaginary coordinate using the actual period discriminant.
The first three projected period columns form an explicit real basis of
`ℂ × ℝ`, with its inverse written in the original period parameters.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

theorem tau_im_ne_zero (p : PeriodDomain) : p.val.τ.im ≠ 0 :=
  ne_of_gt p.property.1

theorem discriminant_ne_zero (p : PeriodDomain) : p.val.discriminant ≠ 0 :=
  ne_of_lt p.property.2

/-- The literal projection along the real direction of the original delta period. -/
def linearProjection (p : PeriodDomain) : ComplexPlane₂ →L[ℝ] (ℂ × ℝ) where
  toFun z := (z 0,
    ((z 1).im - (p.val.μ.im / p.val.τ.im) * (z 0).im) / p.val.discriminant)
  map_add' z w := by
    apply Prod.ext
    · rfl
    · simp only [Prod.snd_add, Pi.add_apply, Complex.add_im]
      ring
  map_smul' r z := by
    apply Prod.ext
    · rfl
    · change ((r • z 1).im -
          (p.val.μ.im / p.val.τ.im) * (r • z 0).im) / p.val.discriminant =
        r * (((z 1).im - (p.val.μ.im / p.val.τ.im) * (z 0).im) /
          p.val.discriminant)
      simp only [Complex.smul_im, smul_eq_mul]
      ring
  cont := by fun_prop

@[simp] theorem linearProjection_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    linearProjection p z = (z 0,
      ((z 1).im - (p.val.μ.im / p.val.τ.im) * (z 0).im) / p.val.discriminant) := rfl

/-- The projected three-period basis, with its explicit inverse in the actual parameters. -/
def projectedPeriods (p : PeriodDomain) : (Fin 3 → ℝ) ≃L[ℝ] (ℂ × ℝ) :=
  (show (Fin 3 → ℝ) ≃ₗ[ℝ] (ℂ × ℝ) from {
    toFun x := (6 * p.val.μ * (x 0 : ℂ) + p.val.τ * (x 1 : ℂ) + (x 2 : ℂ), x 0)
    invFun y := ![y.2, (y.1.im - 6 * p.val.μ.im * y.2) / p.val.τ.im,
      y.1.re - 6 * p.val.μ.re * y.2 -
        p.val.τ.re * ((y.1.im - 6 * p.val.μ.im * y.2) / p.val.τ.im)]
    left_inv x := by
      ext j
      fin_cases j <;> simp [Complex.mul_re, Complex.mul_im] <;>
        field_simp [tau_im_ne_zero p] <;> ring
    right_inv y := by
      apply Prod.ext
      · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;>
          field_simp [tau_im_ne_zero p] <;> ring
      · rfl
    map_add' x y := by
      apply Prod.ext
      · simp only [Prod.fst_add, Pi.add_apply, Complex.ofReal_add]
        ring
      · rfl
    map_smul' r x := by
      apply Prod.ext
      · change 6 * p.val.μ * ((r * x 0 : ℝ) : ℂ) +
            p.val.τ * ((r * x 1 : ℝ) : ℂ) + ((r * x 2 : ℝ) : ℂ) =
          (r : ℂ) * (6 * p.val.μ * (x 0 : ℂ) +
            p.val.τ * (x 1 : ℂ) + (x 2 : ℂ))
        simp only [Complex.ofReal_mul]
        ring
      · rfl }).toContinuousLinearEquiv

@[simp] theorem projectedPeriods_apply (p : PeriodDomain) (x : Fin 3 → ℝ) :
    projectedPeriods p x =
      (6 * p.val.μ * (x 0 : ℂ) + p.val.τ * (x 1 : ℂ) + (x 2 : ℂ), x 0) := rfl

@[simp] theorem projectedPeriods_symm_apply (p : PeriodDomain) (y : ℂ × ℝ) :
    (projectedPeriods p).symm y =
      ![y.2, (y.1.im - 6 * p.val.μ.im * y.2) / p.val.τ.im,
        y.1.re - 6 * p.val.μ.re * y.2 -
          p.val.τ.re * ((y.1.im - 6 * p.val.μ.im * y.2) / p.val.τ.im)] := rfl

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
