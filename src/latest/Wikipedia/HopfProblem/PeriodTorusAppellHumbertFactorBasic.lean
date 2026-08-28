import Wikipedia.HopfProblem.PeriodTorusAppellHumbertData
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianProperties
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Genuine Appell--Humbert factors from Hermitian data

The cocycle law is proved for the explicit exponential expression. The
semicharacter identity used here has the negative phase, which agrees with
the usual positive phase whenever the imaginary pairing is integral.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

open Complex PeriodTorusTypeOneOne
open scoped ContDiff

/-- The actual associated Hermitian form of an integral tangent form of type `(1,1)`. -/
def integralHermitian (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) : PeriodTorusTheta.HermitianForm :=
  associatedSesquilinear (tangentForm p E) hType

@[simp]
theorem integralHermitian_im (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (x y : ComplexPlane₂) :
    (integralHermitian p E hType x y).im = tangentForm p E x y :=
  associatedSesquilinear_im (tangentForm p E) hType x y

theorem integralHermitian_isHermitian (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) :
    PeriodTorusTheta.IsHermitian (integralHermitian p E hType) :=
  associatedSesquilinear_conj_symm (tangentForm p E) hType (tangentForm_self p E)

/-- The imaginary part on genuine period-lattice elements is the specified integer pairing. -/
theorem integralHermitian_lattice_im (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l m : p.lattice) :
    (integralHermitian p E hType l m).im =
      (coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) : ℝ) := by
  rw [integralHermitian_im]
  simpa only [periodEquiv_integer_eq_periodVector, p.periodVector_latticeEquiv] using
    tangentForm_integer_periods p E (p.latticeEquiv l) (p.latticeEquiv m)

/-- The holomorphic exponential term, in the first-linear convention. -/
def appellHumbertExponent (H : PeriodTorusTheta.HermitianForm)
    (l z : ComplexPlane₂) : ℂ :=
  (Real.pi : ℂ) * H z l + ((Real.pi : ℂ) / 2) * H l l

theorem appellHumbertExponent_cocycle (H : PeriodTorusTheta.HermitianForm)
    (hH : PeriodTorusTheta.IsHermitian H) (l m z : ComplexPlane₂) :
    -((Real.pi : ℂ) * I * ((H l m).im : ℂ)) + appellHumbertExponent H (l + m) z =
      appellHumbertExponent H l (z + m) + appellHumbertExponent H m z := by
  apply Complex.ext <;>
    simp [appellHumbertExponent, map_add, LinearMap.add_apply, hH l m,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem appellHumbertExponent_holomorphic (H : PeriodTorusTheta.HermitianForm)
    (l : ComplexPlane₂) : ContDiff ℂ ω (appellHumbertExponent H l) := by
  have hlin : ContDiff ℂ ω (fun z => H z l) := (H.flip l).toContinuousLinearMap.contDiff
  exact (contDiff_const.mul hlin).add contDiff_const

/-- The explicit nonvanishing holomorphic factor associated with compatible data. -/
def hermitianFactor (p : PeriodDomain) (H : PeriodTorusTheta.HermitianForm)
    (hH : PeriodTorusTheta.IsHermitian H) (α : p.lattice → ℂ)
    (hα0 : α 0 = 1) (hαne : ∀ l, α l ≠ 0)
    (hαadd : ∀ l m, α (l + m) = α l * α m *
      Complex.exp (-((Real.pi : ℂ) * I * ((H l m).im : ℂ)))) : FactorOfAutomorphy p where
  factor l z := Units.mk0 (α l * Complex.exp (appellHumbertExponent H l z))
    (mul_ne_zero (hαne l) (Complex.exp_ne_zero _))
  factor_zero z := by
    apply Units.ext
    simp [hα0, appellHumbertExponent]
  factor_add l m z := by
    apply Units.ext
    change α (l + m) * Complex.exp (appellHumbertExponent H (l + m : p.lattice) z) =
      (α l * Complex.exp (appellHumbertExponent H l (z + m))) *
        (α m * Complex.exp (appellHumbertExponent H m z))
    rw [hαadd]
    simp only [Submodule.coe_add]
    calc
      (α l * α m * Complex.exp (-((Real.pi : ℂ) * I * ((H l m).im : ℂ)))) *
          Complex.exp (appellHumbertExponent H (l + m) z) =
          α l * α m * Complex.exp (-((Real.pi : ℂ) * I * ((H l m).im : ℂ)) +
            appellHumbertExponent H (l + m) z) := by
        rw [Complex.exp_add]
        ring
      _ = α l * α m * Complex.exp
          (appellHumbertExponent H l (z + m) + appellHumbertExponent H m z) := by
        rw [appellHumbertExponent_cocycle H hH]
      _ = _ := by
        rw [Complex.exp_add]
        ring
  holomorphic_factor l := by
    change ContDiff ℂ ω (fun z => α l * Complex.exp (appellHumbertExponent H l z))
    exact contDiff_const.mul (appellHumbertExponent_holomorphic H l).cexp

@[simp]
theorem hermitianFactor_coe (p : PeriodDomain) (H : PeriodTorusTheta.HermitianForm)
    (hH : PeriodTorusTheta.IsHermitian H) (α : p.lattice → ℂ)
    (hα0 : α 0 = 1) (hαne : ∀ l, α l ≠ 0)
    (hαadd : ∀ l m, α (l + m) = α l * α m *
      Complex.exp (-((Real.pi : ℂ) * I * ((H l m).im : ℂ))))
    (l : p.lattice) (z : ComplexPlane₂) :
    ((hermitianFactor p H hH α hα0 hαne hαadd).factor l z : ℂ) =
      α l * Complex.exp ((Real.pi : ℂ) * H z l + ((Real.pi : ℂ) / 2) * H l l) := rfl

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
