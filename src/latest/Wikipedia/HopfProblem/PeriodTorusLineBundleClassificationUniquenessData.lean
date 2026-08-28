import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactorBasic

/-!
# Unitary Appell--Humbert input data

The multiplier is arbitrary subject to the actual norm-one and
semicharacter laws.  In particular, unitary character twists are not
discarded.  This type contains no realization or classification assertion.
Its associated factor is the explicit, previously proved analytic cocycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness

open PeriodTorusAppellHumbert PeriodTorusTheta

/-- Genuine unitary Appell--Humbert data in the linear-first convention.
The phase sign matches the original positive lattice translation action. -/
structure UnitaryDatum (p : PeriodDomain) where
  form : HermitianForm
  hermitian : IsHermitian form
  multiplier : p.lattice → ℂ
  norm_multiplier : ∀ l, ‖multiplier l‖ = 1
  multiplier_add : ∀ l m, multiplier (l + m) = multiplier l * multiplier m *
    Complex.exp (-((Real.pi : ℂ) * Complex.I * ((form l m).im : ℂ)))

namespace UnitaryDatum

variable {p : PeriodDomain} (D : UnitaryDatum p)

theorem multiplier_ne_zero (l : p.lattice) : D.multiplier l ≠ 0 := by
  intro h
  have hn := D.norm_multiplier l
  simp only [h, norm_zero] at hn
  exact zero_ne_one hn

@[simp] theorem multiplier_zero : D.multiplier 0 = 1 := by
  apply mul_left_cancel₀ (D.multiplier_ne_zero 0)
  simpa only [zero_add, Submodule.coe_zero, map_zero, Complex.zero_im,
    Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] using
    (D.multiplier_add 0 0).symm

/-- The genuine holomorphic factor, with normalization and nonvanishing
proved from the defining unitary semicharacter laws. -/
def factor : FactorOfAutomorphy p :=
  hermitianFactor p D.form D.hermitian D.multiplier D.multiplier_zero
    D.multiplier_ne_zero D.multiplier_add

@[simp] theorem factor_coe (l : p.lattice) (z : ComplexPlane₂) :
    (D.factor.factor l z : ℂ) = D.multiplier l *
      Complex.exp ((Real.pi : ℂ) * D.form z l + ((Real.pi : ℂ) / 2) * D.form l l) := rfl

/-- Proof fields do not add artificial distinctions between the actual data. -/
@[ext] theorem ext {D E : UnitaryDatum p} (hform : D.form = E.form)
    (hmultiplier : D.multiplier = E.multiplier) : D = E := by
  cases D
  cases E
  cases hform
  cases hmultiplier
  rfl

end UnitaryDatum

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
