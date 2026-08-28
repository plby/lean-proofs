import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessImaginary
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertSectionsAnalytic
import Wikipedia.HopfProblem.PeriodTorusThetaSpecial

/-!
# Nonzero theta sections force trivial unitary data on the special tori

The actual imaginary form of arbitrary unitary Appell--Humbert data is
already proved alternating, lattice-integral, and of type `(1,1)`. Away
from the actual exceptional period set, the genuine theta obstruction
forces this form to vanish. The zero-form theorem then forces the actual
multiplier to be one and every nonzero entire theta function to be a
nonzero constant. No section classification or bundle triviality is
assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationUniqueness
open PeriodTorusTypeOneOne SpecialPeriods UpperHalfPlane

/-- The genuine zero-form, constant-one unitary Appell--Humbert datum. -/
def trivialUnitaryDatum (p : PeriodDomain) : UnitaryDatum p where
  form := 0
  hermitian := PeriodTorusTheta.zero_isHermitian
  multiplier := fun _ => 1
  norm_multiplier _ := norm_one
  multiplier_add _ _ := by simp

@[simp] theorem trivialUnitaryDatum_form (p : PeriodDomain) :
    (trivialUnitaryDatum p).form = 0 := rfl

@[simp] theorem trivialUnitaryDatum_multiplier (p : PeriodDomain) :
    (trivialUnitaryDatum p).multiplier = (fun _ => 1) := rfl

@[simp] theorem trivialUnitaryDatum_factor_coe (p : PeriodDomain)
    (l : p.lattice) (x : ComplexPlane₂) :
    ((trivialUnitaryDatum p).factor.factor l x : ℂ) = 1 := by
  simp only [UnitaryDatum.factor_coe, trivialUnitaryDatum_form,
    trivialUnitaryDatum_multiplier, LinearMap.zero_apply, mul_zero, add_zero,
    Complex.exp_zero, mul_one]

/-- The defining equation of an actual entire theta function is exactly
the Appell--Humbert equation for its original unitary datum. -/
theorem unitaryDatum_theta_automorphy {p : PeriodDomain} (D : UnitaryDatum p)
    (θ : EntireThetaFunction D.factor) :
    PeriodTorusTheta.AppellHumbertAutomorphy p D.form D.multiplier θ.val := by
  intro l x
  simpa only [UnitaryDatum.factor_coe] using θ.property.2 l x

/-- Outside the actual exceptional set, a nonzero entire theta function
forces zero Hermitian form, trivial multiplier, and nonzero constancy. -/
theorem unitaryDatum_theta_constant_of_not_exceptional (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (D : UnitaryDatum (specialPeriodMap.point z))
    (θ : EntireThetaFunction D.factor) (hne : ∃ x, θ.val x ≠ 0) :
    D.form = 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ θ.val = (fun _ => c) ∧
      D.multiplier = (fun _ => 1) := by
  have hAuto : PeriodTorusTheta.AppellHumbertAutomorphy (specialPeriodMap.point z)
      (associatedSesquilinear D.imaginaryForm D.imaginaryForm_isTypeOneOne)
      D.multiplier θ.val := by
    rw [← D.form_eq_associatedSesquilinear]
    exact unitaryDatum_theta_automorphy D θ
  obtain ⟨hB, c, hc, hθ, hα⟩ := PeriodTorusTheta.theta_constant_of_not_exceptional z hz
    D.imaginaryForm D.imaginaryForm_self D.imaginaryForm_integral
    D.imaginaryForm_isTypeOneOne D.multiplier D.norm_multiplier θ.val
    (θ.property.1.differentiable (by simp)) hAuto hne
  refine ⟨?_, c, hc, hθ, funext hα⟩
  rw [D.form_eq_associatedSesquilinear]
  exact PeriodTorusTheta.associated_eq_zero_of_form_eq_zero
    D.imaginaryForm D.imaginaryForm_isTypeOneOne hB

theorem unitaryDatum_form_multiplier_of_nonzero_theta (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (D : UnitaryDatum (specialPeriodMap.point z))
    (θ : EntireThetaFunction D.factor) (hne : ∃ x, θ.val x ≠ 0) :
    D.form = 0 ∧ D.multiplier = (fun _ => 1) := by
  obtain ⟨hform, _, _, _, hmult⟩ :=
    unitaryDatum_theta_constant_of_not_exceptional z hz D θ hne
  exact ⟨hform, hmult⟩

/-- The datum itself, including its full unitary semicharacter, is trivial. -/
theorem unitaryDatum_eq_trivial_of_nonzero_theta (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (D : UnitaryDatum (specialPeriodMap.point z))
    (θ : EntireThetaFunction D.factor) (hne : ∃ x, θ.val x ≠ 0) :
    D = trivialUnitaryDatum (specialPeriodMap.point z) := by
  obtain ⟨hform, hmult⟩ := unitaryDatum_form_multiplier_of_nonzero_theta z hz D θ hne
  exact UnitaryDatum.ext hform hmult

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
