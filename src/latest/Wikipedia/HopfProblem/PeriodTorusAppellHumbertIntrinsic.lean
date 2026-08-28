import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactor
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegralCompleteness

/-!
# Factors of automorphy from intrinsic integral forms

The unique integer coefficient vector is recovered from an actual
alternating real form integral on the actual period lattice.  When the
form is of type `(1,1)`, the existing integral-factor construction then
realizes it without assuming a coefficient presentation.  Its underlying
Hermitian form is identified with the one associated to the original
real form by equality of imaginary parts.

This realizes intrinsic integral data; it does not classify arbitrary
line bundles or assert a Néron--Severi comparison.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

open PeriodTorusTypeOneOne

variable (p : PeriodDomain) (B : RealForm) (hAlt : ∀ x, B x x = 0)
  (hInt : IntegralOnPeriodLattice p B)

/-- The unique integer coefficients of the intrinsic form in the actual period marking. -/
def intrinsicCoefficients : Fin 6 → ℤ :=
  (existsUnique_tangentForm_of_integral p B hAlt hInt).choose

@[simp] theorem tangentForm_intrinsicCoefficients :
    tangentForm p (intrinsicCoefficients p B hAlt hInt) = B :=
  (existsUnique_tangentForm_of_integral p B hAlt hInt).choose_spec.1

theorem intrinsicCoefficients_unique (E : Fin 6 → ℤ) (hE : tangentForm p E = B) :
    E = intrinsicCoefficients p B hAlt hInt :=
  tangentForm_injective p (hE.trans (tangentForm_intrinsicCoefficients p B hAlt hInt).symm)

/-- The recovered coefficients are precisely the six actual period-basis pairings. -/
theorem intrinsicCoefficients_basis_pair (k : Fin 6) :
    (intrinsicCoefficients p B hAlt hInt k : ℝ) =
      B (p.basis (coefficientPair k).1) (p.basis (coefficientPair k).2) := by
  rw [← tangentForm_basis_pair p (intrinsicCoefficients p B hAlt hInt) k,
    tangentForm_intrinsicCoefficients]

/-- The canonical norm-one multiplier is constructed from the recovered coefficients. -/
def intrinsicMultiplier : p.lattice → ℂ :=
  latticeSemicharacter p (intrinsicCoefficients p B hAlt hInt)

@[simp] theorem intrinsicMultiplier_norm (l : p.lattice) :
    ‖intrinsicMultiplier p B hAlt hInt l‖ = 1 :=
  latticeSemicharacter_norm p (intrinsicCoefficients p B hAlt hInt) l

@[simp] theorem intrinsicMultiplier_zero : intrinsicMultiplier p B hAlt hInt 0 = 1 :=
  latticeSemicharacter_zero p (intrinsicCoefficients p B hAlt hInt)

variable (hType : IsTypeOneOne B)

include hType in
theorem intrinsicCoefficients_isTypeOneOne :
    IsTypeOneOne (tangentForm p (intrinsicCoefficients p B hAlt hInt)) := by
  rw [tangentForm_intrinsicCoefficients]
  exact hType

/-- The actual Hermitian form used by the integral-factor construction. -/
def intrinsicHermitian : PeriodTorusTheta.HermitianForm :=
  integralHermitian p (intrinsicCoefficients p B hAlt hInt)
    (intrinsicCoefficients_isTypeOneOne p B hAlt hInt hType)

@[simp] theorem intrinsicHermitian_im (x y : ComplexPlane₂) :
    (intrinsicHermitian p B hAlt hInt hType x y).im = B x y := by
  rw [intrinsicHermitian, integralHermitian_im, tangentForm_intrinsicCoefficients]

/-- Imaginary-part uniqueness identifies the constructed Hermitian form
with the intrinsic associated form, without a dependent rewrite. -/
theorem intrinsicHermitian_eq_associated :
    intrinsicHermitian p B hAlt hInt hType = associatedSesquilinear B hType :=
  eq_associatedSesquilinear_of_im B hType _ (intrinsicHermitian_im p B hAlt hInt hType)

theorem intrinsicHermitian_isHermitian :
    PeriodTorusTheta.IsHermitian (intrinsicHermitian p B hAlt hInt hType) :=
  integralHermitian_isHermitian p (intrinsicCoefficients p B hAlt hInt)
    (intrinsicCoefficients_isTypeOneOne p B hAlt hInt hType)

/-- The holomorphic factor realizing the intrinsic integral type-`(1,1)` data. -/
def intrinsicFactor : FactorOfAutomorphy p :=
  integralFactor p (intrinsicCoefficients p B hAlt hInt)
    (intrinsicCoefficients_isTypeOneOne p B hAlt hInt hType)

/-- Its explicit coefficient uses the original real form's associated
Hermitian form and the constructed norm-one multiplier. -/
@[simp] theorem intrinsicFactor_coe (l : p.lattice) (z : ComplexPlane₂) :
    ((intrinsicFactor p B hAlt hInt hType).factor l z : ℂ) =
      intrinsicMultiplier p B hAlt hInt l * Complex.exp
        ((Real.pi : ℂ) * associatedSesquilinear B hType z l +
          ((Real.pi : ℂ) / 2) * associatedSesquilinear B hType l l) := by
  change intrinsicMultiplier p B hAlt hInt l * Complex.exp
    ((Real.pi : ℂ) * intrinsicHermitian p B hAlt hInt hType z l +
      ((Real.pi : ℂ) / 2) * intrinsicHermitian p B hAlt hInt hType l l) = _
  rw [intrinsicHermitian_eq_associated]

theorem intrinsicFactor_holomorphic (l : p.lattice) :
    ContDiff ℂ ω (fun z => ((intrinsicFactor p B hAlt hInt hType).factor l z : ℂ)) :=
  (intrinsicFactor p B hAlt hInt hType).holomorphic_factor l

theorem intrinsicFactor_cocycle (l m : p.lattice) (z : ComplexPlane₂) :
    ((intrinsicFactor p B hAlt hInt hType).factor (l + m) z : ℂ) =
      ((intrinsicFactor p B hAlt hInt hType).factor l (z + m) : ℂ) *
        ((intrinsicFactor p B hAlt hInt hType).factor m z : ℂ) :=
  (intrinsicFactor p B hAlt hInt hType).factor_add_coe l m z

/-- The resulting factor law is exactly the theta automorphy law for the
intrinsic Hermitian form. -/
theorem intrinsicFactor_automorphy_iff (θ : ComplexPlane₂ → ℂ) :
    (∀ (l : p.lattice) z,
      θ (z + l) = ((intrinsicFactor p B hAlt hInt hType).factor l z : ℂ) * θ z) ↔
      PeriodTorusTheta.AppellHumbertAutomorphy p (associatedSesquilinear B hType)
        (intrinsicMultiplier p B hAlt hInt) θ := by
  simp only [intrinsicFactor_coe, PeriodTorusTheta.AppellHumbertAutomorphy]

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
