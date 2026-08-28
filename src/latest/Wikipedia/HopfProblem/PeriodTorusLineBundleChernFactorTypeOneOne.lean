import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassEvaluation
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorTypeOneOne
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingRealForms

/-!
# Type `(1,1)` and realization for the genuine first Chern classes of factors

The actual logarithmic periods identify every factor's winding-defined first
Chern class with the negative of its extracted integral coefficients. The
proved holomorphic-factor type condition therefore applies to its actual
native cohomology real form. Conversely, the existing canonical negative-form
construction realizes every integral type `(1,1)` native class.

These statements concern actual factors of automorphy and their native
bundles. No classification of arbitrary bundles or Néron--Severi group is
introduced here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open FirstHurewicz SingularCohomologyFree PeriodTorusHigherHomologyPontryagin
open PeriodTorusAppellHumbert PeriodTorusTypeOneOne PeriodTorusLineBundleClassification
open PeriodTorusCohomology

/-- The genuine first Chern class is the negative extracted logarithmic coefficient class. -/
theorem firstChernClass_eq_coefficientClass_neg_factorIntegralCoefficients
    {p : PeriodDomain} (F : FactorOfAutomorphy p) :
    firstChernClass F = coefficientClass p (-factorIntegralCoefficients F) := by
  have hneg : coefficientClass p (-factorIntegralCoefficients F) =
      -coefficientClass p (factorIntegralCoefficients F) :=
    map_neg (coefficientClassEquiv p) _
  rw [hneg]
  apply cohomology_ext_periodLoops p
  intro x y
  rw [firstChernClass_evaluate_periodLoops, map_neg, LinearMap.neg_apply,
    coefficientClass_evaluate_periodLoops]
  simpa only [AddEquiv.apply_symm_apply] using
    congrArg Neg.neg
      (factorIntegralCoefficients_spec F (p.latticeEquiv.symm x)
        (p.latticeEquiv.symm y)).symm

/-- The six actual native cohomology coefficients retain the proved negative sign. -/
theorem firstChernClass_coefficients {p : PeriodDomain} (F : FactorOfAutomorphy p) :
    (coefficientClassEquiv p).symm (firstChernClass F) = -factorIntegralCoefficients F := by
  rw [firstChernClass_eq_coefficientClass_neg_factorIntegralCoefficients]
  exact (coefficientClassEquiv p).symm_apply_apply _

/-- The actual real form of the native first Chern class has the extracted signed periods. -/
theorem firstChernClass_cohomologyRealForm {p : PeriodDomain} (F : FactorOfAutomorphy p) :
    cohomologyRealForm p (firstChernClass F) = tangentForm p (-factorIntegralCoefficients F) := by
  rw [firstChernClass_eq_coefficientClass_neg_factorIntegralCoefficients,
    cohomologyRealForm_coefficientClass]

/-- Holomorphicity of every actual factor forces its genuine native Chern class to be `(1,1)`. -/
theorem firstChernClass_isTypeOneOne {p : PeriodDomain} (F : FactorOfAutomorphy p) :
    IsTypeOneOne (cohomologyRealForm p (firstChernClass F)) := by
  rw [firstChernClass_cohomologyRealForm]
  exact integralType_neg p (factorIntegralCoefficients F)
    (factorIntegralCoefficients_typeOneOne F)

/-- Exactly the integral native classes of type `(1,1)` are realized by actual factor bundles. -/
theorem exists_factor_firstChernClass_iff_typeOneOne (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    (∃ F : FactorOfAutomorphy p, firstChernClass F = a) ↔
      IsTypeOneOne (cohomologyRealForm p a) := by
  constructor
  · rintro ⟨F, rfl⟩
    exact firstChernClass_isTypeOneOne F
  · intro ha
    let E : Fin 6 → ℤ := (coefficientClassEquiv p).symm a
    have hType : IsTypeOneOne (tangentForm p E) := ha
    obtain ⟨F, hF⟩ := exists_factor_firstChernClass p E hType
    exact ⟨F, hF.trans ((coefficientClassEquiv p).apply_symm_apply a)⟩

/-- Coefficient form of the exact realization criterion, with no assumed Chern comparison. -/
theorem exists_factor_firstChernClass_coefficient_iff (p : PeriodDomain) (E : Fin 6 → ℤ) :
    (∃ F : FactorOfAutomorphy p, firstChernClass F = coefficientClass p E) ↔
      IsTypeOneOne (tangentForm p E) := by
  rw [exists_factor_firstChernClass_iff_typeOneOne, cohomologyRealForm_coefficientClass]

/-- The same realization criterion expressed intrinsically on actual real period forms. -/
theorem exists_factor_firstChernClass_realForm_iff (p : PeriodDomain) (B : RealForm) :
    (∃ F : FactorOfAutomorphy p, cohomologyRealForm p (firstChernClass F) = B) ↔
      (∀ x, B x x = 0) ∧ IntegralOnPeriodLattice p B ∧ IsTypeOneOne B := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨cohomologyRealForm_self p _, cohomologyRealForm_integral p _,
      firstChernClass_isTypeOneOne F⟩
  · rintro ⟨hAlt, hIntegral, hType⟩
    obtain ⟨a, ha, _⟩ := existsUnique_cohomologyRealForm_of_integral p B hAlt hIntegral
    have haType : IsTypeOneOne (cohomologyRealForm p a) := ha.symm ▸ hType
    obtain ⟨F, hF⟩ := (exists_factor_firstChernClass_iff_typeOneOne p a).mpr haType
    exact ⟨F, (congrArg (cohomologyRealForm p) hF).trans ha⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
