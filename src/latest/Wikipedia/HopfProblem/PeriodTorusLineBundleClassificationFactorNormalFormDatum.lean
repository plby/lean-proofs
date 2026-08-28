import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorComparisonLog
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterNormalization
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessData

/-!
# Genuine unitary Appell--Humbert data with character twists

The unitary character is retained in the multiplier. Its semicharacter
law and the actual factor identity are checked for the original positive
lattice-action convention.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusTypeOneOne
open PeriodTorusLineBundleClassificationUniqueness

def twistedIntegralDatum (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E))
    (α : LatticeCharacter p) (hα : IsUnitaryCharacter α) : UnitaryDatum p where
  form := integralHermitian p E hType
  hermitian := integralHermitian_isHermitian p E hType
  multiplier l := latticeSemicharacter p E l * characterValue α l
  norm_multiplier l := by
    rw [norm_mul, latticeSemicharacter_norm, hα, one_mul]
  multiplier_add l m := by
    rw [latticeSemicharacter_add_neg, characterValue_add,
      integralHermitian_lattice_im, Complex.ofReal_intCast]
    ring

@[simp]
theorem twistedIntegralDatum_form (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E))
    (α : LatticeCharacter p) (hα : IsUnitaryCharacter α) :
    (twistedIntegralDatum p E hType α hα).form = integralHermitian p E hType := rfl

@[simp]
theorem twistedIntegralDatum_multiplier (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E))
    (α : LatticeCharacter p) (hα : IsUnitaryCharacter α) (l : p.lattice) :
    (twistedIntegralDatum p E hType α hα).multiplier l =
      latticeSemicharacter p E l * characterValue α l := rfl

/-- The associated factor is the genuine canonical factor multiplied by
the actual unitary character. -/
theorem twistedIntegralDatum_factor_coe (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E))
    (α : LatticeCharacter p) (hα : IsUnitaryCharacter α)
    (l : p.lattice) (z : ComplexPlane₂) :
    ((twistedIntegralDatum p E hType α hα).factor.factor l z : ℂ) =
      characterValue α l * ((integralFactor p E hType).factor l z : ℂ) := by
  rw [UnitaryDatum.factor_coe, twistedIntegralDatum_form,
    twistedIntegralDatum_multiplier, integralFactor_coe]
  ring

/-- Unit-normalized data for the actual derived integral form of a factor. -/
def normalizedFactorDatum {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (ρ : LatticeCharacter p) : UnitaryDatum p :=
  twistedIntegralDatum p (factorIntegralCoefficients F) (factorIntegralCoefficients_typeOneOne F)
    (unitaryCharacter ρ) (unitaryCharacter_isUnitary ρ)

theorem normalizedFactorDatum_factor_coe {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (ρ : LatticeCharacter p) (l : p.lattice) (z : ComplexPlane₂) :
    ((normalizedFactorDatum F ρ).factor.factor l z : ℂ) =
      characterValue (unitaryCharacter ρ) l * ((factorReference F).factor l z : ℂ) :=
  twistedIntegralDatum_factor_coe p _ _ _ _ l z

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
