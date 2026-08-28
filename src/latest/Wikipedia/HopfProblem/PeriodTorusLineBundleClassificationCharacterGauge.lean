import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterNormalization
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactorBasic

/-!
# The exponential gauge for normalized lattice characters

Constant characters give the actual zero-Hermitian-form factors. The
exponential of the constructed complex-linear part is an everywhere nonzero
entire gauge from the normalized unitary factor to the original factor.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert

variable {p : PeriodDomain}

/-- The genuine zero-Hermitian-form Appell--Humbert factor of a character. -/
def constantCharacterFactor (ρ : LatticeCharacter p) : FactorOfAutomorphy p :=
  hermitianFactor p 0 (by intro x y; simp)
    (characterValue ρ) (characterValue_zero ρ) (characterValue_ne_zero ρ)
    (by intro l m; simpa using characterValue_add ρ l m)

@[simp]
theorem constantCharacterFactor_coe (ρ : LatticeCharacter p) (l : p.lattice)
    (z : ComplexPlane₂) :
    ((constantCharacterFactor ρ).factor l z : ℂ) = characterValue ρ l := by
  change characterValue ρ l * Complex.exp (appellHumbertExponent 0 l z) = _
  simp [appellHumbertExponent]

theorem constantCharacterFactor_factor (ρ : LatticeCharacter p) (l : p.lattice)
    (z : ComplexPlane₂) :
    (constantCharacterFactor ρ).factor l z = ρ (Multiplicative.ofAdd l) := by
  apply Units.ext
  exact constantCharacterFactor_coe ρ l z

/-- The entire exponential gauge, with value one at the origin. -/
def characterGauge (ρ : LatticeCharacter p) (z : ComplexPlane₂) : ℂ :=
  Complex.exp (characterLinear ρ z)

@[simp]
theorem characterGauge_zero (ρ : LatticeCharacter p) : characterGauge ρ 0 = 1 := by
  simp [characterGauge]

theorem characterGauge_ne_zero (ρ : LatticeCharacter p) (z : ComplexPlane₂) :
    characterGauge ρ z ≠ 0 := Complex.exp_ne_zero _

theorem characterGauge_holomorphic (ρ : LatticeCharacter p) :
    ContDiff ℂ ω (characterGauge ρ) :=
  (characterLinear ρ).toContinuousLinearMap.contDiff.cexp

/-- The sign and direction agree with positive lattice translation:
the gauge maps the unitary-character factor to the original factor. -/
theorem characterGauge_factor_relation (ρ : LatticeCharacter p) (l : p.lattice)
    (z : ComplexPlane₂) :
    characterGauge ρ (z + l) *
        ((constantCharacterFactor (unitaryCharacter ρ)).factor l z : ℂ) =
      ((constantCharacterFactor ρ).factor l z : ℂ) * characterGauge ρ z := by
  simp only [constantCharacterFactor_coe, characterGauge, map_add, Complex.exp_add]
  rw [character_decomposition ρ l]
  ring

theorem characterGauge_automorphy (ρ : LatticeCharacter p) (l : p.lattice)
    (z : ComplexPlane₂) :
    characterGauge ρ (z + l) = characterValue ρ l /
      characterValue (unitaryCharacter ρ) l * characterGauge ρ z := by
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (characterValue_ne_zero (unitaryCharacter ρ) l)).mpr
  simpa only [constantCharacterFactor_coe] using characterGauge_factor_relation ρ l z

/-- Multiplication by the genuine gauge transports the full automorphy law. -/
theorem characterGauge_automorphy_iff (ρ : LatticeCharacter p) (θ : ComplexPlane₂ → ℂ) :
    (∀ l : p.lattice, ∀ z, θ (z + l) =
      ((constantCharacterFactor (unitaryCharacter ρ)).factor l z : ℂ) * θ z) ↔
    (∀ l : p.lattice, ∀ z, characterGauge ρ (z + l) * θ (z + l) =
      ((constantCharacterFactor ρ).factor l z : ℂ) * (characterGauge ρ z * θ z)) := by
  constructor
  · intro h l z
    rw [h l z, ← mul_assoc, characterGauge_factor_relation, mul_assoc]
  · intro h l z
    apply mul_left_cancel₀ (characterGauge_ne_zero ρ (z + l))
    calc
      characterGauge ρ (z + l) * θ (z + l) =
          ((constantCharacterFactor ρ).factor l z : ℂ) *
            (characterGauge ρ z * θ z) := h l z
      _ = (characterGauge ρ (z + l) *
          ((constantCharacterFactor (unitaryCharacter ρ)).factor l z : ℂ)) * θ z := by
        rw [characterGauge_factor_relation, mul_assoc]
      _ = _ := mul_assoc _ _ _

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
