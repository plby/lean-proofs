import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterLinear
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Normalization of actual constant lattice characters

Every nonzero complex character of the actual period lattice is uniquely the
product of a unitary character and the exponential of a complex-linear
functional on the covering plane. Both factors are constructed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable {p : PeriodDomain}

/-- The uniquely determined complex-linear part of a lattice character. -/
def characterLinear (ρ : LatticeCharacter p) : ComplexPlane₂ →ₗ[ℂ] ℂ :=
  complexLinearOfReal (characterRealLinear ρ)

theorem characterLinear_apply (ρ : LatticeCharacter p) (z : ComplexPlane₂) :
    characterLinear ρ z = (characterRealLinear ρ z : ℂ) -
      Complex.I * (characterRealLinear ρ (Complex.I • z) : ℂ) := rfl

@[simp]
theorem characterLinear_re (ρ : LatticeCharacter p) (z : ComplexPlane₂) :
    (characterLinear ρ z).re = characterRealLinear ρ z :=
  complexLinearOfReal_re _ _

theorem characterLinear_re_lattice (ρ : LatticeCharacter p) (l : p.lattice) :
    (characterLinear ρ (l : ComplexPlane₂)).re = logNormCharacter ρ l := by
  rw [characterLinear_re, characterRealLinear_lattice]

/-- Exponentiating a genuine complex-linear functional gives an actual
character of the lattice, with values in the units. -/
def linearExponentialCharacter (ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ) : LatticeCharacter p where
  toFun g := Units.mk0 (Complex.exp (ℓ ((Multiplicative.toAdd g : p.lattice) : ComplexPlane₂)))
    (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    change Complex.exp (ℓ (0 : ComplexPlane₂)) = 1
    simp
  map_mul' g h := by
    apply Units.ext
    change Complex.exp (ℓ ((Multiplicative.toAdd g + Multiplicative.toAdd h : p.lattice) :
      ComplexPlane₂)) = Complex.exp (ℓ ((Multiplicative.toAdd g : p.lattice) : ComplexPlane₂)) *
        Complex.exp (ℓ ((Multiplicative.toAdd h : p.lattice) : ComplexPlane₂))
    rw [Submodule.coe_add, map_add, Complex.exp_add]

@[simp]
theorem linearExponentialCharacter_value (ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ) (l : p.lattice) :
    characterValue (linearExponentialCharacter ℓ) l =
      Complex.exp (ℓ (l : ComplexPlane₂)) := rfl

theorem characterValue_mul (ρ σ : LatticeCharacter p) (l : p.lattice) :
    characterValue (ρ * σ) l = characterValue ρ l * characterValue σ l := rfl

/-- A unitary character has norm one on every actual lattice vector. -/
def IsUnitaryCharacter (α : LatticeCharacter p) : Prop :=
  ∀ l : p.lattice, ‖characterValue α l‖ = 1

/-- Remove the uniquely determined exponential modulus from the character. -/
def unitaryCharacter (ρ : LatticeCharacter p) : LatticeCharacter p :=
  ρ * linearExponentialCharacter (-characterLinear ρ)

theorem unitaryCharacter_value (ρ : LatticeCharacter p) (l : p.lattice) :
    characterValue (unitaryCharacter ρ) l = characterValue ρ l *
      Complex.exp (-(characterLinear ρ (l : ComplexPlane₂))) := rfl

theorem unitaryCharacter_isUnitary (ρ : LatticeCharacter p) :
    IsUnitaryCharacter (unitaryCharacter ρ) := by
  intro l
  rw [unitaryCharacter_value, norm_mul, Complex.norm_exp, Complex.neg_re,
    characterLinear_re_lattice, logNormCharacter_apply, Real.exp_neg,
    Real.exp_log (norm_pos_iff.mpr (characterValue_ne_zero ρ l))]
  exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr (characterValue_ne_zero ρ l))

/-- The canonical decomposition, evaluated on the actual lattice. -/
theorem character_decomposition (ρ : LatticeCharacter p) (l : p.lattice) :
    characterValue ρ l = characterValue (unitaryCharacter ρ) l *
      Complex.exp (characterLinear ρ (l : ComplexPlane₂)) := by
  rw [unitaryCharacter_value, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

theorem character_decomposition_hom (ρ : LatticeCharacter p) :
    ρ = unitaryCharacter ρ * linearExponentialCharacter (characterLinear ρ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  exact character_decomposition ρ (Multiplicative.toAdd g)

/-- Any decomposition with unitary first factor has the constructed
complex-linear second factor and the constructed unitary first factor. -/
theorem character_decomposition_unique (ρ α : LatticeCharacter p)
    (ℓ : ComplexPlane₂ →ₗ[ℂ] ℂ) (hα : IsUnitaryCharacter α)
    (h : ∀ l : p.lattice, characterValue ρ l = characterValue α l *
      Complex.exp (ℓ (l : ComplexPlane₂))) :
    α = unitaryCharacter ρ ∧ ℓ = characterLinear ρ := by
  have hlog (l : p.lattice) : (ℓ (l : ComplexPlane₂)).re = logNormCharacter ρ l := by
    have hn := congrArg norm (h l)
    rw [norm_mul, hα l, one_mul, Complex.norm_exp] at hn
    rw [logNormCharacter_apply, hn, Real.log_exp]
  have hre : realPartLinear ℓ = characterRealLinear ρ :=
    characterRealLinear_unique ρ (realPartLinear ℓ) hlog
  have hℓ : ℓ = characterLinear ρ := by
    apply complexLinearOfReal_unique
    intro z
    exact LinearMap.congr_fun hre z
  refine ⟨?_, hℓ⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have hc := (h (Multiplicative.toAdd g)).symm.trans
    (character_decomposition ρ (Multiplicative.toAdd g))
  rw [hℓ] at hc
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) hc

theorem existsUnique_unitary_exponential_decomposition (ρ : LatticeCharacter p) :
    ∃! d : LatticeCharacter p × (ComplexPlane₂ →ₗ[ℂ] ℂ),
      IsUnitaryCharacter d.1 ∧ ∀ l : p.lattice,
        characterValue ρ l = characterValue d.1 l *
          Complex.exp (d.2 (l : ComplexPlane₂)) := by
  refine ⟨⟨unitaryCharacter ρ, characterLinear ρ⟩,
    ⟨unitaryCharacter_isUnitary ρ, character_decomposition ρ⟩, ?_⟩
  rintro ⟨α, ℓ⟩ ⟨hα, h⟩
  obtain ⟨rfl, rfl⟩ := character_decomposition_unique ρ α ℓ hα h
  rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
