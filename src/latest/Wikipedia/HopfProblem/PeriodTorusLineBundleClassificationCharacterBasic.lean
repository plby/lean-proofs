import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The real logarithmic modulus of a lattice character

The logarithm of the norm is an additive real character. Its values on
the four actual period-basis vectors extend uniquely to a real-linear
functional on the actual covering plane.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

abbrev LatticeCharacter (p : PeriodDomain) := Multiplicative p.lattice →* ℂˣ

variable {p : PeriodDomain}

def characterValue (ρ : LatticeCharacter p) (l : p.lattice) : ℂ :=
  (ρ (Multiplicative.ofAdd l) : ℂ)

@[simp]
theorem characterValue_zero (ρ : LatticeCharacter p) : characterValue ρ 0 = 1 := by
  change (ρ 1 : ℂ) = 1
  rw [map_one]
  rfl

theorem characterValue_add (ρ : LatticeCharacter p) (l m : p.lattice) :
    characterValue ρ (l + m) = characterValue ρ l * characterValue ρ m := by
  change (ρ (Multiplicative.ofAdd l * Multiplicative.ofAdd m) : ℂ) = _
  rw [map_mul]
  rfl

theorem characterValue_ne_zero (ρ : LatticeCharacter p) (l : p.lattice) :
    characterValue ρ l ≠ 0 := (ρ (Multiplicative.ofAdd l)).ne_zero

/-- The actual real additive character given by the logarithmic modulus. -/
def logNormCharacter (ρ : LatticeCharacter p) : p.lattice →+ ℝ where
  toFun l := Real.log ‖characterValue ρ l‖
  map_zero' := by simp
  map_add' l m := by
    rw [characterValue_add, norm_mul]
    exact Real.log_mul (norm_ne_zero_iff.mpr (characterValue_ne_zero ρ l))
      (norm_ne_zero_iff.mpr (characterValue_ne_zero ρ m))

@[simp]
theorem logNormCharacter_apply (ρ : LatticeCharacter p) (l : p.lattice) :
    logNormCharacter ρ l = Real.log ‖characterValue ρ l‖ := rfl

/-- Each actual real period-basis vector is a member of the actual lattice. -/
def latticeBasisVector (p : PeriodDomain) (i : Fin 4) : p.lattice :=
  ⟨p.basis i, by
    rw [p.lattice_eq_span_basis]
    exact Submodule.subset_span ⟨i, rfl⟩⟩

@[simp]
theorem latticeBasisVector_coe (p : PeriodDomain) (i : Fin 4) :
    (latticeBasisVector p i : ComplexPlane₂) = p.basis i := rfl

/-- The real-linear extension is constructed using the actual period basis. -/
def characterRealLinear (ρ : LatticeCharacter p) : ComplexPlane₂ →ₗ[ℝ] ℝ :=
  p.basis.constr ℝ (fun i => logNormCharacter ρ (latticeBasisVector p i))

@[simp]
theorem characterRealLinear_basis (ρ : LatticeCharacter p) (i : Fin 4) :
    characterRealLinear ρ (p.basis i) = logNormCharacter ρ (latticeBasisVector p i) := by
  simp [characterRealLinear]

theorem characterRealLinear_lattice (ρ : LatticeCharacter p) (l : p.lattice) :
    characterRealLinear ρ (l : ComplexPlane₂) = logNormCharacter ρ l := by
  classical
  let c := p.latticeEquiv l
  have hx : (l : ComplexPlane₂) = ∑ i, c i • p.basis i :=
    (p.periodVector_latticeEquiv l).symm.trans (p.periodVector_eq_sum c)
  have hl : l = ∑ i, c i • latticeBasisVector p i := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, latticeBasisVector_coe] using hx
  have hlog : logNormCharacter ρ l = ∑ i, c i • logNormCharacter ρ (latticeBasisVector p i) := by
    rw [hl, map_sum]
    simp only [map_zsmul]
  rw [hx, map_sum, hlog]
  simp only [map_zsmul, characterRealLinear_basis]

theorem characterRealLinear_unique (ρ : LatticeCharacter p)
    (ν : ComplexPlane₂ →ₗ[ℝ] ℝ)
    (hν : ∀ l : p.lattice, ν (l : ComplexPlane₂) = logNormCharacter ρ l) :
    ν = characterRealLinear ρ := by
  apply p.basis.ext
  intro i
  rw [characterRealLinear_basis]
  exact hν (latticeBasisVector p i)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
