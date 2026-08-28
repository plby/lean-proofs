import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearReduction

/-!
# The actual Fourier symbol in the holomorphic period-coordinate frame

Changing from the two native antiholomorphic coordinate coefficients to
the first two marked period primitives gives a symbol involving only
the original period entries, without conjugates or inverse periods.
Its nondegeneracy is a consequence of the already proved nondegeneracy
of the original Fourier symbol and the actual frame comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear

open Complex PeriodTorusLineBundleClassification
open scoped Matrix BigOperators

/-- Regard actual real frequency coordinates as complex period values. -/
def realCoefficients : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℂ) where
  toFun v j := (v j : ℂ)
  map_add' v w := by ext j; simp
  map_smul' r v := by ext j; simp [Complex.real_smul]

@[simp] theorem realCoefficients_apply (v : Fin 4 → ℝ) (j : Fin 4) :
    realCoefficients v j = (v j : ℂ) := rfl

/-- The genuine real-frequency primitive is the complex embedding of
the original real frequency functional. -/
theorem primitive_realCoefficients (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) :
    primitive p (realCoefficients v) z = (frequencyFunctional p v z : ℂ) := by
  simp [primitive_apply, frequencyFunctional_apply, Complex.ofReal_sum, Complex.ofReal_mul]

/-- The actual original Fourier symbol is the derivative of its
literal exponential frequency, with the original `2πI` normalization. -/
theorem dolbeaultSymbol_eq_smul_dbar (p : PeriodDomain) (v : Fin 4 → ℝ) :
    dolbeaultSymbol p v = (2 * (Real.pi : ℂ) * I) • dbarLinear p (realCoefficients v) := by
  ext i
  simp only [dolbeaultSymbol_apply, Pi.smul_apply, smul_eq_mul,
    dbarLinear_apply, primitive_realCoefficients]
  ring_nf
  simp only [I_sq]
  ring

/-- The actual vertical Fourier symbol in the two marked period-coordinate
forms. Its displayed coefficients use only the original period matrix. -/
def relativeSymbol (p : PeriodDomain) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ) :=
  (2 * (Real.pi : ℂ) * I) • ((reduction p).restrictScalars ℝ).comp realCoefficients

@[simp] theorem relativeSymbol_apply (p : PeriodDomain) (v : Fin 4 → ℝ) :
    relativeSymbol p v = (2 * (Real.pi : ℂ) * I) • reduction p (realCoefficients v) := rfl

/-- Literal first relative symbol coefficient in the original period entries. -/
theorem relativeSymbol_zero (p : PeriodDomain) (v : Fin 4 → ℝ) :
    relativeSymbol p v 0 = (2 * (Real.pi : ℂ) * I) *
      ((v 0 : ℂ) - (6 * p.val.μ * (v 2 : ℂ) + p.val.β * (v 3 : ℂ))) := rfl

/-- Literal second relative symbol coefficient in the original period entries. -/
theorem relativeSymbol_one (p : PeriodDomain) (v : Fin 4 → ℝ) :
    relativeSymbol p v 1 = (2 * (Real.pi : ℂ) * I) *
      ((v 1 : ℂ) - (p.val.τ * (v 2 : ℂ) + p.val.μ * (v 3 : ℂ))) := rfl

/-- The proved native frame change sends the relative symbol to the
original Fourier symbol, exactly and with its original normalization. -/
theorem firstDbarEquiv_relativeSymbol (p : PeriodDomain) (v : Fin 4 → ℝ) :
    firstDbarEquiv p (relativeSymbol p v) = dolbeaultSymbol p v := by
  rw [relativeSymbol_apply, map_smul, ← dbarLinear_eq_firstDbar_reduction,
    dolbeaultSymbol_eq_smul_dbar]

/-- No real frequency is lost by passing to the actual marked frame. -/
theorem relativeSymbol_injective (p : PeriodDomain) :
    Function.Injective (relativeSymbol p) := by
  intro v w h
  apply dolbeaultSymbol_injective p
  simpa only [firstDbarEquiv_relativeSymbol] using congrArg (firstDbarEquiv p) h

theorem relativeSymbol_ne_zero (p : PeriodDomain) {v : Fin 4 → ℝ} (hv : v ≠ 0) :
    relativeSymbol p v ≠ 0 := by
  intro h
  apply hv
  apply relativeSymbol_injective p
  simpa only [map_zero] using h

/-- The actual relative symbol has a genuine positive elliptic lower bound. -/
theorem relativeSymbol_exists_pos_lowerBound (p : PeriodDomain) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin 4 → ℝ, c * ‖v‖ ≤ ‖relativeSymbol p v‖ := by
  obtain ⟨K, _, hK⟩ :=
    (relativeSymbol p).injective_iff_antilipschitz.mp (relativeSymbol_injective p)
  exact antilipschitzWith_iff_exists_mul_le_norm.mp ⟨K, hK⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear
