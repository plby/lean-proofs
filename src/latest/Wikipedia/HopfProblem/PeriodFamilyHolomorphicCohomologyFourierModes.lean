import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierContinuity
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierHermitian

/-!
# Continuous Hermitian inverse multipliers for the original Fourier modes

The formulas use the actual symbol of the marked period torus.  They vanish
at the zero frequency and solve the nonzero-frequency symbol equations.
For every original holomorphic period map, they depend continuously on the
base and on the input coefficient.  This is not an assertion of holomorphic
dependence: the formulas explicitly involve complex conjugation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier

open PeriodTorusLineBundleClassification

/-- The Hermitian primitive multiplier at an original integer frequency. -/
def modePotential (p : PeriodDomain) (k : Fin 4 → ℤ) (a : ComplexPlane₂) : ℂ :=
  FourierHermitian.potential (dolbeaultSymbol p (integerFrequency k)) a

/-- The Hermitian top-degree multiplier at an original integer frequency. -/
def modeTopInverse (p : PeriodDomain) (k : Fin 4 → ℤ) (h : ℂ) : ComplexPlane₂ :=
  FourierHermitian.topInverse (dolbeaultSymbol p (integerFrequency k)) h

@[simp] theorem modePotential_zero_frequency (p : PeriodDomain) (a : ComplexPlane₂) :
    modePotential p 0 a = 0 := by
  simp only [modePotential, integerFrequency_zero, map_zero,
    FourierHermitian.potential_zero_symbol]

@[simp] theorem modeTopInverse_zero_frequency (p : PeriodDomain) (h : ℂ) :
    modeTopInverse p 0 h = 0 := by
  simp only [modeTopInverse, integerFrequency_zero, map_zero,
    FourierHermitian.topInverse_zero_symbol]

/-- The compatible one-form equations remove exactly the constant Fourier mode. -/
theorem modePotential_equation (p : PeriodDomain) (k : Fin 4 → ℤ) (a : ComplexPlane₂)
    (hc : dolbeaultSymbol p (integerFrequency k) 0 * a 1 =
      dolbeaultSymbol p (integerFrequency k) 1 * a 0) (i : Fin 2) :
    dolbeaultSymbol p (integerFrequency k) i * modePotential p k a =
      a i - (if k = 0 then a i else 0) := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [if_neg hk, sub_zero]
    exact FourierHermitian.potential_mul _ a (dolbeaultSymbol_integer_ne_zero p hk) hc i

/-- The top-degree equation removes exactly the constant Fourier mode. -/
theorem modeTopInverse_equation (p : PeriodDomain) (k : Fin 4 → ℤ) (h : ℂ) :
    dolbeaultSymbol p (integerFrequency k) 0 * modeTopInverse p k h 1 -
      dolbeaultSymbol p (integerFrequency k) 1 * modeTopInverse p k h 0 =
        h - (if k = 0 then h else 0) := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [if_neg hk, sub_zero]
    exact FourierHermitian.topInverse_equation _ h (dolbeaultSymbol_integer_ne_zero p hk)

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- Joint continuity of the actual primitive multiplier in the base and input. -/
theorem continuous_modePotential (k : Fin 4 → ℤ) :
    Continuous (fun x : B × ComplexPlane₂ => modePotential (P.point x.1) k x.2) := by
  by_cases hk : k = 0
  · subst k
    simpa only [modePotential_zero_frequency] using
      (continuous_const : Continuous (fun _ : B × ComplexPlane₂ => (0 : ℂ)))
  · apply FourierHermitian.potential_contDiffOn.continuousOn.comp_continuous
      (f := fun x : B × ComplexPlane₂ =>
        (dolbeaultSymbol (P.point x.1) (integerFrequency k), x.2))
    · exact ((continuous_integerSymbol P k).comp continuous_fst).prodMk continuous_snd
    · intro x
      exact dolbeaultSymbol_integer_ne_zero (P.point x.1) hk

/-- Joint continuity of the actual top inverse in the base and input. -/
theorem continuous_modeTopInverse (k : Fin 4 → ℤ) :
    Continuous (fun x : B × ℂ => modeTopInverse (P.point x.1) k x.2) := by
  by_cases hk : k = 0
  · subst k
    simpa only [modeTopInverse_zero_frequency] using
      (continuous_const : Continuous (fun _ : B × ℂ => (0 : ComplexPlane₂)))
  · apply FourierHermitian.topInverse_contDiffOn.continuousOn.comp_continuous
      (f := fun x : B × ℂ =>
        (dolbeaultSymbol (P.point x.1) (integerFrequency k), x.2))
    · exact ((continuous_integerSymbol P k).comp continuous_fst).prodMk continuous_snd
    · intro x
      exact dolbeaultSymbol_integer_ne_zero (P.point x.1) hk

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier
