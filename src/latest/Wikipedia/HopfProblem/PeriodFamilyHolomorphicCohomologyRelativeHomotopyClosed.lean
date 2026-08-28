import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyBase
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperators

/-!
# Actual closed relative triples and their original Fourier equations

The three equations use the genuine scalar differential operators on
smooth functions, not an assumed relation between formal Fourier data.
Their original Haar coefficients satisfy the symbol equations by the
proved differentiation formulas. In particular the two vertical means
are genuinely holomorphic in the original base.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierParameter FourierSynthesis RelativeOperators MarkedLinear
  PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The literal closedness equations for a smooth triple in the original relative frame. -/
structure IsClosedTriple (a₀ : SmoothFamily U (Fin 4))
    (a : Fin 2 → SmoothFamily U (Fin 4)) : Prop where
  vertical : ∀ x, d1 P (a 1) x = d2 P (a 0) x
  base_first : ∀ x, d0 (a 0) x = d1 P a₀ x
  base_second : ∀ x, d0 (a 1) x = d2 P a₀ x

variable {P} {a₀ : SmoothFamily U (Fin 4)} {a : Fin 2 → SmoothFamily U (Fin 4)}

/-- Equality of actual smooth family functions gives equality of their genuine Haar coefficients. -/
theorem coefficientValue_eq_of_forall {f g : SmoothFamily U (Fin 4)}
    (h : ∀ x, f x = g x) (b : U) (k : Frequency) :
    f.coefficientValue k (b : ℂ) = g.coefficientValue k (b : ℂ) := by
  simp only [SmoothFamily.coefficientValue_apply]
  exact congrArg (fun v : UnitAddTorus (Fin 4) → ℂ => mFourierCoeff v k)
    (funext fun t => h (b, t))

/-- The actual vertical closedness equation gives the original two-component Fourier relation. -/
theorem IsClosedTriple.vertical_coefficients (h : IsClosedTriple P a₀ a)
    (b : U) (k : Frequency) :
    relativeSymbol (P.point b) (integerFrequency k) 0 * (a 1).coefficientValue k (b : ℂ) =
      relativeSymbol (P.point b) (integerFrequency k) 1 * (a 0).coefficientValue k (b : ℂ) := by
  have heq := coefficientValue_eq_of_forall h.vertical b k
  rwa [coefficientValue_d1, coefficientValue_d2] at heq

/-- The actual base closedness equations give the original antiholomorphic coefficient equations. -/
theorem IsClosedTriple.base_coefficients (h : IsClosedTriple P a₀ a)
    (b : U) (j : Fin 2) (k : Frequency) :
    baseDbarCoefficients (a j).coefficientValue k (b : ℂ) =
      relativeSymbol (P.point b) (integerFrequency k) j * a₀.coefficientValue k (b : ℂ) := by
  fin_cases j
  · have heq := coefficientValue_eq_of_forall h.base_first b k
    rwa [coefficientValue_d0, coefficientValue_d1, ← baseDbarCoefficients_apply] at heq
  · have heq := coefficientValue_eq_of_forall h.base_second b k
    rwa [coefficientValue_d0, coefficientValue_d2, ← baseDbarCoefficients_apply] at heq

/-- The actual mean of each vertical coefficient has zero antiholomorphic base derivative. -/
theorem IsClosedTriple.vertical_mean_dbar_zero (h : IsClosedTriple P a₀ a)
    (b : U) (j : Fin 2) :
    (d0 (a j)).coefficientValue 0 (b : ℂ) = 0 := by
  rw [coefficientValue_d0, ← baseDbarCoefficients_apply]
  simpa only [integerFrequency_zero, map_zero, Pi.zero_apply, zero_mul]
    using h.base_coefficients b j 0

/-- The original vertical Haar means are genuinely holomorphic on the original open base. -/
theorem IsClosedTriple.vertical_mean_differentiableOn (h : IsClosedTriple P a₀ a)
    (j : Fin 2) : DifferentiableOn ℂ ((a j).coefficientValue 0) U :=
  coefficientValue_differentiableOn_of_d0_zero (a j) 0
    (fun b => h.vertical_mean_dbar_zero b j)

/-- Native holomorphicity uses the unchanged open-subtype complex atlas. -/
theorem IsClosedTriple.vertical_mean_contMDiff (h : IsClosedTriple P a₀ a) (j : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun b : U => (a j).coefficientValue 0 (b : ℂ)) := by
  rw [← contMDiffOn_univ]
  exact ((h.vertical_mean_differentiableOn j).contDiffOn U.isOpen).contMDiffOn.comp
    contMDiff_subtype_val.contMDiffOn (fun b _ => b.property)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
