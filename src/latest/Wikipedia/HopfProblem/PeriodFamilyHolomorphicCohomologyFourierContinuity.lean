import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSymbol

/-!
# Continuity of the genuine period-family Dolbeault symbol

The symbol is the one already used for the actual period torus, with the inverse
of its actual marked period isomorphism.  Its dependence on the base follows
from the holomorphic period functions; continuity of an abstract symbol family
is not an extra hypothesis.  Finite-dimensionality upgrades joint evaluation
continuity to continuity in the operator norm.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier

open Complex
open PeriodTorusLineBundleClassification
open scoped BigOperators

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- The inverse coordinates are those of the original marked period torus. -/
theorem continuous_inversePeriodCoordinates :
    Continuous (fun x : B × ComplexPlane₂ =>
      (PeriodTorusTypeOneOne.periodEquiv (P.point x.1)).symm x.2) :=
  P.continuous_periodEquiv_symm

/-- An individual inverse-period coordinate, retaining the native period map. -/
theorem continuous_inversePeriodCoordinate (j : Fin 4) :
    Continuous (fun x : B × ComplexPlane₂ =>
      ((PeriodTorusTypeOneOne.periodEquiv (P.point x.1)).symm x.2) j) :=
  (continuous_apply j).comp (continuous_inversePeriodCoordinates P)

/-- Each term in the native frequency functional varies continuously. -/
theorem continuous_frequencyTerm (j : Fin 4) :
    Continuous (fun x : B × (Fin 4 → ℝ) × ComplexPlane₂ =>
      x.2.1 j * ((PeriodTorusTypeOneOne.periodEquiv (P.point x.1)).symm x.2.2) j) := by
  have hv : Continuous (fun x : B × (Fin 4 → ℝ) × ComplexPlane₂ => x.2.1 j) :=
    (continuous_apply j).comp continuous_snd.fst
  have hz : Continuous (fun x : B × (Fin 4 → ℝ) × ComplexPlane₂ =>
      ((PeriodTorusTypeOneOne.periodEquiv (P.point x.1)).symm x.2.2) j) :=
    (continuous_inversePeriodCoordinate P j).comp
      (f := fun x : B × (Fin 4 → ℝ) × ComplexPlane₂ => (x.1, x.2.2))
      (continuous_fst.prodMk continuous_snd.snd)
  exact hv.mul hz

/-- The finite sum appearing in the original frequency functional is continuous. -/
theorem continuous_frequencySum :
    Continuous (fun x : B × (Fin 4 → ℝ) × ComplexPlane₂ =>
      ∑ j : Fin 4, x.2.1 j *
        ((PeriodTorusTypeOneOne.periodEquiv (P.point x.1)).symm x.2.2) j) :=
  continuous_finsetSum _ (fun j _ => continuous_frequencyTerm P j)

/-- Joint continuity in the base, real frequency and covering-space vector. -/
theorem continuous_frequencyFunctional :
    Continuous (fun x : B × (Fin 4 → ℝ) × ComplexPlane₂ =>
      frequencyFunctional (P.point x.1) x.2.1 x.2.2) :=
  (continuous_frequencySum P).congr
    (fun x => (frequencyFunctional_apply (P.point x.1) x.2.1 x.2.2).symm)

/-- Joint continuity of the actual Dolbeault Fourier symbol. -/
theorem continuous_symbol :
    Continuous (fun x : B × (Fin 4 → ℝ) => dolbeaultSymbol (P.point x.1) x.2) := by
  apply continuous_pi
  intro i
  simp only [dolbeaultSymbol_apply]
  have h (z : ComplexPlane₂) :
      Continuous (fun x : B × (Fin 4 → ℝ) => frequencyFunctional (P.point x.1) x.2 z) :=
    (continuous_frequencyFunctional P).comp
      (f := fun x : B × (Fin 4 → ℝ) => (x.1, x.2, z))
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  exact continuous_const.mul
    ((continuous_const.mul (Complex.continuous_ofReal.comp (h _))).sub
      (Complex.continuous_ofReal.comp (h _)))

/-- The genuine symbol, bundled with its automatically continuous real-linear map. -/
def symbolOperator (p : PeriodDomain) : (Fin 4 → ℝ) →L[ℝ] ComplexPlane₂ :=
  (dolbeaultSymbol p).toContinuousLinearMap

@[simp] theorem symbolOperator_apply (p : PeriodDomain) (v : Fin 4 → ℝ) :
    symbolOperator p v = dolbeaultSymbol p v := rfl

/-- Continuity holds in operator norm, not just separately at each frequency. -/
theorem continuous_symbolOperator :
    Continuous (fun b => symbolOperator (P.point b)) := by
  apply continuous_clm_apply.mpr
  intro v
  simp only [symbolOperator_apply]
  exact (continuous_symbol P).comp (f := fun b : B => (b, v))
    (continuous_id.prodMk continuous_const)

/-- In particular every fixed genuine integer Fourier symbol varies continuously. -/
theorem continuous_integerSymbol (k : Fin 4 → ℤ) :
    Continuous (fun b => dolbeaultSymbol (P.point b) (integerFrequency k)) :=
  (continuous_symbol P).comp (f := fun b : B => (b, integerFrequency k))
    (continuous_id.prodMk continuous_const)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier
