import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearSymbol

/-!
# Holomorphic dependence of the actual relative Fourier symbol

The symbol is expressed in the already verified marked period-coordinate
frame. Its coefficients involve the original holomorphic period functions,
without conjugating them. Continuity is joint in the base and real frequency
and also holds in operator norm.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

open Complex MarkedLinear PeriodTorusLineBundleClassification

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- Joint continuity of the symbol in the original holomorphic marked frame. -/
theorem continuous_symbol :
    Continuous (fun x : B × (Fin 4 → ℝ) => relativeSymbol (P.point x.1) x.2) := by
  have ht : Continuous (fun x : B × (Fin 4 → ℝ) => (P.point x.1).val.τ) :=
    P.holomorphic_tau.continuous.comp continuous_fst
  have hm : Continuous (fun x : B × (Fin 4 → ℝ) => (P.point x.1).val.μ) :=
    P.holomorphic_mu.continuous.comp continuous_fst
  have hb : Continuous (fun x : B × (Fin 4 → ℝ) => (P.point x.1).val.β) :=
    P.holomorphic_beta.continuous.comp continuous_fst
  have hv (j : Fin 4) : Continuous (fun x : B × (Fin 4 → ℝ) => (x.2 j : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_snd)
  apply continuous_pi
  intro j
  fin_cases j
  · change Continuous (fun x : B × (Fin 4 → ℝ) => (2 * (Real.pi : ℂ) * I) *
      ((x.2 0 : ℂ) - (6 * (P.point x.1).val.μ * (x.2 2 : ℂ) +
        (P.point x.1).val.β * (x.2 3 : ℂ))))
    exact continuous_const.mul ((hv 0).sub
      (((continuous_const.mul hm).mul (hv 2)).add (hb.mul (hv 3))))
  · change Continuous (fun x : B × (Fin 4 → ℝ) => (2 * (Real.pi : ℂ) * I) *
      ((x.2 1 : ℂ) - ((P.point x.1).val.τ * (x.2 2 : ℂ) +
        (P.point x.1).val.μ * (x.2 3 : ℂ))))
    exact continuous_const.mul ((hv 1).sub ((ht.mul (hv 2)).add (hm.mul (hv 3))))

/-- Every fixed real frequency has genuinely holomorphic symbol coefficients. -/
theorem holomorphic_symbol_coordinate (v : Fin 4 → ℝ) (j : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b => relativeSymbol (P.point b) v j) := by
  fin_cases j
  · change ContMDiff _ _ ω (fun b => (2 * (Real.pi : ℂ) * I) *
      ((v 0 : ℂ) - (6 * (P.point b).val.μ * (v 2 : ℂ) +
        (P.point b).val.β * (v 3 : ℂ))))
    exact contMDiff_const.mul (contMDiff_const.sub
      (((contMDiff_const.mul P.holomorphic_mu).mul contMDiff_const).add
        (P.holomorphic_beta.mul contMDiff_const)))
  · change ContMDiff _ _ ω (fun b => (2 * (Real.pi : ℂ) * I) *
      ((v 1 : ℂ) - ((P.point b).val.τ * (v 2 : ℂ) +
        (P.point b).val.μ * (v 3 : ℂ))))
    exact contMDiff_const.mul (contMDiff_const.sub
      ((P.holomorphic_tau.mul contMDiff_const).add
        (P.holomorphic_mu.mul contMDiff_const)))

/-- The entire two-component symbol is holomorphic at each fixed frequency. -/
theorem holomorphic_symbol (v : Fin 4 → ℝ) :
    ContMDiff (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ (Fin 2 → ℂ)) ω
      (fun b => relativeSymbol (P.point b) v) :=
  contMDiff_pi_space.mpr (holomorphic_symbol_coordinate P v)

/-- The original real-linear relative symbol with its automatic continuity. -/
def symbolOperator (p : PeriodDomain) : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℂ) :=
  (relativeSymbol p).toContinuousLinearMap

@[simp] theorem symbolOperator_apply (p : PeriodDomain) (v : Fin 4 → ℝ) :
    symbolOperator p v = relativeSymbol p v := rfl

/-- Finite dimensionality gives genuine operator-norm continuity. -/
theorem continuous_symbolOperator :
    Continuous (fun b => symbolOperator (P.point b)) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (continuous_symbol P).comp (f := fun b : B => (b, v))
    (continuous_id.prodMk continuous_const)

/-- The same holomorphic coefficient statement uses the actual integer modes. -/
theorem holomorphic_integerSymbol_coordinate (k : Fin 4 → ℤ) (j : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b => relativeSymbol (P.point b) (integerFrequency k) j) :=
  holomorphic_symbol_coordinate P (integerFrequency k) j

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier
