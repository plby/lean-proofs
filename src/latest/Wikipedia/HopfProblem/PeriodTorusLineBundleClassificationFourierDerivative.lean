import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeIntegral
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeMonomial

/-!
# Fourier coefficients of actual smooth torus derivatives

Translation invariance of the Haar integral and the proved dominated
differentiation theorem give the directional multiplier `2πi ⟨k,v⟩`.
No coefficient identity, decay estimate, or integration-by-parts conclusion
is included among the hypotheses.
-/

noncomputable section

open MeasureTheory UnitAddTorus
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- Actual real directional differentiation has the expected Fourier
multiplier, for every direction and every integer frequency, including zero. -/
theorem mFourierCoeff_torusDirectionalDerivative (f : SmoothTorusFunction d)
    (v : d → ℝ) (k : d → ℤ) :
    mFourierCoeff (torusDirectionalDerivative f v) k =
      (2 * (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) * (v j : ℂ)) *
        mFourierCoeff f k := by
  let A : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) * (v j : ℂ)
  have hfirst : HasDerivAt
      (fun r : ℝ => mFourierCoeff (fun t => f (t + torusQuotient (r • v))) k)
      (mFourierCoeff (torusDirectionalDerivative f v) k) 0 := by
    simpa only [mFourierCoeff, smul_eq_mul, zero_smul, torusQuotient_zero, add_zero]
      using hasDerivAt_integral_torus_translate f (mFourier (-k)) v 0
  have hsecond : HasDerivAt
      (fun r : ℝ => mFourierCoeff (fun t => f (t + torusQuotient (r • v))) k)
      (A * mFourierCoeff f k) 0 := by
    change HasDerivAt
      (fun r : ℝ => mFourierCoeff
        (fun t => f.toContinuousMap (t + torusQuotient (r • v))) k)
      (A * mFourierCoeff f k) 0
    simp_rw [mFourierCoeff_translate]
    change HasDerivAt
      (fun r : ℝ => mFourier k (fun i => (r * v i : UnitAddCircle)) * mFourierCoeff f k)
      (A * mFourierCoeff f k) 0
    simpa only [A, zero_mul,
      AddCircle.coe_zero, ← Pi.zero_def, mFourier_zero_argument, mul_one] using
      (hasDerivAt_mFourier_line k v 0).mul_const (mFourierCoeff f k)
  exact hfirst.unique hsecond

/-- Coordinate differentiation is the special case of the actual unit
coordinate direction in the real covering space. -/
theorem mFourierCoeff_torusCoordinateDerivative [DecidableEq d]
    (f : SmoothTorusFunction d) (j : d) (k : d → ℤ) :
    mFourierCoeff (torusDirectionalDerivative f (Pi.single j 1)) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * mFourierCoeff f k := by
  rw [mFourierCoeff_torusDirectionalDerivative]
  congr 2
  simp [Pi.single_apply, apply_ite]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
