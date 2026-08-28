import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Elementary bounds for the actual torus Fourier coefficients

All coefficients in this file are Mathlib's `UnitAddTorus.mFourierCoeff`,
with the probability Haar normalization on each unit circle.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

local instance fourierBasicMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fourierBasicIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fourierBasicIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

theorem torusMonomial_norm (k : d → ℤ) (x : UnitAddTorus d) :
    ‖mFourier k x‖ = 1 := by
  simp [mFourier, norm_prod, fourier_apply, Circle.norm_coe]

theorem torusFourierIntegrable (f : C(UnitAddTorus d, ℂ)) (k : d → ℤ) :
    Integrable (fun x => mFourier (-k) x * f x) := by
  have h : Integrable (⇑(mFourier (-k)) * ⇑f) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (((mFourier (-k)).continuous.mul f.continuous).continuousOn.integrableOn_compact
        (μ := volume) isCompact_univ)
  exact h.congr (Filter.Eventually.of_forall fun _ => rfl)

theorem torusFourierCoeff_add (f g : C(UnitAddTorus d, ℂ)) (k : d → ℤ) :
    mFourierCoeff (f + g) k = mFourierCoeff f k + mFourierCoeff g k := by
  simp only [mFourierCoeff, ContinuousMap.add_apply, smul_eq_mul, mul_add]
  exact integral_add (torusFourierIntegrable f k) (torusFourierIntegrable g k)

theorem torusFourierCoeff_sub (f g : C(UnitAddTorus d, ℂ)) (k : d → ℤ) :
    mFourierCoeff (f - g) k = mFourierCoeff f k - mFourierCoeff g k := by
  simp only [mFourierCoeff, ContinuousMap.sub_apply, smul_eq_mul, mul_sub]
  exact integral_sub (torusFourierIntegrable f k) (torusFourierIntegrable g k)

theorem torusFourierCoeff_const_mul (f : UnitAddTorus d → ℂ) (c : ℂ) (k : d → ℤ) :
    mFourierCoeff (fun x => c * f x) k = c * mFourierCoeff f k := by
  simp only [mFourierCoeff, smul_eq_mul]
  simp_rw [mul_left_comm _ c (f _)]
  rw [integral_const_mul]

theorem torusFourierCoeff_smul (f : C(UnitAddTorus d, ℂ)) (c : ℂ) (k : d → ℤ) :
    mFourierCoeff (c • f) k = c • mFourierCoeff f k :=
  torusFourierCoeff_const_mul f c k

theorem torusFourierCoeff_norm_le (f : C(UnitAddTorus d, ℂ)) (k : d → ℤ) :
    ‖mFourierCoeff f k‖ ≤ ‖f‖ := by
  have hbound : ∀ᵐ x : UnitAddTorus d, ‖mFourier (-k) x • f x‖ ≤ ‖f‖ :=
    Filter.Eventually.of_forall fun x => by
      rw [norm_smul, torusMonomial_norm, one_mul]
      exact f.norm_coe_le_norm x
  simpa only [mFourierCoeff, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hbound

/-- The actual Fourier coefficient is a bounded complex-linear functional. -/
def torusFourierCoeffLinear (k : d → ℤ) : C(UnitAddTorus d, ℂ) →ₗ[ℂ] ℂ where
  toFun f := mFourierCoeff f k
  map_add' := fun f g => torusFourierCoeff_add f g k
  map_smul' := fun c f => torusFourierCoeff_smul f c k

@[simp]
theorem torusFourierCoeffLinear_apply (k : d → ℤ) (f : C(UnitAddTorus d, ℂ)) :
    torusFourierCoeffLinear k f = mFourierCoeff f k := rfl

def torusFourierCoeffCLM (k : d → ℤ) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  (torusFourierCoeffLinear k).mkContinuous 1 (by
    intro f
    simpa only [torusFourierCoeffLinear_apply, one_mul] using torusFourierCoeff_norm_le f k)

@[simp]
theorem torusFourierCoeffCLM_apply (k : d → ℤ) (f : C(UnitAddTorus d, ℂ)) :
    torusFourierCoeffCLM k f = mFourierCoeff f k := rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
