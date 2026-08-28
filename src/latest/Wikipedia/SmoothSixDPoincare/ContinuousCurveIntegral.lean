import Wikipedia.SmoothSixDPoincare.CompactFunctionDerivative
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration as a bounded linear operator on continuous curves

The curve space has the fixed parameter interval `[0,1]`. Extending a curve
by the interval projection defines its primitive on the whole real line.
The restricted primitive has operator norm at most one and the original
curve as its derivative on the interval.
-/

noncomputable section

open Set ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def curvePrimitive (a : C(I, E)) (t : ℝ) : E :=
  ∫ s in 0..t, IccExtendCM a s

theorem hasDerivAt_curvePrimitive (a : C(I, E)) (t : ℝ) :
    HasDerivAt (curvePrimitive a) (IccExtendCM a t) t :=
  (IccExtendCM a).continuous.integral_hasStrictDerivAt 0 t |>.hasDerivAt

theorem continuous_curvePrimitive (a : C(I, E)) : Continuous (curvePrimitive a) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_curvePrimitive a t).continuousAt)

def curveIntegralLinear : C(I, E) →ₗ[ℝ] C(I, E) where
  toFun a := ⟨fun t => curvePrimitive a t,
    (continuous_curvePrimitive a).comp continuous_subtype_val⟩
  map_add' a b := by
    ext t
    change (∫ s in 0..(t : ℝ), IccExtendCM (a + b) s) =
      (∫ s in 0..(t : ℝ), IccExtendCM a s) + ∫ s in 0..(t : ℝ), IccExtendCM b s
    exact intervalIntegral.integral_add ((IccExtendCM a).continuous.intervalIntegrable _ _)
      ((IccExtendCM b).continuous.intervalIntegrable _ _)
  map_smul' c a := by
    ext t
    change (∫ s in 0..(t : ℝ), c • IccExtendCM a s) =
      c • ∫ s in 0..(t : ℝ), IccExtendCM a s
    exact intervalIntegral.integral_smul c _

theorem curveIntegralLinear_norm_le (a : C(I, E)) : ‖curveIntegralLinear a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  change ‖∫ s in 0..(t : ℝ), IccExtendCM a s‖ ≤ ‖a‖
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (f := fun s => IccExtendCM a s)
    (C := ‖a‖) (fun s _ => a.norm_coe_le_norm (projIccCM s))
  rw [sub_zero, abs_of_nonneg t.property.1] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) t.property.2)

def curveIntegral : C(I, E) →L[ℝ] C(I, E) :=
  curveIntegralLinear.mkContinuous 1 (fun a => by
    simpa only [one_mul] using curveIntegralLinear_norm_le a)

theorem curveIntegral_apply (a : C(I, E)) (t : I) :
    curveIntegral a t = curvePrimitive a t := rfl

theorem curveIntegral_zero (a : C(I, E)) : curveIntegral a 0 = 0 := by
  change (∫ s in (0 : ℝ)..0, IccExtendCM a s) = 0
  exact intervalIntegral.integral_same

theorem curveIntegral_norm_le (a : C(I, E)) : ‖curveIntegral a‖ ≤ ‖a‖ :=
  curveIntegralLinear_norm_le a

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
