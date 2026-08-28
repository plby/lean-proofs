import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Pointwise derivative fields as bounded operators on compact continuous-function spaces

A continuous field of linear maps acts on a whole continuous function by
pointwise evaluation. Its operator norm is bounded by the uniform norm of
the field, and the passage from fields to operators is itself bounded linear.
This is the derivative operator for the local-flow integral equation.
-/

noncomputable section

open ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {X E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def applyFieldLinear (L : C(X, E →L[ℝ] F)) : C(X, E) →ₗ[ℝ] C(X, F) where
  toFun a := ⟨fun x => L x (a x), L.continuous.clm_apply a.continuous⟩
  map_add' a b := ContinuousMap.ext (fun x => (L x).map_add (a x) (b x))
  map_smul' c a := ContinuousMap.ext (fun x => (L x).map_smul c (a x))

theorem applyFieldLinear_norm_le (L : C(X, E →L[ℝ] F)) (a : C(X, E)) :
    ‖applyFieldLinear L a‖ ≤ ‖L‖ * ‖a‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  exact ((L x).le_opNorm (a x)).trans
    (mul_le_mul (L.norm_coe_le_norm x) (a.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _))

def applyField (L : C(X, E →L[ℝ] F)) : C(X, E) →L[ℝ] C(X, F) :=
  (applyFieldLinear L).mkContinuous ‖L‖ (applyFieldLinear_norm_le L)

theorem applyField_apply (L : C(X, E →L[ℝ] F)) (a : C(X, E)) (x : X) :
    applyField L a x = L x (a x) := rfl

theorem applyField_norm_le (L : C(X, E →L[ℝ] F)) : ‖applyField L‖ ≤ ‖L‖ :=
  (applyFieldLinear L).mkContinuous_norm_le (norm_nonneg L) (applyFieldLinear_norm_le L)

def liftField : C(X, E →L[ℝ] F) →L[ℝ] (C(X, E) →L[ℝ] C(X, F)) :=
  LinearMap.mkContinuous {
    toFun := applyField
    map_add' L Q := ContinuousLinearMap.ext (fun a => ContinuousMap.ext (fun x => rfl))
    map_smul' c L := ContinuousLinearMap.ext (fun a => ContinuousMap.ext (fun x => rfl)) }
    1 (fun L => by
      change ‖applyField L‖ ≤ 1 * ‖L‖
      simpa only [one_mul] using applyField_norm_le L)

theorem liftField_apply (L : C(X, E →L[ℝ] F)) (a : C(X, E)) (x : X) :
    liftField L a x = L x (a x) := rfl

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
