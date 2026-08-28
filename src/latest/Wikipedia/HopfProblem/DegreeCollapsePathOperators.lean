import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pointwise continuous linear operators on compact path spaces

The derivative of nonlinear postcomposition acts pointwise. This file
constructs that bounded operator and its continuous linear dependence on
the coefficient path, including the uniform norm bound needed for the
Picard fixed-point equation.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Apply a continuous path of operators to a continuous path pointwise. -/
def pathOperator (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
      map_add' := by intro u v; ext t; exact map_add (A t) (u t) (v t)
      map_smul' := by intro r u; ext t; exact map_smul (A t) r (u t) }
    ‖A‖ (by
      intro u
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact ((A t).le_opNorm (u t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _)))

theorem pathOperator_apply (A : C(K, E →L[ℝ] F)) (u : C(K, E)) (t : K) :
    pathOperator A u t = A t (u t) := rfl

theorem norm_pathOperator_le (A : C(K, E →L[ℝ] F)) : ‖pathOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

/-- The operator itself depends continuously and linearly on its coefficient path. -/
def pathOperatorCLM : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := pathOperator
      map_add' := by intro A B; ext u t; rfl
      map_smul' := by intro r A; ext u t; rfl }
    1 (by
      intro A
      change ‖pathOperator A‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact norm_pathOperator_le A)

theorem pathOperatorCLM_apply (A : C(K, E →L[ℝ] F)) : pathOperatorCLM A = pathOperator A := rfl

theorem contDiff_pathOperator : ContDiff ℝ ∞ (pathOperator (K := K) (E := E) (F := F)) :=
  (pathOperatorCLM (K := K) (E := E) (F := F)).contDiff

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
