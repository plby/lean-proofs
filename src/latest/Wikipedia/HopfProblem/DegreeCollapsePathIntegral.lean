import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The bounded primitive operator on the fixed path interval

Paths use the fixed interval `[-2,2]`, so evaluation at `1` is an interior
time. Constant extension through the interval projection defines their
ordinary integrals. The primitive is a bounded linear operator in the
sup norm, and its ordinary derivative is the original extended path.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

abbrev PathTime := Icc (-2 : ℝ) 2

def pathClamp : ℝ → PathTime := projIcc (-2) 2 (by norm_num)

theorem continuous_pathClamp : Continuous pathClamp := continuous_projIcc

theorem pathClamp_coe (t : PathTime) : pathClamp (t : ℝ) = t := projIcc_val _ t

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def pathExtend (u : C(PathTime, E)) : ℝ → E := u ∘ pathClamp

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_pathExtend (u : C(PathTime, E)) : Continuous (pathExtend u) :=
  u.continuous.comp continuous_pathClamp

def pathPrimitive (u : C(PathTime, E)) : C(PathTime, E) :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s,
    (intervalIntegral.differentiable_integral_of_continuous
      (continuous_pathExtend u)).continuous.comp continuous_subtype_val⟩

theorem norm_pathPrimitive_le (u : C(PathTime, E)) : ‖pathPrimitive u‖ ≤ 2 * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg u))).mpr
  intro t
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (f := pathExtend u)
    (fun s _ => u.norm_coe_le_norm (pathClamp s))
  have ht : |(t : ℝ)| ≤ 2 := abs_le.mpr t.property
  simp only [sub_zero] at hh
  change ‖∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s‖ ≤ 2 * ‖u‖
  simpa only [sub_zero, mul_comm] using
    hh.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg u))

/-- Integrating from zero is bounded and linear on the actual path space. -/
def pathPrimitiveCLM : C(PathTime, E) →L[ℝ] C(PathTime, E) :=
  LinearMap.mkContinuous
    { toFun := pathPrimitive
      map_add' := by
        intro u v
        ext t
        change (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s + pathExtend v s) =
          (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s) +
          (∫ s in (0 : ℝ)..(t : ℝ), pathExtend v s)
        exact intervalIntegral.integral_add
          ((continuous_pathExtend u).intervalIntegrable _ _)
          ((continuous_pathExtend v).intervalIntegrable _ _)
      map_smul' := by
        intro r u
        ext t
        change (∫ s in (0 : ℝ)..(t : ℝ), r • pathExtend u s) =
          r • (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s)
        exact intervalIntegral.integral_smul r (pathExtend u) }
    2 (fun u => norm_pathPrimitive_le u)

theorem pathPrimitiveCLM_apply (u : C(PathTime, E)) : pathPrimitiveCLM u = pathPrimitive u := rfl

theorem pathPrimitive_zero (u : C(PathTime, E)) : pathPrimitive u ⟨0, by norm_num⟩ = 0 := by
  exact intervalIntegral.integral_same

theorem hasDerivAt_pathPrimitive (u : C(PathTime, E)) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, pathExtend u s) (pathExtend u t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_pathExtend u).intervalIntegrable _ _)
    (continuous_pathExtend u).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_pathExtend u).continuousAt

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
