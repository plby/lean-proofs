import Wikipedia.HopfProblem.DegreeCollapseSmoothFixedPoint
import Wikipedia.HopfProblem.DegreeCollapseSmoothPathPostcomposition
import Wikipedia.HopfProblem.DegreeCollapsePathIntegral

/-!
# Smooth path solutions of the time-scaled Picard equation

Elapsed time is a parameter and the path domain stays fixed. At elapsed
time zero the Picard map is constant in the unknown path, so its partial
derivative there vanishes. The Banach implicit-function theorem constructs
one smooth family on an open parameter neighborhood. Evaluation at a fixed
interior path time will give smooth dependence of the local ODE solution.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def picardPathMap (v : C(E, E)) (q : (E × ℝ) × C(PathTime, E)) : C(PathTime, E) :=
  ContinuousMap.const PathTime q.1.1 + q.1.2 • pathPrimitiveCLM (v.comp q.2)

theorem contDiff_picardPathMap (v : C(E, E)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (picardPathMap v) := by
  exact ((ContinuousLinearMap.const ℝ PathTime : E →L[ℝ] C(PathTime, E)).contDiff.comp
    contDiff_fst.fst).add (contDiff_fst.snd.smul
      ((pathPrimitiveCLM (E := E)).contDiff.comp
        ((contDiff_pathPostcomposition v hv).comp contDiff_snd)))

theorem picardPathMap_zero (v : C(E, E)) (x : E) (u : C(PathTime, E)) :
    picardPathMap v ((x, 0), u) = ContinuousMap.const PathTime x := by
  simp only [picardPathMap, zero_smul, add_zero]

theorem picardPathMap_partial_zero (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E)
    (u : C(PathTime, E)) :
    (fderiv ℝ (picardPathMap v) ((x, 0), u)).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E)) = 0 := by
  have hQ := contDiff_picardPathMap v hv
  have hd := (hQ.differentiable (by simp) ((x, 0), u)).hasFDerivAt.comp u
    ((hasFDerivAt_const (x, (0 : ℝ)) u).prodMk (hasFDerivAt_id u))
  change HasFDerivAt (fun w => picardPathMap v ((x, 0), w))
    ((fderiv ℝ (picardPathMap v) ((x, 0), u)).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E))) u at hd
  have he : (fun w => picardPathMap v ((x, 0), w)) =
      fun _ => ContinuousMap.const PathTime x := funext (picardPathMap_zero v x)
  rw [he] at hd
  exact hd.unique (hasFDerivAt_const (ContinuousMap.const PathTime x) u)

/-- Construct a smooth family solving the actual scaled Picard integral equation. -/
theorem exists_smooth_picard_paths (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ∃ (U : Set (E × ℝ)) (u : E × ℝ → C(PathTime, E)),
      IsOpen U ∧ (x, 0) ∈ U ∧ u (x, 0) = ContinuousMap.const PathTime x ∧
      ContDiffOn ℝ ∞ u U ∧ ∀ q ∈ U, ∀ t : PathTime,
        u q t = q.1 + q.2 • (∫ s in (0 : ℝ)..(t : ℝ), v (u q (pathClamp s))) := by
  have hsmall : ‖(fderiv ℝ (picardPathMap v) ((x, 0), ContinuousMap.const PathTime x)).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E))‖ < 1 := by
    rw [picardPathMap_partial_zero v hv x, norm_zero]
    exact zero_lt_one
  obtain ⟨U, u, hU, hx, hu, hcont, hfix⟩ := exists_smooth_fixedPoint_neighborhood
    (contDiff_picardPathMap v hv) (picardPathMap_zero v x (ContinuousMap.const PathTime x)) hsmall
  refine ⟨U, u, hU, hx, hu, hcont, ?_⟩
  intro q hq t
  have hh := congrArg (fun w : C(PathTime, E) => w t) (hfix q hq)
  exact hh.symm

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
