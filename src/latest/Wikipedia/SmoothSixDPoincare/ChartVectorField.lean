import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Vector fields and integral curves in genuine manifold charts

The coordinate field is the tangent-coordinate change applied to the native
vector field. Inverse-chart differentiation cancels that coordinate change,
so a Euclidean solution lifts to a solution of the original manifold field.
-/

noncomputable section

open Set Manifold Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

def coordinateField (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) (y : E) : E :=
  tangentCoordChange 𝓘(ℝ, E) ((chartAt E p).symm y) p ((chartAt E p).symm y)
    (v ((chartAt E p).symm y))

/-- Native smoothness of a vector field gives ordinary smoothness in its base chart. -/
theorem contDiffAt_coordinateField {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}
    (hv : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) p) :
    ContDiffAt ℝ 1 (coordinateField v p) (chartAt E p p) := by
  rw [contMDiffAt_iff] at hv
  have h := hv.2.contDiffAt
    (range_mem_nhds_isInteriorPoint (I := 𝓘(ℝ, E))
      (BoundarylessManifold.isInteriorPoint (x := p)))
  convert h.snd using 1 <;> rfl

/-- The coordinate field is the native differential of the chart applied to the original field. -/
theorem coordinateField_eq_mfderiv (v : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    coordinateField v p y =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p) ((chartAt E p).symm y)
        (v ((chartAt E p).symm y)) := by
  rw [mfderiv_chartAt_eq_tangentCoordChange ((chartAt E p).map_target hy)]
  rfl

/-- Applying the differential of the inverse chart recovers the original vector field. -/
theorem mfderiv_symm_coordinateField (v : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
      ((NormedSpace.fromTangentSpace y).symm (coordinateField v p y)) =
      v ((chartAt E p).symm y) := by
  let e := chartAt E p
  have he := (mdifferentiable_chart (I := 𝓘(ℝ, E)) p).symm_comp_deriv (e.map_target hy)
  rw [e.right_inv hy] at he
  rw [coordinateField_eq_mfderiv v p hy]
  exact congrArg (fun A : E →L[ℝ] E => A (v (e.symm y))) he

/-- A solution of the coordinate ODE staying in the chart target solves the native manifold ODE. -/
theorem hasMFDerivAt_lift_coordinateCurve
    {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M} {α : ℝ → E} {t : ℝ}
    (hα : HasDerivAt α (coordinateField v p (α t)) t)
    (ht : α t ∈ (chartAt E p).target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((chartAt E p).symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((chartAt E p).symm (α t)))) := by
  have hi := ((mdifferentiable_chart (I := 𝓘(ℝ, E)) p).mdifferentiableAt_symm ht).hasMFDerivAt
  have h := hi.comp t hα.hasFDerivAt.hasMFDerivAt
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm (α t))
    ((NormedSpace.fromTangentSpace t a) •
      (NormedSpace.fromTangentSpace (α t)).symm (coordinateField v p (α t))) =
      (NormedSpace.fromTangentSpace t a) • v ((chartAt E p).symm (α t))
  rw [map_smul, mfderiv_symm_coordinateField v p ht]

end Wikipedia.SmoothSixDPoincare.FlowConstruction
