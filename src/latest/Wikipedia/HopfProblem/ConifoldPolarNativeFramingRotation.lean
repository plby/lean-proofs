import Wikipedia.HopfProblem.ConifoldPolarNativeFramingRotationLinear
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingRotationDirection

/-!
# The checked native real-sphere coordinate correction

The explicitly specified linear isometry sends every original image-line
direction to the existing native stereographic sphere point, including
infinity.  In particular the original line direction has Euclidean norm one.
-/

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open CuspCircleNormalTrivialization

@[simp] theorem orthogonalEquiv_lineDirection (p : RiemannSphere) :
    orthogonalEquiv (lineDirection p) = (RealSphere.sphereDiffeomorph p : Base) :=
  orthogonalMap_lineDirection p

@[simp] theorem orthogonalEquiv_symm_sphereDiffeomorph (p : RiemannSphere) :
    orthogonalEquiv.symm (RealSphere.sphereDiffeomorph p : Base) = lineDirection p := by
  rw [← orthogonalEquiv_lineDirection, orthogonalEquiv.symm_apply_apply]

theorem lineDirection_norm (p : RiemannSphere) : ‖lineDirection p‖ = 1 := by
  rw [← orthogonalMap_norm, orthogonalMap_lineDirection]
  simpa only [Metric.mem_sphere, dist_zero_right] using
    (RealSphere.sphereDiffeomorph p).property

theorem lineDirection_mem_sphere (p : RiemannSphere) :
    lineDirection p ∈ Metric.sphere (0 : Base) 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using lineDirection_norm p

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
