import Wikipedia.NoExoticSixSphere.CanonicalRightInverse
import Wikipedia.NoExoticSixSphere.CollapseRegularFiber

/-!
# The induced collapse frame agrees with the given normal frame

The canonical orthogonal right inverse of the actual collapse differential
is exactly the given ambient normal frame multiplied by the positive tube
radius. Thus the differential construction retains the specified framing,
up to this explicit positive scaling, rather than merely supplying some
unrelated normal basis.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

theorem orthogonalRightInverse_coordinates (x : M) :
    orthogonalRightInverse (fderiv ℝ d.coordinates (e.toFun x)) = d.radius • a.ambient x := by
  apply orthogonalRightInverse_eq_of_rightInverse _
    (d.surjective_differential _ (d.range_subset ⟨x, rfl⟩))
  · exact d.differential_frame x
  · rw [d.kernel_eq_tangentImage]
    rintro _ ⟨v, rfl⟩
    change d.radius • a.ambient x v ∈ e.normalFiber x
    apply Submodule.smul_mem
    have hv : a.ambient x v ∈ (e.normalProjection x).range := (a.equiv x v).property
    rwa [e.range_normalProjection] at hv

theorem orthogonalRightInverse_coordinates_apply (x : M) (v : e.NormalModel) :
    orthogonalRightInverse (fderiv ℝ d.coordinates (e.toFun x)) v =
      d.radius • a.ambient x v := by
  rw [d.orthogonalRightInverse_coordinates]
  rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
