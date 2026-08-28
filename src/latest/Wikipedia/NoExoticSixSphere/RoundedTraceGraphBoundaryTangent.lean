import Wikipedia.NoExoticSixSphere.RoundedTraceGraphBoundaryColumns

/-!
# The graph boundary tangent image and its fixed normal two-plane

The actual graph boundary differential has zero time component and the old
boundary ambient differential as its remaining component. Consequently the
entire slope-rotation family lies in its actual normal space.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_timeGraphBoundary : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) 𝓘(ℝ, TimeGraphSpace (e := e)) ∞
      (fun p : Boundary A ↦ timeGraph A p.val) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact (contMDiff_timeGraph A).comp (contMDiff_boundaryInclusion A)

def timeGraphBoundaryDifferential (p : Boundary A) : Vector 6 →L[ℝ] TimeGraphSpace (e := e) :=
  letI := boundaryChartedSpace A
  mvfderiv (𝓡 6) (fun q : Boundary A ↦ timeGraph A q.val) p

theorem timeGraphBoundaryDifferential_eq (p : Boundary A) :
    timeGraphBoundaryDifferential A p =
      (timeGraphDifferential A p.val).comp (boundaryTraceDifferential A p) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  exact mfderiv_comp p ((contMDiff_timeGraph A).mdifferentiableAt (by simp))
    ((contMDiff_boundaryInclusion A).mdifferentiableAt (by simp))

theorem injective_timeGraphBoundaryDifferential (p : Boundary A) :
    Injective (timeGraphBoundaryDifferential A p) := by
  rw [timeGraphBoundaryDifferential_eq]
  exact (injective_timeGraphDifferential A p.val).comp (injective_boundaryTraceDifferential A p)

theorem timeGraphBoundaryDifferential_apply (p : Boundary A) (v : Vector 6) :
    timeGraphBoundaryDifferential A p v =
      WithLp.toLp 2 ((0 : ℝ), boundaryAmbientDerivative A p v) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  have hz : bordismTimeDifferential A p.val (boundaryTraceDifferential A p v) = 0 := by
    change boundaryTraceDifferential A p v ∈ (bordismTimeDifferential A p.val).ker
    rw [← range_boundaryTraceDifferential_time]
    exact ⟨v, rfl⟩
  have hd := congrArg (fun D : Vector 6 →L[ℝ] Vector (e.ambientDimension + 6) ↦ D v)
    (boundaryAmbientDerivative_eq A p)
  change boundaryAmbientDerivative A p v =
    traceAmbientDerivative A p.val (boundaryTraceDifferential A p v) at hd
  rw [timeGraphBoundaryDifferential_eq]
  change timeGraphDifferential A p.val (boundaryTraceDifferential A p v) = _
  rw [timeGraphDifferential_apply, hz, ← hd]

theorem timeGraphLiftedFrame_mem_boundary (p : Boundary A)
    (v : Vector ((e.ambientDimension - 6) + 5)) :
    timeGraphLiftedFrame A p.val v ∈ (timeGraphBoundaryDifferential A p).rangeᗮ := by
  apply Submodule.orthogonal_le (show (timeGraphBoundaryDifferential A p).range ≤
      (timeGraphDifferential A p.val).range from ?_)
    (timeGraphLiftedFrame_mem A p.val v)
  rw [timeGraphBoundaryDifferential_eq]
  rintro _ ⟨w, rfl⟩
  exact ⟨boundaryTraceDifferential A p w, rfl⟩

theorem timeGraph_planeNormal_mem_boundary (p : Boundary A) (s : ℝ) :
    NormalGraphPlane.normalColumn (outwardNormal A p) s ∈
      (timeGraphBoundaryDifferential A p).rangeᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (timeGraphBoundaryDifferential A p v)
    (NormalGraphPlane.normalColumn (outwardNormal A p) s) = 0
  rw [timeGraphBoundaryDifferential_apply, real_inner_comm]
  apply NormalGraphPlane.normalColumn_orthogonal_lift
  exact (real_inner_comm _ _).trans
    ((boundaryAmbientDerivative A p).range.inner_right_of_mem_orthogonal ⟨v, rfl⟩
      (outwardNormal_mem_boundaryNormal A p))

theorem timeGraph_planeOutward_mem_boundary (p : Boundary A) (s : ℝ) :
    NormalGraphPlane.outwardColumn (outwardNormal A p) s ∈
      (timeGraphBoundaryDifferential A p).rangeᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (timeGraphBoundaryDifferential A p v)
    (NormalGraphPlane.outwardColumn (outwardNormal A p) s) = 0
  rw [timeGraphBoundaryDifferential_apply, real_inner_comm]
  apply NormalGraphPlane.outwardColumn_orthogonal_lift
  exact (real_inner_comm _ _).trans
    ((boundaryAmbientDerivative A p).range.inner_right_of_mem_orthogonal ⟨v, rfl⟩
      (outwardNormal_mem_boundaryNormal A p))

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
