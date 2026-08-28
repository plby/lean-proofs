import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalFrame
import Wikipedia.NoExoticSixSphere.RoundedTraceGraphBoundaryColumns

/-!
# The exact tangential correction on the native graph boundary

At a boundary point of outward time slope `s`, the cutoff correction is
`s⁻¹ (s, ν)`. The calculation uses the proved normal projection and the
nonzero actual slope; no interior regularity of the time function is assumed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem graphTimeTangent_boundary (p : Boundary A) :
    graphTimeTangent A p.val =
      (boundaryTimeSlope A p * (1 / (1 + boundaryTimeSlope A p ^ 2))) •
        NormalGraphPlane.outwardRaw (outwardNormal A p) (boundaryTimeSlope A p) := by
  rw [graphTimeTangent, timeGraph_projectedTime_boundary]
  have he : timeGraphTimeUnit (e := e) =
      (1 / (1 + boundaryTimeSlope A p ^ 2)) •
        NormalGraphPlane.normalRaw (outwardNormal A p) (boundaryTimeSlope A p) +
      (boundaryTimeSlope A p * (1 / (1 + boundaryTimeSlope A p ^ 2))) •
        NormalGraphPlane.outwardRaw (outwardNormal A p) (boundaryTimeSlope A p) :=
    NormalGraphPlane.time_axis_decomposition _ _
  rw [he]
  abel

theorem graphTimeSpeed_boundary (p : Boundary A) :
    graphTimeSpeed A p.val = boundaryTimeSlope A p ^ 2 / (1 + boundaryTimeSlope A p ^ 2) := by
  rw [graphTimeSpeed, graphTimeTangent_boundary, map_smul]
  change (boundaryTimeSlope A p * (1 / (1 + boundaryTimeSlope A p ^ 2))) *
    boundaryTimeSlope A p = _
  ring

theorem cutoffTimeTangent_boundary (p : Boundary A) :
    cutoffTimeTangent A p.val = (boundaryTimeSlope A p)⁻¹ •
      NormalGraphPlane.outwardRaw (outwardNormal A p) (boundaryTimeSlope A p) := by
  let := traceChartedSpace A
  rw [cutoffTimeTangent, verticalFrameCutoff_one_boundary, graphTimeSpeed_boundary,
    graphTimeTangent_boundary, smul_smul]
  apply congrArg (fun c : ℝ ↦ c •
    NormalGraphPlane.outwardRaw (outwardNormal A p) (boundaryTimeSlope A p))
  have hs := boundaryTimeSlope_ne_zero A p
  have hd : 1 + boundaryTimeSlope A p ^ 2 ≠ 0 := by positivity
  field_simp

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
