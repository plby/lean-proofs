import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryTimeSlope
import Wikipedia.NoExoticSixSphere.NormalGraphPlane

/-!
# Exact normal and outward columns on the graph boundary

The projected time normal is the normalized vector `(1, -s ν)` and the
outward graph tangent is the normalized vector `(s, ν)`, where `s` is the
actual outward time derivative and `ν` the original ambient unit outward normal.
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

theorem timeGraphDifferential_outward (p : Boundary A) :
    timeGraphDifferential A p.val (outwardTraceVector A p) =
      NormalGraphPlane.outwardRaw (outwardNormal A p) (boundaryTimeSlope A p) := by
  rw [timeGraphDifferential_apply, traceDerivative_outwardTraceVector]
  rfl

theorem timeGraph_normalRaw_mem (p : Boundary A) :
    NormalGraphPlane.normalRaw (outwardNormal A p) (boundaryTimeSlope A p) ∈
      (timeGraphDifferential A p.val).rangeᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (timeGraphDifferential A p.val v)
    (NormalGraphPlane.normalRaw (outwardNormal A p) (boundaryTimeSlope A p)) = 0
  rw [timeGraphDifferential_apply]
  simp only [NormalGraphPlane.normalRaw, WithLp.prod_inner_apply, Real.inner_apply,
    mul_one, inner_neg_right, real_inner_smul_right]
  rw [real_inner_comm]
  have he := bordismTimeDifferential_outward_covector A p v
  linarith

theorem timeGraph_projectedTime_boundary (p : Boundary A) :
    timeGraphNormalProjection A p.val (timeGraphTimeUnit (e := e)) =
      (1 / (1 + boundaryTimeSlope A p ^ 2)) •
        NormalGraphPlane.normalRaw (outwardNormal A p) (boundaryTimeSlope A p) := by
  let s := boundaryTimeSlope A p
  let ν := outwardNormal A p
  let c := 1 / (1 + s ^ 2)
  have hdec : timeGraphTimeUnit (e := e) =
      c • NormalGraphPlane.normalRaw ν s + (s * c) • NormalGraphPlane.outwardRaw ν s :=
    NormalGraphPlane.time_axis_decomposition ν s
  have hres : timeGraphTimeUnit (e := e) - c • NormalGraphPlane.normalRaw ν s =
      (s * c) • NormalGraphPlane.outwardRaw ν s := by
    rw [hdec]
    abel
  change (timeGraphDifferential A p.val).rangeᗮ.starProjection (timeGraphTimeUnit (e := e)) =
    c • NormalGraphPlane.normalRaw ν s
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact Submodule.smul_mem _ _ (timeGraph_normalRaw_mem A p)
  · apply (timeGraphDifferential A p.val).range.le_orthogonal_orthogonal
    rw [hres]
    exact Submodule.smul_mem _ _ ⟨outwardTraceVector A p, timeGraphDifferential_outward A p⟩

theorem timeGraphNewNormal_boundary (p : Boundary A) :
    timeGraphNewNormal A p.val =
      NormalGraphPlane.normalColumn (outwardNormal A p) (boundaryTimeSlope A p) := by
  change NormedSpace.normalize (timeGraphNormalProjection A p.val (timeGraphTimeUnit (e := e))) = _
  rw [timeGraph_projectedTime_boundary, NormedSpace.normalize_smul_of_pos (by positivity)]
  rfl

def timeGraphOutwardNormal (p : Boundary A) : TimeGraphSpace (e := e) :=
  NormalGraphPlane.outwardColumn (outwardNormal A p) (boundaryTimeSlope A p)

theorem contMDiff_timeGraphOutwardNormal : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) 𝓘(ℝ, TimeGraphSpace (e := e)) ∞ (timeGraphOutwardNormal A) := by
  let := boundaryChartedSpace A
  exact NormalGraphPlane.contMDiff_outwardColumn (contMDiff_outwardNormal A)
    (contMDiff_boundaryTimeSlope A) (norm_outwardNormal A)

theorem norm_timeGraphOutwardNormal (p : Boundary A) : ‖timeGraphOutwardNormal A p‖ = 1 :=
  NormalGraphPlane.norm_outwardColumn (norm_outwardNormal A p) _

theorem timeGraphOutwardNormal_mem_trace (p : Boundary A) :
    timeGraphOutwardNormal A p ∈ (timeGraphDifferential A p.val).range :=
  Submodule.smul_mem _ _ ⟨outwardTraceVector A p, timeGraphDifferential_outward A p⟩

theorem timeGraphOutwardNormal_lift (p : Boundary A) :
    timeGraphDifferential A p.val
      (‖NormalGraphPlane.outwardRaw (outwardNormal A p) (boundaryTimeSlope A p)‖⁻¹ •
        outwardTraceVector A p) = timeGraphOutwardNormal A p := by
  rw [map_smul, timeGraphDifferential_outward]
  rfl

theorem timeGraphOutwardNormal_lift_coorientation (p : Boundary A) :
    boundaryDefiningDifferential A p.val
      (‖NormalGraphPlane.outwardRaw (outwardNormal A p) (boundaryTimeSlope A p)‖⁻¹ •
        outwardTraceVector A p) < 0 := by
  rw [map_smul]
  exact mul_neg_of_pos_of_neg
    (inv_pos.mpr (norm_pos_iff.mpr
      (NormalGraphPlane.outwardRaw_ne_zero (norm_outwardNormal A p) _)))
    (boundaryDefiningDifferential_outward A p)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
