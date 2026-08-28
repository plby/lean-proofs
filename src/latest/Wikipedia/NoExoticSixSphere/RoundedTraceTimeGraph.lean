import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryTimeKernel

/-!
# A smooth closed embedding of the trace into a time slab

The graph uses the Euclidean product norm. Its first coordinate is the
constructed bordism time; projection to the remaining coordinates is the
original ambient embedding. The boundary slices are transverse and retain
the actual native boundary tangent spaces.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

abbrev TimeGraphSpace := WithLp 2 (ℝ × Vector (e.ambientDimension + 6))

def timeGraphCoordinates : TimeGraphSpace (e := e) ≃L[ℝ]
    (ℝ × Vector (e.ambientDimension + 6)) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Vector (e.ambientDimension + 6))

def timeGraph (p : ambientSet A) : TimeGraphSpace (e := e) :=
  (timeGraphCoordinates (e := e)).symm (bordismTime A p, p.val)

theorem contMDiff_timeGraph : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, TimeGraphSpace (e := e)) ∞
      (timeGraph A) := by
  let := traceChartedSpace A
  exact (timeGraphCoordinates (e := e)).symm.contDiff.contMDiff.comp
    ((contMDiff_bordismTime A).prodMk_space (trace_contMDiff_ambient A))

theorem timeGraph_coordinates (p : ambientSet A) :
    timeGraphCoordinates (e := e) (timeGraph A p) = (bordismTime A p, p.val) :=
  (timeGraphCoordinates (e := e)).apply_symm_apply _

theorem injective_timeGraph : Injective (timeGraph A) := by
  intro p q hpq
  have he := congrArg (timeGraphCoordinates (e := e)) hpq
  rw [timeGraph_coordinates, timeGraph_coordinates] at he
  exact Subtype.ext (congrArg Prod.snd he)

theorem isClosedEmbedding_timeGraph : IsClosedEmbedding (timeGraph A) := by
  let := traceChartedSpace A
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  exact (contMDiff_timeGraph A).continuous.isClosedEmbedding (injective_timeGraph A)

def timeGraphDifferential (p : ambientSet A) :
    (ℝ × Vector 6) →L[ℝ] TimeGraphSpace (e := e) :=
  letI := traceChartedSpace A
  mvfderiv (ProductHalfSpace.model (Vector 6)) (timeGraph A) p

theorem timeGraphDifferential_coordinates (p : ambientSet A) :
    (timeGraphCoordinates (e := e)).toContinuousLinearMap.comp (timeGraphDifferential A p) =
      (bordismTimeDifferential A p).prod (traceAmbientDerivative A p) := by
  let := traceChartedSpace A
  have hs : ContMDiff 𝓘(ℝ, TimeGraphSpace (e := e))
      𝓘(ℝ, ℝ × Vector (e.ambientDimension + 6)) ∞ (timeGraphCoordinates (e := e)) :=
    (timeGraphCoordinates (e := e)).contDiff.contMDiff
  have hc := mfderiv_comp p
    (hs.mdifferentiableAt (by simp))
    ((contMDiff_timeGraph A).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, (timeGraphCoordinates (e := e)).fderiv] at hc
  have he : timeGraphCoordinates (e := e) ∘ timeGraph A =
      (fun q ↦ (bordismTime A q, q.val)) := funext (timeGraph_coordinates A)
  have hprod := (hasMFDerivAt_prodMk_space
    ((contMDiff_bordismTime A).mdifferentiableAt (x := p) (by simp)).hasMFDerivAt
    ((trace_contMDiff_ambient A).mdifferentiableAt (x := p) (by simp)).hasMFDerivAt).mfderiv
  rw [he, hprod] at hc
  exact hc.symm

theorem injective_timeGraphDifferential (p : ambientSet A) :
    Injective (timeGraphDifferential A p) := by
  intro v w hvw
  apply injective_traceAmbientDerivative A p
  have he := congrArg (timeGraphCoordinates (e := e)) hvw
  have hcoord := timeGraphDifferential_coordinates A p
  have hv := congrArg
    (fun D : (ℝ × Vector 6) →L[ℝ] (ℝ × Vector (e.ambientDimension + 6)) ↦ D v) hcoord
  have hw := congrArg
    (fun D : (ℝ × Vector 6) →L[ℝ] (ℝ × Vector (e.ambientDimension + 6)) ↦ D w) hcoord
  exact congrArg Prod.snd (hv.symm.trans (he.trans hw))

theorem timeGraphDifferential_apply (p : ambientSet A) (v : ℝ × Vector 6) :
    timeGraphDifferential A p v =
      WithLp.toLp 2 (bordismTimeDifferential A p v, traceAmbientDerivative A p v) := by
  apply (timeGraphCoordinates (e := e)).injective
  exact congrArg
    (fun D : (ℝ × Vector 6) →L[ℝ] (ℝ × Vector (e.ambientDimension + 6)) ↦ D v)
    (timeGraphDifferential_coordinates A p)

theorem timeGraph_first_mem_Icc (p : ambientSet A) :
    (timeGraphCoordinates (e := e) (timeGraph A p)).1 ∈ Icc 0 1 := by
  rw [timeGraph_coordinates]
  exact bordismTime_mem_Icc A p

theorem timeGraph_boundary_iff (p : ambientSet A) : letI := traceChartedSpace A;
    (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p ↔
      (timeGraphCoordinates (e := e) (timeGraph A p)).1 = 0 ∨
      (timeGraphCoordinates (e := e) (timeGraph A p)).1 = 1 := by
  let := traceChartedSpace A
  rw [timeGraph_coordinates, bordismTime_zero_iff, bordismTime_one_iff]
  exact boundary_iff_mem_ends A p

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
