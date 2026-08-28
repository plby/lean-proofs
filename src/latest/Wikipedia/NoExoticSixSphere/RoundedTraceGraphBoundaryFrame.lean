import Wikipedia.NoExoticSixSphere.RoundedTraceGraphBoundaryTangent
import Wikipedia.NoExoticSixSphere.OrthogonalUnitExtension
import Wikipedia.NoExoticSixSphere.RoundedTraceInducedBoundaryFrame

/-!
# Full native boundary frames throughout the normal-plane rotation

The source coordinates are ordered as old trace columns, new time column,
then outward column. At the actual slope this is the induced graph boundary
frame. At zero slope it is the old boundary frame stabilized by a time axis,
with the column order explicitly retained.
-/

noncomputable section

open Function Set Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

abbrev TimeGraphBoundaryFrameSpace := WithLp 2 (TimeGraphFrameSpace (e := e) × ℝ)

def graphBoundaryPlaneFrame (p : Boundary A) (s : ℝ) :
    TimeGraphBoundaryFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e) :=
  OrthogonalUnitExtension.operator
    (OrthogonalUnitExtension.operator (timeGraphLiftedFrame A p.val)
      (NormalGraphPlane.normalColumn (outwardNormal A p) s))
    (NormalGraphPlane.outwardColumn (outwardNormal A p) s)

theorem graphBoundaryPlaneFrame_apply (p : Boundary A) (s : ℝ)
    (v : TimeGraphBoundaryFrameSpace (e := e)) :
    graphBoundaryPlaneFrame A p s v = timeGraphLiftedFrame A p.val v.fst.fst +
      v.fst.snd • NormalGraphPlane.normalColumn (outwardNormal A p) s +
      v.snd • NormalGraphPlane.outwardColumn (outwardNormal A p) s := rfl

theorem norm_graphBoundaryPlaneFrame (p : Boundary A) (s : ℝ)
    (v : TimeGraphBoundaryFrameSpace (e := e)) : ‖graphBoundaryPlaneFrame A p s v‖ = ‖v‖ := by
  have hB (w : Vector ((e.ambientDimension - 6) + 5)) :
      ‖timeGraphLiftedFrame A p.val w‖ = ‖w‖ := by
    change ‖WithLp.toLp 2 ((0 : ℝ), traceNormalFrame A p.val w)‖ = ‖w‖
    rw [WithLp.norm_toLp_snd, traceNormalFrame_norm]
  have hn (w : Vector ((e.ambientDimension - 6) + 5)) :
      inner ℝ (NormalGraphPlane.normalColumn (outwardNormal A p) s)
        (timeGraphLiftedFrame A p.val w) = 0 :=
    NormalGraphPlane.normalColumn_orthogonal_lift _ _ (outwardNormal_orthogonal_frame A p w) s
  have ho (w : TimeGraphFrameSpace (e := e)) :
      inner ℝ (NormalGraphPlane.outwardColumn (outwardNormal A p) s)
        (OrthogonalUnitExtension.operator (timeGraphLiftedFrame A p.val)
          (NormalGraphPlane.normalColumn (outwardNormal A p) s) w) = 0 := by
    rw [OrthogonalUnitExtension.operator_apply, inner_add_right, real_inner_smul_right]
    have h₁ := NormalGraphPlane.outwardColumn_orthogonal_lift _ _
      (outwardNormal_orthogonal_frame A p w.fst) s
    have h₂ := (real_inner_comm _ _).trans
      (NormalGraphPlane.inner_columns (norm_outwardNormal A p) s)
    change inner ℝ (NormalGraphPlane.outwardColumn (outwardNormal A p) s)
      (timeGraphLiftedFrame A p.val w.fst) = 0 at h₁
    rw [h₁, h₂, mul_zero, add_zero]
  exact OrthogonalUnitExtension.norm_operator _
    (OrthogonalUnitExtension.norm_operator _ hB _ (NormalGraphPlane.norm_normalColumn _ s) hn)
    _ (NormalGraphPlane.norm_outwardColumn (norm_outwardNormal A p) s) ho v

theorem graphBoundaryPlaneFrame_range_le (p : Boundary A) (s : ℝ) :
    (graphBoundaryPlaneFrame A p s).range ≤ (timeGraphBoundaryDifferential A p).rangeᗮ := by
  rintro _ ⟨v, rfl⟩
  change graphBoundaryPlaneFrame A p s v ∈ (timeGraphBoundaryDifferential A p).rangeᗮ
  rw [graphBoundaryPlaneFrame_apply]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (timeGraphLiftedFrame_mem_boundary A p v.fst.fst)
      (Submodule.smul_mem _ _ (timeGraph_planeNormal_mem_boundary A p s)))
    (Submodule.smul_mem _ _ (timeGraph_planeOutward_mem_boundary A p s))

theorem graphBoundaryPlaneFrame_range (p : Boundary A) (s : ℝ) :
    (graphBoundaryPlaneFrame A p s).range = (timeGraphBoundaryDifferential A p).rangeᗮ := by
  let L : TimeGraphBoundaryFrameSpace (e := e) →ₗᵢ[ℝ] TimeGraphSpace (e := e) :=
    { toLinearMap := (graphBoundaryPlaneFrame A p s).toLinearMap
      norm_map' := norm_graphBoundaryPlaneFrame A p s }
  apply Submodule.eq_of_le_of_finrank_eq (graphBoundaryPlaneFrame_range_le A p s)
  rw [LinearMap.finrank_range_of_inj L.injective]
  have hd := (timeGraphBoundaryDifferential A p).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (injective_timeGraphBoundaryDifferential A p),
    (timeGraphCoordinates (e := e)).finrank_eq] at hd
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ (TimeGraphFrameSpace (e := e)) ℝ).finrank_eq,
    finrank_prod, (timeGraphFrameCoordinates (e := e)).finrank_eq]
  simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin] at hd ⊢
  have hN := e.dimension_le_ambient (f (pole 3))
  omega

theorem contMDiff_graphBoundaryPlaneFrame : letI := boundaryChartedSpace A;
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 6))
      𝓘(ℝ, TimeGraphBoundaryFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) ∞
      (fun q : ℝ × Boundary A ↦ graphBoundaryPlaneFrame A q.2 q.1) := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  have hsnd : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 6)) (𝓡 6) ∞
      (Prod.snd : ℝ × Boundary A → Boundary A) := contMDiff_snd
  have hν := (contMDiff_outwardNormal A).comp hsnd
  have hB := (contMDiff_timeGraphLiftedFrame A).comp
    ((contMDiff_boundaryInclusion A).comp hsnd)
  exact OrthogonalUnitExtension.contMDiff_operator
    (OrthogonalUnitExtension.contMDiff_operator hB
      (NormalGraphPlane.contMDiff_normalColumn hν contMDiff_fst))
    (NormalGraphPlane.contMDiff_outwardColumn hν contMDiff_fst (fun q ↦ norm_outwardNormal A q.2))

def timeGraphInducedBoundaryFrame (p : Boundary A) :
    TimeGraphBoundaryFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e) :=
  OrthogonalUnitExtension.operator (timeGraphFrame A p.val) (timeGraphOutwardNormal A p)

theorem continuous_graphBoundaryPlaneFrame :
    Continuous (fun q : ℝ × Boundary A ↦ graphBoundaryPlaneFrame A q.2 q.1) := by
  let := boundaryChartedSpace A
  exact (contMDiff_graphBoundaryPlaneFrame A).continuous

theorem graphBoundaryPlaneFrame_actual (p : Boundary A) :
    graphBoundaryPlaneFrame A p (boundaryTimeSlope A p) = timeGraphInducedBoundaryFrame A p := by
  unfold graphBoundaryPlaneFrame
  rw [← timeGraphNewNormal_boundary]
  rfl

theorem graphBoundaryPlaneFrame_zero (p : Boundary A)
    (v : TimeGraphBoundaryFrameSpace (e := e)) :
    graphBoundaryPlaneFrame A p 0 v = timeGraphLiftedFrame A p.val v.fst.fst +
      v.fst.snd • timeGraphTimeUnit (e := e) +
      v.snd • WithLp.toLp 2 ((0 : ℝ), outwardNormal A p) := by
  rw [graphBoundaryPlaneFrame_apply, NormalGraphPlane.normalColumn_zero,
    NormalGraphPlane.outwardColumn_zero (norm_outwardNormal A p)]
  rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
