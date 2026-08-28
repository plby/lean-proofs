import Wikipedia.NoExoticSixSphere.RoundedTraceTimeGraphNormal
import Wikipedia.NoExoticSixSphere.CylinderNormalFrame

/-!
# A full smooth normal framing of the time-slab embedding

The old trace frame is lifted with zero time component. The projected time
column is orthogonal to it. Their orthogonal sum is norm preserving and,
by the actual dimension calculation, spans the entire graph normal space.
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

def timeGraphLiftedFrame (p : ambientSet A) :
    Vector ((e.ambientDimension - 6) + 5) →L[ℝ] TimeGraphSpace (e := e) :=
  CylinderNormalFrame.liftFrame (traceNormalFrame A p)

theorem contMDiff_timeGraphLiftedFrame : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6))
      𝓘(ℝ, Vector ((e.ambientDimension - 6) + 5) →L[ℝ] TimeGraphSpace (e := e)) ∞
      (timeGraphLiftedFrame A) := by
  let := traceChartedSpace A
  exact contMDiff_const.clm_comp (contMDiff_const.clm_comp (contMDiff_traceNormalFrame A))

theorem timeGraphLiftedFrame_mem (p : ambientSet A)
    (v : Vector ((e.ambientDimension - 6) + 5)) :
    timeGraphLiftedFrame A p v ∈ (timeGraphDifferential A p).rangeᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨w, rfl⟩
  have hc := congrArg
    (fun D : (ℝ × Vector 6) →L[ℝ] (ℝ × Vector (e.ambientDimension + 6)) ↦ D w)
    (timeGraphDifferential_coordinates A p)
  have hn : traceNormalFrame A p v ∈ (traceAmbientDerivative A p).rangeᗮ := by
    rw [← traceNormalFrame_range]
    exact ⟨v, rfl⟩
  have he : timeGraphDifferential A p w =
      WithLp.toLp 2 (bordismTimeDifferential A p w, traceAmbientDerivative A p w) :=
    (timeGraphCoordinates (e := e)).injective hc
  change inner ℝ (timeGraphDifferential A p w) (timeGraphLiftedFrame A p v) = 0
  rw [he]
  change inner ℝ (WithLp.toLp 2 (_, _)) (WithLp.toLp 2 (0, traceNormalFrame A p v)) = 0
  simp only [WithLp.prod_inner_apply, inner_zero_right, zero_add]
  exact (traceAmbientDerivative A p).range.inner_right_of_mem_orthogonal ⟨w, rfl⟩ hn

theorem timeGraphNewNormal_orthogonal_frame (p : ambientSet A)
    (v : Vector ((e.ambientDimension - 6) + 5)) :
    inner ℝ (timeGraphNewNormal A p) (timeGraphLiftedFrame A p v) = 0 := by
  change inner ℝ (‖timeGraphNormalProjection A p (timeGraphTimeUnit (e := e))‖⁻¹ •
    timeGraphNormalProjection A p (timeGraphTimeUnit (e := e))) (timeGraphLiftedFrame A p v) = 0
  rw [real_inner_smul_left]
  have he : inner ℝ (timeGraphNormalProjection A p (timeGraphTimeUnit (e := e)))
      (timeGraphLiftedFrame A p v) = 0 := by
    rw [timeGraphNormalProjection, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (timeGraphLiftedFrame_mem A p v)]
    change inner ℝ (WithLp.toLp 2 (1, 0)) (WithLp.toLp 2 (0, traceNormalFrame A p v)) = 0
    simp only [WithLp.prod_inner_apply, inner_zero_right, inner_zero_left, add_zero]
  rw [he, mul_zero]

abbrev TimeGraphFrameSpace := WithLp 2 (Vector ((e.ambientDimension - 6) + 5) × ℝ)

def timeGraphFrameCoordinates : TimeGraphFrameSpace (e := e) ≃L[ℝ]
    (Vector ((e.ambientDimension - 6) + 5) × ℝ) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (Vector ((e.ambientDimension - 6) + 5)) ℝ

def timeGraphFrame (p : ambientSet A) :
    TimeGraphFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e) :=
  (timeGraphLiftedFrame A p).comp
    ((ContinuousLinearMap.fst ℝ _ ℝ).comp
      (timeGraphFrameCoordinates (e := e)).toContinuousLinearMap) +
    ((ContinuousLinearMap.snd ℝ (Vector ((e.ambientDimension - 6) + 5)) ℝ).comp
      (timeGraphFrameCoordinates (e := e)).toContinuousLinearMap).smulRight (timeGraphNewNormal A p)

theorem timeGraphFrame_apply (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphFrame A p v = timeGraphLiftedFrame A p v.fst + v.snd • timeGraphNewNormal A p :=
  rfl

theorem contMDiff_timeGraphFrame : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6))
      𝓘(ℝ, TimeGraphFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) ∞
      (timeGraphFrame A) := by
  let := traceChartedSpace A
  unfold timeGraphFrame
  apply ((contMDiff_timeGraphLiftedFrame A).clm_comp contMDiff_const).add
  exact (ContinuousLinearMap.smulRightL ℝ (TimeGraphFrameSpace (e := e))
    (TimeGraphSpace (e := e)) _).contDiff.contMDiff.comp (contMDiff_timeGraphNewNormal A)

theorem inner_timeGraphFrame (p : ambientSet A) (u v : TimeGraphFrameSpace (e := e)) :
    inner ℝ (timeGraphFrame A p u) (timeGraphFrame A p v) = inner ℝ u v := by
  have hB := (Stiefel.toIsometry ⟨traceNormalFrame A p, traceNormalFrame_norm A p⟩).inner_map_map
    u.fst v.fst
  change inner ℝ (traceNormalFrame A p u.fst) (traceNormalFrame A p v.fst) = _ at hB
  have ho (w : Vector ((e.ambientDimension - 6) + 5)) :
      inner ℝ (timeGraphLiftedFrame A p w) (timeGraphNewNormal A p) = 0 :=
    (real_inner_comm _ _).trans (timeGraphNewNormal_orthogonal_frame A p w)
  rw [timeGraphFrame_apply, timeGraphFrame_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    timeGraphNewNormal_orthogonal_frame, ho, mul_zero, add_zero, zero_add,
    real_inner_self_eq_norm_sq, norm_timeGraphNewNormal, one_pow, mul_one]
  change inner ℝ (WithLp.toLp 2 ((0 : ℝ), traceNormalFrame A p u.fst))
    (WithLp.toLp 2 ((0 : ℝ), traceNormalFrame A p v.fst)) + v.snd * u.snd = inner ℝ u v
  simp only [WithLp.prod_inner_apply, inner_zero_left, zero_add, hB, Real.inner_apply]
  change inner ℝ u.fst v.fst + v.snd * u.snd = inner ℝ u.fst v.fst + u.snd * v.snd
  ring

theorem norm_timeGraphFrame (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    ‖timeGraphFrame A p v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_timeGraphFrame A p v v

theorem injective_timeGraphFrame (p : ambientSet A) : Injective (timeGraphFrame A p) := by
  let L : TimeGraphFrameSpace (e := e) →ₗᵢ[ℝ] TimeGraphSpace (e := e) :=
    { toLinearMap := (timeGraphFrame A p).toLinearMap
      norm_map' := norm_timeGraphFrame A p }
  exact L.injective

theorem timeGraphFrame_range_le (p : ambientSet A) :
    (timeGraphFrame A p).range ≤ (timeGraphDifferential A p).rangeᗮ := by
  rintro _ ⟨v, rfl⟩
  change timeGraphFrame A p v ∈ (timeGraphDifferential A p).rangeᗮ
  rw [timeGraphFrame_apply]
  exact Submodule.add_mem _ (timeGraphLiftedFrame_mem A p v.fst)
    (Submodule.smul_mem _ _ (timeGraphNewNormal_mem A p))

theorem timeGraphFrame_range (p : ambientSet A) :
    (timeGraphFrame A p).range = (timeGraphDifferential A p).rangeᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq (timeGraphFrame_range_le A p)
  rw [LinearMap.finrank_range_of_inj (injective_timeGraphFrame A p)]
  have hd := (timeGraphDifferential A p).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (injective_timeGraphDifferential A p),
    (timeGraphCoordinates (e := e)).finrank_eq] at hd
  rw [(timeGraphFrameCoordinates (e := e)).finrank_eq]
  simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin] at hd ⊢
  have hN := e.dimension_le_ambient (f (pole 3))
  omega

theorem timeGraphFrame_range_projection (p : ambientSet A) :
    (timeGraphFrame A p).range = (timeGraphNormalProjection A p).range :=
  (timeGraphFrame_range A p).trans
    ((timeGraphDifferential A p).rangeᗮ.range_starProjection).symm

def timeGraphRangeFrame : letI := traceChartedSpace A;
    SmoothRangeFrame (ProductHalfSpace.model (Vector 6)) (timeGraphNormalProjection A)
      (TimeGraphFrameSpace (e := e)) := by
  let := traceChartedSpace A
  let P := timeGraphNormalProjection A
  let q (p : ambientSet A) : TimeGraphFrameSpace (e := e) ≃L[ℝ] (P p).range :=
    (LinearEquiv.ofInjective (timeGraphFrame A p).toLinearMap
      (injective_timeGraphFrame A p)).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (timeGraphFrame_range_projection A p))
  refine ⟨q, ?_⟩
  have he : (fun p ↦ (P p).range.subtypeL.comp (q p).toContinuousLinearMap) =
      timeGraphFrame A := by
    funext p
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [he]
  exact contMDiff_timeGraphFrame A

theorem timeGraphRangeFrame_ambient (p : ambientSet A) : letI := traceChartedSpace A;
    (timeGraphRangeFrame A).ambient p = timeGraphFrame A p := by
  let := traceChartedSpace A
  apply ContinuousLinearMap.ext
  intro w
  rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
