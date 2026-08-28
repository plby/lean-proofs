import Wikipedia.NoExoticSixSphere.RoundedTraceCutoffTimeTangent

/-!
# A smooth transverse frame vertical near both slab ends

Subtracting a tangent vector times each column's time component does not
change its orthogonal normal projection. The resulting frame is transverse,
not asserted orthogonal. Near the native boundary every column has time zero.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def verticalShear (p : ambientSet A) : TimeGraphSpace (e := e) →L[ℝ] TimeGraphSpace (e := e) :=
  1 - (timeGraphTimeFunctional (e := e)).smulRight (cutoffTimeTangent A p)

theorem verticalShear_apply (p : ambientSet A) (v : TimeGraphSpace (e := e)) :
    verticalShear A p v = v - timeGraphTimeFunctional (e := e) v • cutoffTimeTangent A p := rfl

theorem contMDiff_verticalShear : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6))
      𝓘(ℝ, TimeGraphSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) ∞ (verticalShear A) := by
  let := traceChartedSpace A
  exact contMDiff_const.sub
    ((ContinuousLinearMap.smulRightL ℝ (TimeGraphSpace (e := e)) (TimeGraphSpace (e := e))
      (timeGraphTimeFunctional (e := e))).contDiff.contMDiff.comp (contMDiff_cutoffTimeTangent A))

theorem normalProjection_verticalShear (p : ambientSet A) (v : TimeGraphSpace (e := e)) :
    timeGraphNormalProjection A p (verticalShear A p v) = timeGraphNormalProjection A p v := by
  rw [verticalShear_apply, map_sub, map_smul, normalProjection_cutoffTimeTangent,
    smul_zero, sub_zero]

theorem timeFunctional_verticalShear (p : ambientSet A) (v : TimeGraphSpace (e := e)) :
    letI := traceChartedSpace A;
    timeGraphTimeFunctional (e := e) (verticalShear A p v) =
      (1 - verticalFrameCutoff A p) * timeGraphTimeFunctional (e := e) v := by
  let := traceChartedSpace A
  rw [verticalShear_apply, map_sub, map_smul, timeFunctional_cutoffTimeTangent]
  change timeGraphTimeFunctional (e := e) v -
    timeGraphTimeFunctional (e := e) v * verticalFrameCutoff A p = _
  ring

def verticalFrame (p : ambientSet A) :
    TimeGraphFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e) :=
  (verticalShear A p).comp (timeGraphFrame A p)

theorem contMDiff_verticalFrame : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6))
      𝓘(ℝ, TimeGraphFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) ∞ (verticalFrame A) := by
  let := traceChartedSpace A
  exact (contMDiff_verticalShear A).clm_comp (contMDiff_timeGraphFrame A)

theorem normalProjection_timeGraphFrame (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphNormalProjection A p (timeGraphFrame A p v) = timeGraphFrame A p v := by
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [← timeGraphFrame_range]
  exact ⟨v, rfl⟩

theorem normalProjection_verticalFrame (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphNormalProjection A p (verticalFrame A p v) = timeGraphFrame A p v := by
  change timeGraphNormalProjection A p (verticalShear A p (timeGraphFrame A p v)) = _
  rw [normalProjection_verticalShear, normalProjection_timeGraphFrame]

theorem injective_verticalFrame (p : ambientSet A) : Injective (verticalFrame A p) := by
  intro v w hvw
  apply injective_timeGraphFrame A p
  have he := congrArg (timeGraphNormalProjection A p) hvw
  simpa only [normalProjection_verticalFrame] using he

theorem timeFunctional_verticalFrame (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    letI := traceChartedSpace A;
    timeGraphTimeFunctional (e := e) (verticalFrame A p v) =
      (1 - verticalFrameCutoff A p) * timeGraphTimeFunctional (e := e) (timeGraphFrame A p v) :=
  timeFunctional_verticalShear A p (timeGraphFrame A p v)

theorem verticalFrame_time_zero_boundary (p : Boundary A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphTimeFunctional (e := e) (verticalFrame A p.val v) = 0 := by
  let := traceChartedSpace A
  rw [timeFunctional_verticalFrame, verticalFrameCutoff_one_boundary, sub_self, zero_mul]

theorem verticalFrame_eventually_time_zero :
    ∀ᶠ p in 𝓝ˢ (range (Subtype.val : Boundary A → ambientSet A)),
      ∀ v, timeGraphTimeFunctional (e := e) (verticalFrame A p v) = 0 := by
  let := traceChartedSpace A
  filter_upwards [verticalFrameCutoff_eventually_one A] with p hp v
  rw [timeFunctional_verticalFrame, hp, sub_self, zero_mul]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
