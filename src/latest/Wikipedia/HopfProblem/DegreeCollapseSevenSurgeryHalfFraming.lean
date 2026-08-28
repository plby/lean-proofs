import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfEmbedding

/-!
# Full normal framing of the actual surgery half, including its boundary

The half and the closed surgery target have the same ambient tangent image.
Restrict the actual target frame and identify its range with the half's
normal projection. The frame values, norm, and exact signed seam formula
are preserved; no extra framing hypothesis is introduced.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

def halfNormalProjection (p : PositiveHalf A hR T) :
    Vector (e.ambientDimension + 6) →L[ℝ] Vector (e.ambientDimension + 6) :=
  (halfAmbientDerivative A hR T p).rangeᗮ.starProjection

theorem halfNormalProjection_range (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR;
    (halfNormalProjection A hR T p).range =
      ((inducedEmbedding A hR).normalProjection p.val).range := by
  let := targetChartedSpace A hR
  have hr : (halfNormalProjection A hR T p).range =
      (halfAmbientDerivative A hR T p).rangeᗮ := Submodule.range_starProjection _
  have hd := congrArg (fun S : Submodule ℝ (Vector (e.ambientDimension + 6)) ↦ Sᗮ)
    (range_halfAmbientDerivative A hR T p)
  have hn : ((inducedEmbedding A hR).normalProjection p.val).range =
      (ambientDerivative A hR p.val).rangeᗮ := (inducedEmbedding A hR).range_normalProjection p.val
  exact (hr.trans hd).trans hn.symm

def halfFrameColumns (p : PositiveHalf A hR T) : letI := targetChartedSpace A hR;
    (inducedEmbedding A hR).NormalModel →L[ℝ] Vector (e.ambientDimension + 6) := by
  let := targetChartedSpace A hR
  exact (normalFraming A hR).ambient p.val

theorem injective_halfFrameColumns (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR; Injective (halfFrameColumns A hR T p) := by
  let := targetChartedSpace A hR
  exact (normalFraming A hR).ambient_injective p.val

theorem contMDiff_halfFrameColumns : letI := targetChartedSpace A hR;
    letI := positiveHalfChartedSpace A hR T;
    ContMDiff (ProductHalfSpace.model (Vector 6))
      𝓘(ℝ, (inducedEmbedding A hR).NormalModel →L[ℝ] Vector (e.ambientDimension + 6)) ∞
        (halfFrameColumns A hR T) := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  exact (normalFraming A hR).smooth.comp (contMDiff_positiveHalfInclusion A hR T)

theorem halfFrameColumns_range (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR;
    (halfFrameColumns A hR T p).range = (halfNormalProjection A hR T p).range := by
  let := targetChartedSpace A hR
  exact ((normalFraming A hR).ambient_range p.val).trans (halfNormalProjection_range A hR T p).symm

def halfNormalFraming : letI := targetChartedSpace A hR;
    letI := positiveHalfChartedSpace A hR T;
    SmoothRangeFrame (ProductHalfSpace.model (Vector 6)) (halfNormalProjection A hR T)
      (inducedEmbedding A hR).NormalModel := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  let F := halfFrameColumns A hR T
  let P := halfNormalProjection A hR T
  let q (p : PositiveHalf A hR T) : (inducedEmbedding A hR).NormalModel ≃L[ℝ] (P p).range :=
    (LinearEquiv.ofInjective (F p).toLinearMap
      (injective_halfFrameColumns A hR T p)).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (halfFrameColumns_range A hR T p))
  refine ⟨q, ?_⟩
  have he : (fun p : PositiveHalf A hR T ↦ (P p).range.subtypeL.comp
      (q p).toContinuousLinearMap) = F := by
    funext p
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact contMDiff_halfFrameColumns A hR T

theorem halfNormalFraming_ambient (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    (halfNormalFraming A hR T).ambient p = (normalFraming A hR).ambient p.val := rfl

theorem halfNormalFraming_norm (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    ∀ v : (inducedEmbedding A hR).NormalModel, ‖(halfNormalFraming A hR T).ambient p v‖ = ‖v‖ := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  intro v
  rw [halfNormalFraming_ambient]
  exact normalFraming_norm A hR p.val v

theorem halfNormalFraming_range (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    ((halfNormalFraming A hR T).ambient p).range = (halfAmbientDerivative A hR T p).rangeᗮ := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  exact ((halfNormalFraming A hR T).ambient_range p).trans (Submodule.range_starProjection _)

theorem halfNormalFraming_on_retainedBand (p : retainedTimeBand A T)
    (q : PositiveHalf A hR T) (hq : q.val = retainedTimeMap A hR T p) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    (halfNormalFraming A hR T).ambient q =
      (OrthogonalFrameAppend.operator (boundaryFrameOperator (a.orthonormal p.val).val)
        (-heightUnit e.ambientDimension)).comp
          (normalModelCoordinates A hR).toContinuousLinearMap := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  rw [halfNormalFraming_ambient, normalFraming_ambient, hq, inducedNormalFrame_retainedTimeMap]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
