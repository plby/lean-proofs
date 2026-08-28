import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryInducedPieceFrames

/-!
# The surgery framing in its actual Euclidean normal model

The explicit dimension equality reindexes the already constructed frame into
the normal model of the actual surgery embedding. This changes no frame
vectors; it supplies the standard `SmoothRangeFrame` input for subsequent
geometric constructions, with its exact ambient operator and norm retained.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem normalModel_dimension : letI := targetChartedSpace A hR;
    (inducedEmbedding A hR).ambientDimension - 7 = ((e.ambientDimension - 7) + 5) + 1 := by
  let := targetChartedSpace A hR
  change (e.ambientDimension + 6) - 7 = ((e.ambientDimension - 7) + 5) + 1
  have hN := e.dimension_le_ambient (f (pole 3))
  omega

def normalModelCoordinates : letI := targetChartedSpace A hR;
    (inducedEmbedding A hR).NormalModel ≃ₗᵢ[ℝ]
      Vector (((e.ambientDimension - 7) + 5) + 1) := by
  let := targetChartedSpace A hR
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (normalModel_dimension A hR))

def normalFraming : letI := targetChartedSpace A hR;
    SmoothRangeFrame (𝓡 7) (inducedEmbedding A hR).normalProjection
      (inducedEmbedding A hR).NormalModel := by
  let := targetChartedSpace A hR
  refine
    { equiv := fun p ↦ (normalModelCoordinates A hR).toContinuousLinearEquiv.trans
        ((inducedRangeFrame A hR).equiv p)
      smooth := ?_ }
  have he : (fun p : Target A hR ↦ ((inducedEmbedding A hR).normalProjection p).range.subtypeL.comp
      (((normalModelCoordinates A hR).toContinuousLinearEquiv.trans
        ((inducedRangeFrame A hR).equiv p)).toContinuousLinearMap)) =
      (fun p ↦ (inducedNormalFrame A hR p).comp
        (normalModelCoordinates A hR).toContinuousLinearMap) := by
    funext p
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [he]
  exact (contMDiff_inducedNormalFrame A hR).clm_comp contMDiff_const

theorem normalFraming_ambient (p : Target A hR) : letI := targetChartedSpace A hR;
    (normalFraming A hR).ambient p = (inducedNormalFrame A hR p).comp
      (normalModelCoordinates A hR).toContinuousLinearMap := by
  let := targetChartedSpace A hR
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem normalFraming_norm (p : Target A hR) : letI := targetChartedSpace A hR;
    ∀ w : (inducedEmbedding A hR).NormalModel, ‖(normalFraming A hR).ambient p w‖ = ‖w‖ := by
  let := targetChartedSpace A hR
  intro w
  rw [normalFraming_ambient]
  change ‖inducedNormalFrame A hR p (normalModelCoordinates A hR w)‖ = ‖w‖
  rw [inducedNormalFrame_norm]
  exact (normalModelCoordinates A hR).norm_map w

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
