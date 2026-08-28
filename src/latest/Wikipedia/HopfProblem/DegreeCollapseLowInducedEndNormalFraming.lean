import Wikipedia.HopfProblem.DegreeCollapseSevenInducedEndNormalFraming
import Wikipedia.HopfProblem.DegreeCollapseLowNativeBoundaryEnds
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceCylinderOutwardNormal

/-!

# Constructed normal framings of the actual low-dimensional native ends

The full induced columns are expressed in the actual normal model of the
boundary embedding and restricted to its native complementary end. Every
column and its entire normal range are retained; no framing is an input.
The existing generic NormalColumns construction converts these exact columns
to a smooth range frame.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem boundaryNormalModel_dimension : letI := boundaryChartedSpace A;
    (boundaryEuclideanEmbedding A).ambientDimension - 7 =
      ((e.ambientDimension - 7) + (1 + (d + 1))) + 1 := by
  change (e.ambientDimension + (1 + (1 + (d + 1)))) - 7 =
    ((e.ambientDimension - 7) + (1 + (d + 1))) + 1
  have hN := e.dimension_le_ambient (f (spherePole d))
  omega

def boundaryNormalModelCoordinates : letI := boundaryChartedSpace A;
    (boundaryEuclideanEmbedding A).NormalModel ≃ₗᵢ[ℝ]
      Vector (((e.ambientDimension - 7) + (1 + (d + 1))) + 1) := by
  let := boundaryChartedSpace A
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (boundaryNormalModel_dimension A))

def boundaryFramingColumns : letI := boundaryChartedSpace A;
    Boundary A → (boundaryEuclideanEmbedding A).NormalModel →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) := by
  let := boundaryChartedSpace A
  exact fun p ↦ (inducedBoundaryFrame A p).comp
    (boundaryNormalModelCoordinates A).toContinuousLinearEquiv.toContinuousLinearMap

theorem boundaryFramingColumns_norm (p : Boundary A) : letI := boundaryChartedSpace A;
    ∀ v, ‖boundaryFramingColumns A p v‖ = ‖v‖ := by
  let := boundaryChartedSpace A
  intro v
  exact (inducedBoundaryFrame_norm A p (boundaryNormalModelCoordinates A v)).trans
    ((boundaryNormalModelCoordinates A).norm_map v)

theorem contMDiff_boundaryFramingColumns : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7) 𝓘(ℝ, (boundaryEuclideanEmbedding A).NormalModel →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ∞ (boundaryFramingColumns A) := by
  let := boundaryChartedSpace A
  exact (contMDiff_inducedBoundaryFrame A).clm_comp contMDiff_const

theorem boundaryFramingColumns_range (p : Boundary A) : letI := boundaryChartedSpace A;
    (boundaryFramingColumns A p).range =
      ((boundaryEuclideanEmbedding A).normalProjection p).range := by
  let := boundaryChartedSpace A
  have hr := LinearMap.range_comp_of_range_eq_top (inducedBoundaryFrame A p).toLinearMap
    (LinearMap.range_eq_top.mpr (boundaryNormalModelCoordinates A).surjective)
  exact hr.trans ((inducedBoundaryFrame_range A p).trans
    ((boundaryEuclideanEmbedding A).range_normalProjection p).symm)

def inducedBoundaryNormalFraming : letI := boundaryChartedSpace A;
    SmoothRangeFrame (𝓡 7) (boundaryEuclideanEmbedding A).normalProjection
      (boundaryEuclideanEmbedding A).NormalModel := by
  let := boundaryChartedSpace A
  exact NormalColumns.normalFraming (boundaryEuclideanEmbedding A) (boundaryFramingColumns A)
    (boundaryFramingColumns_norm A) (contMDiff_boundaryFramingColumns A)
    (boundaryFramingColumns_range A)

theorem inducedBoundaryNormalFraming_ambient (p : Boundary A) : letI := boundaryChartedSpace A;
    ∀ v, (inducedBoundaryNormalFraming A).ambient p v =
      inducedBoundaryFrame A p (boundaryNormalModelCoordinates A v) := by
  let := boundaryChartedSpace A
  intro v
  rfl

theorem otherBoundaryNormalProjection_range (p : otherBoundaryPart A) :
    letI := boundaryChartedSpace A;
    ((otherBoundaryEuclideanEmbedding A).normalProjection p).range =
      ((boundaryEuclideanEmbedding A).normalProjection p.val).range := by
  let := boundaryChartedSpace A
  have hD : (mfderiv (𝓡 7) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
      (fun q : otherBoundaryPart A ↦ q.val.val.val) p).range =
        (boundaryAmbientDerivative A p.val).range := by
    change (mfderiv (𝓡 7) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1)))))
      ((fun q : Boundary A ↦ q.val.val) ∘
        (Subtype.val : otherBoundaryPart A → Boundary A)) p).range = _
    rw [mfderiv_comp p ((contMDiff_boundaryAmbientInclusion A).mdifferentiableAt (by simp))
      ((_root_.contMDiff_subtype_val (I := 𝓡 7)
        (U := otherBoundaryPart A) (n := ∞)).mdifferentiableAt (by simp))]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
      (mfderiv_openSubset_val_bijective (I := 𝓡 7) (otherBoundaryPart A) p).2)
  exact ((otherBoundaryEuclideanEmbedding A).range_normalProjection p).trans
    ((congrArg (fun S : Submodule ℝ
      (Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ↦ Sᗮ) hD).trans
      ((boundaryEuclideanEmbedding A).range_normalProjection p.val).symm)

def inducedOtherEndNormalFraming : letI := boundaryChartedSpace A;
    SmoothRangeFrame (𝓡 7) (otherBoundaryEuclideanEmbedding A).normalProjection
      (otherBoundaryEuclideanEmbedding A).NormalModel := by
  let := boundaryChartedSpace A
  apply NormalColumns.normalFraming (otherBoundaryEuclideanEmbedding A)
    (fun p ↦ boundaryFramingColumns A p.val)
  · exact fun p ↦ boundaryFramingColumns_norm A p.val
  · exact (contMDiff_boundaryFramingColumns A).comp
      (_root_.contMDiff_subtype_val (I := 𝓡 7) (U := otherBoundaryPart A) (n := ∞))
  · exact fun p ↦ (boundaryFramingColumns_range A p.val).trans
      (otherBoundaryNormalProjection_range A p).symm

theorem inducedOtherEndNormalFraming_ambient (p : otherBoundaryPart A) :
    letI := boundaryChartedSpace A;
    ∀ v, (inducedOtherEndNormalFraming A).ambient p v =
      inducedBoundaryFrame A p.val (boundaryNormalModelCoordinates A v) := by
  let := boundaryChartedSpace A
  intro v
  rfl

theorem inducedOtherEndNormalFraming_norm (p : otherBoundaryPart A) :
    letI := boundaryChartedSpace A;
    ∀ v, ‖(inducedOtherEndNormalFraming A).ambient p v‖ = ‖v‖ := by
  let := boundaryChartedSpace A
  intro v
  rw [inducedOtherEndNormalFraming_ambient]
  exact boundaryFramingColumns_norm A p.val v

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
