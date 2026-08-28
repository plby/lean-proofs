import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenBoundary
import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm
import Wikipedia.NoExoticSixSphere.SuperlevelDifferential
import Wikipedia.NoExoticSixSphere.SuperlevelBoundary

/-!
# The actual positive half of any collared state, with its native normal frame

Regularity of the state's own time function constructs its half-space
charts. The half inclusion has a bijective full tangent map at every
point, including the boundary. Its restricted Euclidean embedding thus
has the original ambient tangent image and the original normal columns.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

abbrev Half := TimeCollar.NonnegativeHalf S.time

def halfAtlas : SuperlevelAtlas (K := Vector 6) (𝓡 7) S.time :=
  Classical.choice (nonempty_superlevelAtlas S.time_smooth S.time_regular 6 (by simp))

@[instance_reducible]
def halfChartedSpace : ChartedSpace (ProductHalfSpace.Space (Vector 6)) S.Half :=
  S.halfAtlas.chartedSpace

theorem half_isManifold : letI := S.halfChartedSpace;
    IsManifold (ProductHalfSpace.model (Vector 6)) ∞ S.Half := S.halfAtlas.isManifold

theorem half_boundary_iff (p : S.Half) : letI := S.halfChartedSpace;
    (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p ↔ S.time p.val = 0 :=
  S.halfAtlas.isBoundaryPoint_iff p

theorem compactSpace_half : CompactSpace S.Half :=
  isCompact_iff_compactSpace.mp
    (isClosed_le continuous_const S.time_smooth.continuous).isCompact

theorem contMDiff_halfInclusion : letI := S.halfChartedSpace;
    ContMDiff (ProductHalfSpace.model (Vector 6)) (𝓡 7) ∞
      (Subtype.val : S.Half → S.Space) := S.halfAtlas.contMDiff_subtype_val

theorem bijective_mfderiv_halfInclusion (p : S.Half) : letI := S.halfChartedSpace;
    Bijective (mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 7)
      (Subtype.val : S.Half → S.Space) p) := S.halfAtlas.bijective_mfderiv_subtype_val p

def halfAmbientMap (p : S.Half) : Vector S.embedding.ambientDimension := S.embedding.toFun p.val

theorem contMDiff_halfAmbientMap : letI := S.halfChartedSpace;
    ContMDiff (ProductHalfSpace.model (Vector 6)) (𝓡 S.embedding.ambientDimension) ∞
      S.halfAmbientMap := by
  let := S.halfChartedSpace
  exact S.embedding.smooth.comp S.contMDiff_halfInclusion

theorem isClosedEmbedding_halfAmbientMap : IsClosedEmbedding S.halfAmbientMap :=
  S.embedding.closedEmbedding.comp
    (isClosed_le continuous_const S.time_smooth.continuous).isClosedEmbedding_subtypeVal

def halfAmbientDerivative (p : S.Half) :
    (ℝ × Vector 6) →L[ℝ] Vector S.embedding.ambientDimension :=
  letI := S.halfChartedSpace
  mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 S.embedding.ambientDimension) S.halfAmbientMap p

theorem halfAmbientDerivative_eq (p : S.Half) : letI := S.halfChartedSpace;
    S.halfAmbientDerivative p =
      (mfderiv (𝓡 7) (𝓡 S.embedding.ambientDimension) S.embedding.toFun p.val).comp
        (mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 7)
          (Subtype.val : S.Half → S.Space) p) := by
  let := S.halfChartedSpace
  exact mfderiv_comp p (S.embedding.smooth.mdifferentiableAt (by simp))
    (S.contMDiff_halfInclusion.mdifferentiableAt (by simp))

theorem injective_halfAmbientDerivative (p : S.Half) : Injective (S.halfAmbientDerivative p) := by
  let := S.halfChartedSpace
  rw [halfAmbientDerivative_eq]
  exact (S.embedding.injective_mfderiv p.val).comp
    (S.bijective_mfderiv_halfInclusion p).injective

theorem range_halfAmbientDerivative (p : S.Half) :
    (S.halfAmbientDerivative p).range = S.embedding.tangentImage p.val := by
  let := S.halfChartedSpace
  rw [halfAmbientDerivative_eq]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    (S.bijective_mfderiv_halfInclusion p).surjective)

def halfNormalProjection (p : S.Half) :
    Vector S.embedding.ambientDimension →L[ℝ] Vector S.embedding.ambientDimension :=
  (S.halfAmbientDerivative p).rangeᗮ.starProjection

theorem halfNormalProjection_range (p : S.Half) :
    (S.halfNormalProjection p).range = (S.embedding.normalProjection p.val).range := by
  have hr : (S.halfNormalProjection p).range = (S.halfAmbientDerivative p).rangeᗮ :=
    Submodule.range_starProjection _
  rw [hr, S.range_halfAmbientDerivative p, S.embedding.range_normalProjection p.val]
  rfl

def halfNormalFraming : letI := S.halfChartedSpace;
    SmoothRangeFrame (ProductHalfSpace.model (Vector 6)) S.halfNormalProjection
      S.embedding.NormalModel := by
  let := S.halfChartedSpace
  let F (p : S.Half) := S.normalFrame.ambient p.val
  let P := S.halfNormalProjection
  have hF (p : S.Half) : (F p).range = (P p).range :=
    (S.normalFrame.ambient_range p.val).trans (S.halfNormalProjection_range p).symm
  let q (p : S.Half) : S.embedding.NormalModel ≃L[ℝ] (P p).range :=
    (LinearEquiv.ofInjective (F p).toLinearMap (S.normalFrame.ambient_injective p.val)
      ).toContinuousLinearEquiv.trans (ContinuousLinearEquiv.ofEq _ _ (hF p))
  refine ⟨q, ?_⟩
  have he : (fun p : S.Half ↦ (P p).range.subtypeL.comp (q p).toContinuousLinearMap) = F := by
    funext p
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact S.normalFrame.smooth.comp S.contMDiff_halfInclusion

theorem halfNormalFraming_ambient (p : S.Half) : letI := S.halfChartedSpace;
    S.halfNormalFraming.ambient p = S.normalFrame.ambient p.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
