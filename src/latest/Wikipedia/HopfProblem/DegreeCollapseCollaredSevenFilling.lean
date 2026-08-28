import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenHalf
import Wikipedia.HopfProblem.DegreeCollapseFramedSevenFilling
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport

/-!
# The positive half is a framed filling of the native regular zero fiber

The literal boundary of the native superlevel manifold is its zero fiber.
We give that boundary its induced regular-fiber charts through the identity
on ambient points, and prove its inclusion smooth and immersive. Together
with the restricted embedding and its actual full frame, this supplies
every field of a geometric framed filling. No initial filling or disk
recognition is assumed or concluded here.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

abbrev HalfBoundary := letI := S.halfChartedSpace;
  {p : S.Half // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p}

def halfBoundaryHomeomorph : S.HalfBoundary ≃ₜ S.Zero := by
  let := S.halfChartedSpace
  exact
    { toFun := fun p ↦ ⟨p.val.val, (S.half_boundary_iff p.val).mp p.property⟩
      invFun := fun p ↦ ⟨⟨p.val, p.property.symm.le⟩,
        (S.half_boundary_iff _).mpr p.property⟩
      left_inv := fun p ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun p ↦ Subtype.ext rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

@[instance_reducible]
def halfBoundaryAtlas : ChartedSpace (Vector 6) S.HalfBoundary := by
  let := S.zeroAtlas
  exact ModelAtlasTransport.atlas S.halfBoundaryHomeomorph

theorem halfBoundary_isManifold : letI := S.halfBoundaryAtlas;
    IsManifold (𝓡 6) ∞ S.HalfBoundary := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  exact ModelAtlasTransport.isManifold S.halfBoundaryHomeomorph (𝓡 6)

def halfBoundaryDiffeomorph : letI := S.halfBoundaryAtlas; letI := S.zeroAtlas;
    S.HalfBoundary ≃ₘ⟮𝓡 6, 𝓡 6⟯ S.Zero := by
  let := S.zeroAtlas
  exact ModelAtlasTransport.diffeomorph S.halfBoundaryHomeomorph (𝓡 6)

theorem halfBoundaryDiffeomorph_point (p : S.HalfBoundary) :
    letI := S.halfBoundaryAtlas; letI := S.zeroAtlas;
    (S.halfBoundaryDiffeomorph p).val = p.val.val := rfl

theorem contMDiff_halfBoundaryInclusion : letI := S.halfChartedSpace;
    letI := S.halfBoundaryAtlas;
    ContMDiff (𝓡 6) (ProductHalfSpace.model (Vector 6)) ∞
      (Subtype.val : S.HalfBoundary → S.Half) := by
  let := S.halfChartedSpace
  let := S.halfBoundaryAtlas
  let := S.zeroAtlas
  apply (S.halfAtlas.contMDiff_iff_ambient Subtype.val).mpr
  have hz : ContMDiff (𝓡 6) (𝓡 7) ∞ (Subtype.val : S.Zero → S.Space) :=
    regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp)
  exact hz.comp S.halfBoundaryDiffeomorph.contMDiff

def boundaryAmbientInclusion (p : S.HalfBoundary) : S.Space := p.val.val

theorem injective_mfderiv_boundaryAmbientInclusion (p : S.HalfBoundary) :
    letI := S.halfBoundaryAtlas;
    Injective (mfderiv (𝓡 6) (𝓡 7) S.boundaryAmbientInclusion p) := by
  let := S.halfBoundaryAtlas
  let := S.zeroAtlas
  let D := S.halfBoundaryDiffeomorph
  have hz : ContMDiff (𝓡 6) (𝓡 7) ∞ (Subtype.val : S.Zero → S.Space) :=
    regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp)
  have hi : Injective (mfderiv (𝓡 6) (𝓡 7) (Subtype.val : S.Zero → S.Space) (D p)) :=
    regularFiber_injective_mfderiv_subtype_val S.zeroTimeMap S.time_smooth 0
      S.time_regular 6 (by simp) (D p)
  change Injective (mfderiv (𝓡 6) (𝓡 7) ((Subtype.val : S.Zero → S.Space) ∘ D) p)
  rw [mfderiv_comp p (hz.mdifferentiableAt (by simp)) (D.contMDiff.mdifferentiableAt (by simp))]
  exact hi.comp ((D.isLocalDiffeomorph p).mfderivToContinuousLinearEquiv (by simp)).injective

theorem injective_mfderiv_halfBoundaryInclusion (p : S.HalfBoundary) :
    letI := S.halfChartedSpace; letI := S.halfBoundaryAtlas;
    Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
      (Subtype.val : S.HalfBoundary → S.Half) p) := by
  let := S.halfChartedSpace
  let := S.halfBoundaryAtlas
  have hc := mfderiv_comp p (S.contMDiff_halfInclusion.mdifferentiableAt (by simp))
    (S.contMDiff_halfBoundaryInclusion.mdifferentiableAt (by simp))
  intro u v he
  apply S.injective_mfderiv_boundaryAmbientInclusion p
  change (mfderiv (𝓡 6) (𝓡 7) ((Subtype.val : S.Half → S.Space) ∘
      (Subtype.val : S.HalfBoundary → S.Half)) p) u =
    (mfderiv (𝓡 6) (𝓡 7) ((Subtype.val : S.Half → S.Space) ∘
      (Subtype.val : S.HalfBoundary → S.Half)) p) v
  rw [hc]
  exact congrArg (mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 7)
    (Subtype.val : S.Half → S.Space) p.val) he

def framedFilling : letI := S.zeroAtlas; FramedSevenFilling (𝓡 6) S.Zero := by
  let := S.zeroAtlas
  let := S.halfChartedSpace
  let := S.halfBoundaryAtlas
  exact
    { W := S.Half
      topology := inferInstance
      hausdorff := S.isClosedEmbedding_halfAmbientMap.isEmbedding.t2Space
      secondCountable := S.isClosedEmbedding_halfAmbientMap.isEmbedding.secondCountableTopology
      compact := S.compactSpace_half
      atlas := S.halfChartedSpace
      manifold := S.half_isManifold
      ambientDimension := S.embedding.ambientDimension
      inclusion := S.halfAmbientMap
      closed_embedding := S.isClosedEmbedding_halfAmbientMap
      smooth_inclusion := S.contMDiff_halfAmbientMap
      injective_differential := S.injective_halfAmbientDerivative
      frame := S.halfNormalFraming
      boundaryAtlas := S.halfBoundaryAtlas
      boundaryManifold := S.halfBoundary_isManifold
      boundaryDiffeomorph := S.halfBoundaryDiffeomorph.symm
      smooth_boundaryInclusion := S.contMDiff_halfBoundaryInclusion
      injective_boundaryDifferential := S.injective_mfderiv_halfBoundaryInclusion }

theorem framedFilling_inclusion (p : S.Half) : letI := S.zeroAtlas;
    S.framedFilling.inclusion p = S.embedding.toFun p.val := rfl

theorem framedFilling_boundary_point (p : S.Zero) : letI := S.zeroAtlas;
    (S.framedFilling.boundaryDiffeomorph p).val.val = p.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
