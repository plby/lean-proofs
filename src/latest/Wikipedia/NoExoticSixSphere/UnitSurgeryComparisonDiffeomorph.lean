import Wikipedia.NoExoticSixSphere.UnitSurgeryComparisonInjective
import Wikipedia.NoExoticSixSphere.UnitSurgeryLocalCoordinates
import Wikipedia.NoExoticSixSphere.UnitSurgeryEndPointSmooth

/-!
# The actual complementary boundary end is diffeomorphic to canonical surgery

The forward map is the checked smooth comparison. Its inverse is smooth
because on each canonical local-diffeomorphism parametrization it equals
the actual smooth boundary parametrization. Both independently constructed
atlases, and in particular the original manifold atlas, are unchanged.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def comparisonEquiv : otherBoundaryPart A ≃ Target A hR :=
  Equiv.ofBijective (comparisonMap A hR) (bijective_comparisonMap A hR)

theorem comparisonEquiv_symm_exterior (p : retainedExterior A) :
    (comparisonEquiv A hR).symm (exteriorMap A hR p) = exteriorEndPoint A p := by
  rw [← comparisonMap_exteriorEndPoint A hR p]
  exact (comparisonEquiv A hR).symm_apply_apply _

theorem comparisonEquiv_symm_handle (p : boundaryHandleParameters A) :
    (comparisonEquiv A hR).symm (handleMap A hR p) = handleEndPoint A p := by
  rw [← comparisonMap_handleEndPoint A hR p]
  exact (comparisonEquiv A hR).symm_apply_apply _

theorem comparisonEquiv_symm_collar (p : boundaryCollarParameters A) :
    (comparisonEquiv A hR).symm (collarMap A hR p) = collarEndPoint A p := by
  rw [← comparisonMap_collarEndPoint A hR p]
  exact (comparisonEquiv A hR).symm_apply_apply _

theorem contMDiff_comparisonEquiv_symm : letI := boundaryChartedSpace A;
    letI := targetChartedSpace A hR;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (comparisonEquiv A hR).symm := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  intro q
  rcases target_cover A hR q with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
  · apply (contMDiffAt_comp_localDiffeomorph_iff
      (isLocalDiffeomorphAt_exteriorMap A hR p) (comparisonEquiv A hR).symm).mp
    have he : (comparisonEquiv A hR).symm ∘ exteriorMap A hR = exteriorEndPoint A :=
      funext (comparisonEquiv_symm_exterior A hR)
    rw [he]
    exact contMDiff_exteriorEndPoint A p
  · apply (contMDiffAt_comp_localDiffeomorph_iff
      (isLocalDiffeomorphAt_handleMap A hR p) (comparisonEquiv A hR).symm).mp
    have he : (comparisonEquiv A hR).symm ∘ handleMap A hR = handleEndPoint A :=
      funext (comparisonEquiv_symm_handle A hR)
    rw [he]
    exact contMDiff_handleEndPoint A p
  · apply (contMDiffAt_comp_localDiffeomorph_iff
      (isLocalDiffeomorphAt_collarMap A hR p) (comparisonEquiv A hR).symm).mp
    have he : (comparisonEquiv A hR).symm ∘ collarMap A hR = collarEndPoint A :=
      funext (comparisonEquiv_symm_collar A hR)
    rw [he]
    exact contMDiff_collarEndPoint A p

def comparisonDiffeomorph : letI := boundaryChartedSpace A;
    letI := targetChartedSpace A hR;
    otherBoundaryPart A ≃ₘ⟮𝓡 6, 𝓡 6⟯ Target A hR := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact
    { toEquiv := comparisonEquiv A hR
      contMDiff_toFun := contMDiff_comparisonMap A hR
      contMDiff_invFun := contMDiff_comparisonEquiv_symm A hR }

theorem comparisonDiffeomorph_apply (p : otherBoundaryPart A) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    comparisonDiffeomorph A hR p = comparisonMap A hR p := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
