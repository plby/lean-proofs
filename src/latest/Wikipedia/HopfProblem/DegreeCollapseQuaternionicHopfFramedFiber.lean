import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfProductLift
import Wikipedia.NoExoticSixSphere.NormalBundle
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# The original Hopf-square regular fiber as a framed Euclidean embedding

The source has exactly the existing regular-fiber atlas. Its embedding is
the original inclusion into R17. The eleven normal coordinates are related
to the original radial-plus-target coordinates by the fixed tail isometry.
The explicit product-column deformation ends at this concrete normal frame.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFramedFiber

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph

abbrev Fiber := {x : Sphere 16 // smoothMap x = QuaternionicHopfProductFiber.point}

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold
local instance : CompactSpace Fiber :=
  isCompact_iff_compactSpace.mp (isClosed_eq smoothMap.continuous continuous_const).isCompact

def embedding : EuclideanEmbedding 6 Fiber where
  ambientDimension := 17
  toFun := SphereFiberNormalFrame.ambientInclusion smoothMap QuaternionicHopfProductFiber.point
  smooth := SphereFiberNormalFrame.contMDiff_ambientInclusion smoothMap smoothMap_contMDiff
    QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide)
  closedEmbedding := (continuous_subtype_val.comp continuous_subtype_val).isClosedEmbedding
    (Subtype.val_injective.comp Subtype.val_injective)
  injective_mfderiv := SphereFiberNormalFrame.injective_ambientDifferential
    smoothMap smoothMap_contMDiff QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide)

theorem embedding_apply (x : Fiber) : embedding.toFun x = x.val.val := rfl

def equationFrame (a : Sphere 16) : SmoothRangeFrame (𝓡 6) embedding.normalProjection
    QuaternionicHopfInducedProductFrame.Normal :=
  SphereFiberNormalFrame.normalFrame smoothMap smoothMap_contMDiff
    QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide) a

def normalCoordinates : embedding.NormalModel ≃L[ℝ] QuaternionicHopfInducedProductFrame.Normal :=
  (EuclideanTailCoordinates.split 10).toContinuousLinearEquiv

def framing (a : Sphere 16) :
    SmoothRangeFrame (𝓡 6) embedding.normalProjection embedding.NormalModel where
  equiv x := normalCoordinates.trans ((equationFrame a).equiv x)
  smooth := by
    have he : (fun x ↦ (embedding.normalProjection x).range.subtypeL.comp
        (normalCoordinates.trans ((equationFrame a).equiv x)).toContinuousLinearMap) =
        fun x ↦ ((equationFrame a).ambient x).comp normalCoordinates.toContinuousLinearMap := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [he]
    exact (equationFrame a).contMDiff_ambient.clm_comp contMDiff_const

theorem framing_ambient (a : Sphere 16) (x : Fiber) :
    (framing a).ambient x = ((equationFrame a).ambient x).comp
      normalCoordinates.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem embedding_fiberDiffeomorph (p : Sphere 3 × Sphere 3) :
    embedding.toFun (fiberDiffeomorph p) = QuaternionicHopfInducedProductFrame.ambientInclusion p :=
  rfl

theorem framing_fiberDiffeomorph (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    (framing a).ambient (fiberDiffeomorph p) =
      ((QuaternionicHopfInducedProductFrame.normalFrame a).ambient p).comp
        normalCoordinates.toContinuousLinearMap := by
  rw [framing_ambient]
  exact congrArg (fun L : QuaternionicHopfInducedProductFrame.Normal →L[ℝ] V 17 ↦
    L.comp normalCoordinates.toContinuousLinearMap)
      (QuaternionicHopfInducedProductFrame.normalFrame_fiberDiffeomorph a p).symm

def framingDeformation (a : Sphere 16) (p : ℝ × (Sphere 3 × Sphere 3)) :
    embedding.NormalModel →L[ℝ] V 17 :=
  (QuaternionicHopfProductLift.normalization a p).comp normalCoordinates.toContinuousLinearMap

theorem contMDiff_framingDeformation (a : Sphere 16) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      𝓘(ℝ, embedding.NormalModel →L[ℝ] V 17) ∞ (framingDeformation a) :=
  (QuaternionicHopfProductLift.contMDiff_normalization a).clm_comp contMDiff_const

theorem framingDeformation_zero (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    framingDeformation a (0, p) = (QuaternionicHopfProductLift.fullRightInverse p).comp
      normalCoordinates.toContinuousLinearMap := by
  rw [framingDeformation, QuaternionicHopfProductLift.normalization_zero]

theorem framingDeformation_one (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    framingDeformation a (1, p) = (framing a).ambient (fiberDiffeomorph p) := by
  rw [framingDeformation, QuaternionicHopfProductLift.normalization_one, framing_fiberDiffeomorph]

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFramedFiber
