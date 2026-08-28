import Wikipedia.NoExoticSixSphere.AttachingProductRadiusCoordinates
import Wikipedia.NoExoticSixSphere.UnroundedSurgeryTrace

/-!
# Normalize the actual framed attaching product to surgery radius one

The transverse linear coordinate change preserves every geometric and
framing condition. In particular, its bijective derivative preserves the
actual tangent image, so the existing normal frame remains a full frame.
The original manifold and its smooth atlas are untouched.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def normalizedRadius : FramedAttachingProduct e a f where
  disk := A.disk
  map := A.map ∘ A.productRadiusCoordinates
  map_core x := by
    change A.map (x, A.transverseRadiusCoordinates 0) = A.disk.toFun x
    rw [map_zero, A.map_core]
  innerRadius := A.innerRadius
  innerRadius_pos := A.innerRadius_pos
  innerRadius_lt_one := A.innerRadius_lt_one
  radius := 2
  radius_pos := by norm_num
  embedded := A.isClosedEmbedding_radiusProduct
  smooth x hx v hv := (A.smooth x hx _ (A.transverseRadiusCoordinates_mem hv)).comp (x, v)
    A.productRadiusCoordinates.contDiff.contDiffAt
  immersive x hx v hv := A.injective_fderiv_radiusProduct hx hv
  tube := A.tube ∘ A.tubeRadiusCoordinates
  tube_core s := by
    change A.tube (s, A.transverseRadiusCoordinates 0) = f s
    rw [map_zero, A.tube_core]
  tube_embedded := A.isClosedEmbedding_radiusTube
  tube_localDiffeomorph s v hv := (A.tubeRadiusCoordinates.isLocalDiffeomorph (s, v)).comp (𝓡 6) M
    (A.tube_localDiffeomorph s _ (A.transverseRadiusCoordinates_mem hv))
  collar_map x hx hxr v hv := A.collar_map x hx hxr _ (A.transverseRadiusCoordinates_mem hv)
  interior_avoids x hx v hv := A.interior_avoids x hx _ (A.transverseRadiusCoordinates_mem hv)
  normalFrame := A.normalFrame ∘ A.productRadiusCoordinates
  normalFrame_smooth x hx v hv :=
    (A.normalFrame_smooth x hx _ (A.transverseRadiusCoordinates_mem hv)).comp (x, v)
      A.productRadiusCoordinates.contDiff.contDiffAt
  normalFrame_norm x hx v hv w :=
    A.normalFrame_norm x hx _ (A.transverseRadiusCoordinates_mem hv) w
  normalFrame_range x hx v hv := by
    exact (A.normalFrame_range x hx _ (A.transverseRadiusCoordinates_mem hv)).trans
      (congrArg (fun S : Submodule ℝ (Vector (e.ambientDimension + 6)) ↦ Sᗮ)
        (A.range_fderiv_radiusProduct hx hv)).symm
  collar_frame x hx hxr v hv := A.collar_frame x hx hxr _ (A.transverseRadiusCoordinates_mem hv)

theorem normalizedRadius_radius : A.normalizedRadius.radius = 2 := rfl

theorem normalizedRadius_handleRadius : UnroundedTrace.handleRadius A.normalizedRadius = 1 := by
  norm_num [UnroundedTrace.handleRadius, normalizedRadius_radius]

theorem normalizedRadius_map (p : Vector 4 × Vector 3) :
    A.normalizedRadius.map p = A.map (p.1, A.radiusScale • p.2) := rfl

theorem normalizedRadius_tube (p : Sphere 3 × Vector 3) :
    A.normalizedRadius.tube p = A.tube (p.1, A.radiusScale • p.2) := rfl

theorem normalizedRadius_frame (p : Vector 4 × Vector 3) :
    A.normalizedRadius.normalFrame p = A.normalFrame (p.1, A.radiusScale • p.2) := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct
