import Wikipedia.HopfProblem.DegreeCollapseLowAttachingProductRadiusCoordinates
import Wikipedia.HopfProblem.DegreeCollapseLowUnroundedSurgeryTrace

/-!

# Normalized low-dimensional framed attaching products with exact native data

The actual transverse coordinate change gives radius two and handle radius
one. Its bijective derivative preserves the original tangent image and hence
the full normal-frame range. The original disk, manifold atlas, native tube
values and whole prescribed collar frame are retained under reparametrization.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def normalizedRadius : FramedAttachingProduct e a f where
  disk := A.disk
  map := A.map ∘ A.productRadiusCoordinates
  map_core x := by
    change A.map (x, A.transverseRadiusCoordinates 0) = A.disk.map x
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
  tube_localDiffeomorph s v hv := (A.tubeRadiusCoordinates.isLocalDiffeomorph (s, v)).comp (𝓡 7) M
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
      (congrArg (fun S : Submodule ℝ (Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ↦ Sᗮ)
        (A.range_fderiv_radiusProduct hx hv)).symm
  collar_frame x hx hxr v hv := A.collar_frame x hx hxr _ (A.transverseRadiusCoordinates_mem hv)

theorem normalizedRadius_radius : A.normalizedRadius.radius = 2 := rfl

theorem normalizedRadius_handleRadius : UnroundedTrace.handleRadius A.normalizedRadius = 1 := by
  norm_num [UnroundedTrace.handleRadius, normalizedRadius_radius]

theorem normalizedRadius_map (p : Vector (d + 1) × Vector (7 - d)) :
    A.normalizedRadius.map p = A.map (p.1, A.radiusScale • p.2) := rfl

theorem normalizedRadius_tube (p : NoExoticSixSphere.Sphere d × Vector (7 - d)) :
    A.normalizedRadius.tube p = A.tube (p.1, A.radiusScale • p.2) := rfl

theorem normalizedRadius_frame (p : Vector (d + 1) × Vector (7 - d)) :
    A.normalizedRadius.normalFrame p = A.normalFrame (p.1, A.radiusScale • p.2) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct
