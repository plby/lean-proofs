import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubeNormalCoordinates
import Wikipedia.NoExoticSixSphere.CollapseFiberEquiv

/-!
# Normalizing the actual stabilized tube in the computed normal model

Reindex the original tube by the inverse of its fixed, radius-dependent
normal-coordinate map. Its normal derivative is exactly the endpoint
frame. The corresponding target compactification change is retained.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

local instance : ChartedSpace (V 3) {x : Sphere 7 // sphereMap x = south} :=
  regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

def southChosenNormalCoordinates : (V 4 × ℝ) ≃L[ℝ] SouthNormalModel :=
  southNormalCoordinates southChartTube.radius southChartTube.radius_pos.ne'

def southNormalizedTube (p : Sphere 3 × SouthNormalModel) : V 8 :=
  southStabilizedTube (p.1, southChosenNormalCoordinates.symm p.2)

theorem southNormalizedTube_isOpenEmbedding : Topology.IsOpenEmbedding southNormalizedTube := by
  let e := (Homeomorph.refl (Sphere 3)).prodCongr southChosenNormalCoordinates.symm.toHomeomorph
  exact southStabilizedTube_isOpenEmbedding.comp e.isOpenEmbedding

theorem southNormalizedTube_zero (q : Sphere 3) :
    southNormalizedTube (q, 0) = (2 : ℝ) • southFiberAmbient q := by
  change southStabilizedTube (q, southChosenNormalCoordinates.symm 0) = _
  rw [map_zero, southStabilizedTube_zero]

theorem hasFDerivAt_southNormalizedTube_normal (q : Sphere 3) :
    HasFDerivAt (fun v : SouthNormalModel ↦ southNormalizedTube (q, v))
      (southRadialFrame 1 q) 0 := by
  have ht : HasFDerivAt (fun p : V 4 × ℝ ↦ southStabilizedTube (q, p))
      ((southRadialFrame 1 q).comp southChosenNormalCoordinates.toContinuousLinearMap)
        (southChosenNormalCoordinates.symm (0 : SouthNormalModel)) := by
    simpa only [map_zero, southChosenNormalCoordinates] using
      hasFDerivAt_southStabilizedTube_normal q
  have h := ht.comp (0 : SouthNormalModel) southChosenNormalCoordinates.symm.hasFDerivAt
  have he : ((southRadialFrame 1 q).comp southChosenNormalCoordinates.toContinuousLinearMap).comp
      southChosenNormalCoordinates.symm.toContinuousLinearMap = southRadialFrame 1 q := by
    apply ContinuousLinearMap.ext
    intro v
    change southRadialFrame 1 q (southChosenNormalCoordinates
      (southChosenNormalCoordinates.symm v)) = southRadialFrame 1 q v
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [he] at h
  exact h

theorem southNormalizedTube_collapse (z : OnePoint (V 8)) :
    OpenFiberCollapse.collapseOnePoint southNormalizedTube z =
      southChosenNormalCoordinates.toHomeomorph.onePointCongr
        (OpenFiberCollapse.collapseOnePoint southStabilizedTube z) :=
  OpenFiberCollapse.collapseOnePoint_fiberEquiv southStabilizedTube
    southChosenNormalCoordinates.symm.toEquiv southStabilizedTube_isOpenEmbedding.injective z

end NoExoticSixSphere.QuaternionicHopf
