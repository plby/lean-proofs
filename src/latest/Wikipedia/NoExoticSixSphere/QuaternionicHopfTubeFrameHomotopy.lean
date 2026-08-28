import Wikipedia.NoExoticSixSphere.QuaternionicHopfNormalizedTube
import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubeFiberRotation

/-!
# An actual based tube-collapse homotopy to the raw Hopf normal frame

Every stage reparametrizes the retained original open tube. Its normal
derivative is exactly the checked radial frame at reversed time. The
initial collapse is the original stabilized collapse in the specified
ambient and fixed normal coordinates, including at infinity.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

def southTubeFrameTube (t : I) : Sphere 3 × SouthNormalModel → V 8 :=
  OpenFiberCollapse.coordinateTube southNormalizedTube southTubeFiberHomeomorph t

theorem southTubeFrameTube_apply (t : I) (p : Sphere 3 × SouthNormalModel) :
    southTubeFrameTube t p = southNormalizedTube (p.1, southTubeFiberRotation t p.1 p.2) := by
  simp only [southTubeFrameTube, OpenFiberCollapse.coordinateTube, southTubeFiberHomeomorph,
    ContinuousLinearEquiv.coe_toHomeomorph]

theorem southTubeFrameTube_isOpenEmbedding (t : I) :
    Topology.IsOpenEmbedding (southTubeFrameTube t) :=
  OpenFiberCollapse.isOpenEmbedding_coordinateTube southNormalizedTube southTubeFiberHomeomorph
    southNormalizedTube_isOpenEmbedding continuous_southTubeFiberHomeomorph
    continuous_southTubeFiberHomeomorph_symm t

theorem southTubeFrameTube_core (t : I) (q : Sphere 3) :
    southTubeFrameTube t (q, 0) = (2 : ℝ) • southFiberAmbient q := by
  simpa only [map_zero, southNormalizedTube_zero] using southTubeFrameTube_apply t (q, 0)

theorem southTubeFrameTube_zero : southTubeFrameTube 0 = southNormalizedTube := by
  funext p
  exact (southTubeFrameTube_apply 0 p).trans
    (congrArg (fun v : SouthNormalModel ↦ southNormalizedTube (p.1, v))
      (congrArg (fun L : SouthNormalModel ≃L[ℝ] SouthNormalModel ↦ L p.2)
        (southTubeFiberRotation_zero p.1)))

theorem hasFDerivAt_southTubeFrameTube_normal (t : I) (q : Sphere 3) :
    HasFDerivAt (fun v : SouthNormalModel ↦ southTubeFrameTube t (q, v))
      (southRadialFrame (1 - (t : ℝ)) q) 0 := by
  have ht : HasFDerivAt (fun v : SouthNormalModel ↦ southNormalizedTube (q, v))
      (southRadialFrame 1 q) (southTubeFiberRotation t q 0) := by
    simpa only [map_zero] using hasFDerivAt_southNormalizedTube_normal q
  have h := ht.comp (0 : SouthNormalModel) (southTubeFiberRotation t q).hasFDerivAt
  have he : (southRadialFrame 1 q).comp (southTubeFiberRotation t q).toContinuousLinearMap =
      southRadialFrame (1 - (t : ℝ)) q := by
    apply ContinuousLinearMap.ext
    exact southTubeFiberRotation_frame t q
  rw [he] at h
  have hefun : (fun v : SouthNormalModel ↦ southTubeFrameTube t (q, v)) =
      (fun v : SouthNormalModel ↦ southNormalizedTube (q, southTubeFiberRotation t q v)) := by
    funext v
    simpa only using southTubeFrameTube_apply t (q, v)
  rw [hefun]
  simpa only [Function.comp_def] using h

theorem hasFDerivAt_southTubeFrameTube_one (q : Sphere 3) :
    HasFDerivAt (fun v : SouthNormalModel ↦ southTubeFrameTube 1 (q, v))
      (southNormalFrame.ambient q) 0 := by
  simpa only [Set.Icc.coe_one, sub_self, southRadialFrame_zero] using
    hasFDerivAt_southTubeFrameTube_normal 1 q

def southTubeFrameCollapseAt (t : I) : C(OnePoint (V 8), OnePoint SouthNormalModel) :=
  OpenFiberCollapse.coordinateCollapseMap southNormalizedTube southTubeFiberHomeomorph
    southNormalizedTube_isOpenEmbedding continuous_southTubeFiberHomeomorph
    continuous_southTubeFiberHomeomorph_symm t

def southTubeFrameCollapseHomotopy :
    (southTubeFrameCollapseAt 0).Homotopy (southTubeFrameCollapseAt 1) :=
  OpenFiberCollapse.coordinateCollapseHomotopy southNormalizedTube southTubeFiberHomeomorph
    southNormalizedTube_isOpenEmbedding continuous_southTubeFiberHomeomorph
    continuous_southTubeFiberHomeomorph_symm

theorem southTubeFrameCollapseHomotopy_apply (t : I) (z : OnePoint (V 8)) :
    southTubeFrameCollapseHomotopy (t, z) =
      OpenFiberCollapse.collapseOnePoint (southTubeFrameTube t) z :=
  OpenFiberCollapse.coordinateCollapseFamily_apply southNormalizedTube southTubeFiberHomeomorph
    southNormalizedTube_isOpenEmbedding continuous_southTubeFiberHomeomorph
    continuous_southTubeFiberHomeomorph_symm t z

theorem southTubeFrameCollapseHomotopy_infty (t : I) :
    southTubeFrameCollapseHomotopy (t, OnePoint.infty) = OnePoint.infty := by
  rw [southTubeFrameCollapseHomotopy_apply, OpenFiberCollapse.collapseOnePoint_infty]

theorem southTubeFrameCollapseHomotopy_zero (z : OnePoint (V 8)) :
    southTubeFrameCollapseHomotopy (0, z) =
      southChosenNormalCoordinates.toHomeomorph.onePointCongr
        (OpenFiberCollapse.collapseOnePoint southStabilizedTube z) := by
  rw [southTubeFrameCollapseHomotopy_apply, southTubeFrameTube_zero]
  exact southNormalizedTube_collapse z

end NoExoticSixSphere.QuaternionicHopf
