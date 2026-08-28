import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubeFrameHomotopy
import Wikipedia.NoExoticSixSphere.HilbertPairedTubeCollapse
import Wikipedia.NoExoticSixSphere.OnePointProductHomotopy

/-!
# The actual paired Hopf tube-collapse homotopy

Both ambient and normal products carry their L2 coordinates. Every time
slice is exactly the collapse of the paired open tube. At the final time,
the normal derivative is the computed raw quaternionic product frame.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

def southTubePairAmbientCoordinates : (V 8 × V 8) ≃ₜ SouthPairAmbientModel :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.toHomeomorph

def southTubePairNormalCoordinates :
    (SouthNormalModel × SouthNormalModel) ≃ₜ SouthPairNormalModel :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ SouthNormalModel SouthNormalModel).symm.toHomeomorph

def southPairedFrameTube (t : I) :
    (Sphere 3 × Sphere 3) × SouthPairNormalModel → SouthPairAmbientModel :=
  OpenFiberCollapse.hilbertPairedTube (southTubeFrameTube t) (southTubeFrameTube t)

theorem southPairedFrameTube_apply (t : I)
    (p : (Sphere 3 × Sphere 3) × SouthPairNormalModel) :
    southPairedFrameTube t p = WithLp.toLp 2
      (southTubeFrameTube t (p.1.1, p.2.fst), southTubeFrameTube t (p.1.2, p.2.snd)) := rfl

theorem southPairedFrameTube_isOpenEmbedding (t : I) :
    Topology.IsOpenEmbedding (southPairedFrameTube t) :=
  OpenFiberCollapse.hilbertPairedTube_isOpenEmbedding _ _
    (southTubeFrameTube_isOpenEmbedding t) (southTubeFrameTube_isOpenEmbedding t)

theorem southPairedFrameTube_core (t : I) (p : Sphere 3 × Sphere 3) :
    southPairedFrameTube t (p, 0) = (2 : ℝ) • southPairAmbient p := by
  change WithLp.toLp 2 (southTubeFrameTube t (p.1, 0), southTubeFrameTube t (p.2, 0)) = _
  rw [southTubeFrameTube_core, southTubeFrameTube_core]
  rfl

theorem hasFDerivAt_southPairedFrameTube_normal (t : I) (p : Sphere 3 × Sphere 3) :
    HasFDerivAt (fun v : SouthPairNormalModel ↦ southPairedFrameTube t (p, v))
      (southPairRadialFrame (1 - (t : ℝ)) p) 0 := by
  have h := HilbertProduct.hasFDerivAt_equations (x := (0 : SouthPairNormalModel))
    (hasFDerivAt_southTubeFrameTube_normal t p.1)
    (hasFDerivAt_southTubeFrameTube_normal t p.2)
  exact h

theorem hasFDerivAt_southPairedFrameTube_one (p : Sphere 3 × Sphere 3) :
    HasFDerivAt (fun v : SouthPairNormalModel ↦ southPairedFrameTube 1 (p, v))
      (southPairNormalFrame.ambient p) 0 := by
  simpa only [Set.Icc.coe_one, sub_self, southPairRadialFrame_zero] using
    hasFDerivAt_southPairedFrameTube_normal 1 p

def southPairedCollapseFamily :
    C(I × OnePoint SouthPairAmbientModel, OnePoint SouthPairNormalModel) :=
  (southTubePairNormalCoordinates.onePointCongr : C(_, _)).comp
    ((OnePointProduct.homotopyMap southTubeFrameCollapseHomotopy southTubeFrameCollapseHomotopy
      southTubeFrameCollapseHomotopy_infty southTubeFrameCollapseHomotopy_infty).comp
        ((ContinuousMap.id I).prodMap
          (southTubePairAmbientCoordinates.symm.onePointCongr : C(_, _))))

theorem southPairedCollapseFamily_map (t : I) (u v : OnePoint (V 8)) :
    southPairedCollapseFamily
        (t, southTubePairAmbientCoordinates.onePointCongr (OnePointProduct.map (u, v))) =
      southTubePairNormalCoordinates.onePointCongr
        (OnePointProduct.map (OpenFiberCollapse.collapseOnePoint (southTubeFrameTube t) u,
          OpenFiberCollapse.collapseOnePoint (southTubeFrameTube t) v)) := by
  change southTubePairNormalCoordinates.onePointCongr
    (OnePointProduct.homotopyMap southTubeFrameCollapseHomotopy southTubeFrameCollapseHomotopy
      southTubeFrameCollapseHomotopy_infty southTubeFrameCollapseHomotopy_infty
        (t, southTubePairAmbientCoordinates.symm.onePointCongr
          (southTubePairAmbientCoordinates.onePointCongr (OnePointProduct.map (u, v))))) = _
  have he : southTubePairAmbientCoordinates.symm.onePointCongr =
      southTubePairAmbientCoordinates.onePointCongr.symm := rfl
  rw [he, Homeomorph.symm_apply_apply, OnePointProduct.homotopyMap_apply,
    southTubeFrameCollapseHomotopy_apply, southTubeFrameCollapseHomotopy_apply]

theorem southPairedCollapseFamily_apply (t : I) (z : OnePoint SouthPairAmbientModel) :
    southPairedCollapseFamily (t, z) =
      OpenFiberCollapse.collapseOnePoint (southPairedFrameTube t) z := by
  obtain ⟨w, rfl⟩ := southTubePairAmbientCoordinates.onePointCongr.surjective z
  obtain ⟨⟨u, v⟩, rfl⟩ := OnePointProduct.map_surjective w
  rw [southPairedCollapseFamily_map]
  exact (OpenFiberCollapse.hilbertPairedTube_collapse_map _ _
    (southTubeFrameTube_isOpenEmbedding t) (southTubeFrameTube_isOpenEmbedding t) u v).symm

def southPairedCollapseAt (t : I) :
    C(OnePoint SouthPairAmbientModel, OnePoint SouthPairNormalModel) :=
  southPairedCollapseFamily.comp ((ContinuousMap.const _ t).prodMk (ContinuousMap.id _))

def southPairedCollapseHomotopy : (southPairedCollapseAt 0).Homotopy (southPairedCollapseAt 1) where
  toContinuousMap := southPairedCollapseFamily
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem southPairedCollapseHomotopy_apply (t : I) (z : OnePoint SouthPairAmbientModel) :
    southPairedCollapseHomotopy (t, z) =
      OpenFiberCollapse.collapseOnePoint (southPairedFrameTube t) z :=
  southPairedCollapseFamily_apply t z

theorem southPairedCollapseHomotopy_infty (t : I) :
    southPairedCollapseHomotopy (t, OnePoint.infty) = OnePoint.infty := by
  rw [southPairedCollapseHomotopy_apply, OpenFiberCollapse.collapseOnePoint_infty]

end NoExoticSixSphere.QuaternionicHopf
