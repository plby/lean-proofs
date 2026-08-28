import Wikipedia.NoExoticSixSphere.QuaternionicHopfPairedCollapseCoordinates

/-!
# The actual raw-frame endpoint collapse has the original sixth-stem class

The sphere map is defined from the endpoint of the actual paired tube
homotopy, using the retained ambient and target homeomorphisms. The initial
map is proved equal to the original paired Hopf collapse. This proves a
class comparison, not nontriviality, generation, or an Arf value.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

open SmoothCube SphereComposition

def southPairedFrameSphereFamily : C(I × Sphere 16, Sphere 10) :=
  (southPairedTargetSphereHomeomorph : C(_, _)).comp
    (southPairedCollapseFamily.comp ((ContinuousMap.id I).prodMap
      ((StereographicEquator.stabilizedPairSphereHomeomorph 7).symm : C(_, _))))

theorem southPairedFrameSphereFamily_apply (t : I) (z : OnePoint SouthPairAmbientModel) :
    southPairedFrameSphereFamily (t, StereographicEquator.stabilizedPairSphereHomeomorph 7 z) =
      southPairedTargetSphereHomeomorph (southPairedCollapseHomotopy (t, z)) := by
  change southPairedTargetSphereHomeomorph (southPairedCollapseHomotopy
    (t, (StereographicEquator.stabilizedPairSphereHomeomorph 7).symm
      (StereographicEquator.stabilizedPairSphereHomeomorph 7 z))) = _
  rw [Homeomorph.symm_apply_apply]

theorem southPairedFrameSphereFamily_zero (y : Sphere 16) :
    southPairedFrameSphereFamily (0, y) = southPairedProductBasedMap.val y := by
  obtain ⟨z, rfl⟩ := (StereographicEquator.stabilizedPairSphereHomeomorph 7).surjective y
  rw [southPairedFrameSphereFamily_apply]
  exact southPairedCollapseHomotopy_zero_original z

theorem southPairedFrameSphereFamily_pole (t : I) :
    southPairedFrameSphereFamily (t, spherePole 16) = spherePole 10 := by
  rw [← southPairedSourceSphereHomeomorph_infty, southPairedFrameSphereFamily_apply,
    southPairedCollapseHomotopy_infty, southPairedTargetSphereHomeomorph_infty]

def southPairedRawSphereMap : C(Sphere 16, Sphere 10) :=
  southPairedFrameSphereFamily.comp ((ContinuousMap.const _ (1 : I)).prodMk (ContinuousMap.id _))

theorem southPairedRawSphereMap_formula (z : OnePoint SouthPairAmbientModel) :
    southPairedRawSphereMap (StereographicEquator.stabilizedPairSphereHomeomorph 7 z) =
      southPairedTargetSphereHomeomorph
        (OpenFiberCollapse.collapseOnePoint (southPairedFrameTube 1) z) := by
  change southPairedFrameSphereFamily
    (1, StereographicEquator.stabilizedPairSphereHomeomorph 7 z) = _
  rw [southPairedFrameSphereFamily_apply, southPairedCollapseHomotopy_apply]

theorem southPairedRawSphereMap_pole : southPairedRawSphereMap (spherePole 16) = spherePole 10 :=
  southPairedFrameSphereFamily_pole 1

def southPairedRawSphereHomotopy :
    southPairedProductBasedMap.val.Homotopy southPairedRawSphereMap where
  toContinuousMap := southPairedFrameSphereFamily
  map_zero_left := southPairedFrameSphereFamily_zero
  map_one_left _ := rfl

theorem southPairedRawSphereHomotopy_pole (t : I) :
    southPairedRawSphereHomotopy (t, spherePole 16) = spherePole 10 :=
  southPairedFrameSphereFamily_pole t

def southPairedRawBasedMap : Based 16 10 := ⟨southPairedRawSphereMap, southPairedRawSphereMap_pole⟩

theorem southPairedRawBasedMap_originalClass :
    sphereClass southPairedRawBasedMap = sphereClass southPairedProductBasedMap := by
  apply (sphereClass_eq_iff (by decide : 0 < 16)
    southPairedRawBasedMap southPairedProductBasedMap).mpr
  apply (sphere_homotopicRel_point_iff (spherePole 16)
    (southPairedRawBasedMap.property.trans southPairedProductBasedMap.property.symm)).mpr
  exact ⟨southPairedRawSphereHomotopy.symm⟩

theorem southPairedRawBasedMap_nativeClass :
    sphereClass southPairedRawBasedMap = SixthStemSmashSquare.nativeClass :=
  southPairedRawBasedMap_originalClass.trans southPairedProduct_nativeClass

theorem southPairedRawBasedMap_originalHopfClass :
    sphereClass southPairedRawBasedMap = suspendedSmashClass :=
  southPairedRawBasedMap_originalClass.trans southPairedProduct_originalHopfClass

end NoExoticSixSphere.QuaternionicHopf
