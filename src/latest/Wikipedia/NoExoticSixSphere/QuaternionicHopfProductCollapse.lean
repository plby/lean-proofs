import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubeClass
import Wikipedia.NoExoticSixSphere.FramedTubeNativeSmash

/-!
# An actual paired stabilized Hopf tube represents the canonical sixth-stem square

This sphere map is defined by collapsing the product of two genuine
stabilized tubes and using the explicit original compactification
coordinates. Its native class is then proved to be the canonical square.
Neither nontriviality nor generation of the sixth stem follows here.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open SmoothCube SphereComposition SuspensionProductComparison

local instance : ChartedSpace (V 3) {x : Sphere 7 // sphereMap x = south} :=
  regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

local instance : IsManifold (𝓡 3) ∞ {x : Sphere 7 // sphereMap x = south} :=
  regularFiber_isManifold sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

local instance : CompactSpace {x : Sphere 7 // sphereMap x = south} :=
  RegularSphereFiber.fiber_compact sphereMap south

def southPairedProductBasedMap : Based 16 10 := southChartTube.pairedProductBasedMap

theorem southPairedProductBasedMap_eq :
    southPairedProductBasedMap =
      SphereSmash.basedSquare (CubicalSphereSuspension.productBasedMap southChartTubeBasedMap) :=
  southChartTube.pairedProductBasedMap_eq southChartTubeBasedMap rfl

theorem southPairedProductBasedMap_formula (z : OnePoint ((V 7 × ℝ) × (V 7 × ℝ))) :
    southPairedProductBasedMap.val (productPairSphereHomeomorph 7 z) =
      productPairSphereHomeomorph 4
        (OpenFiberCollapse.collapseOnePoint southChartTube.pairedProductTube z) := by
  change productPairSphereHomeomorph 4
    (OpenFiberCollapse.collapseOnePoint southChartTube.pairedProductTube
      ((productPairSphereHomeomorph 7).symm (productPairSphereHomeomorph 7 z))) = _
  rw [Homeomorph.symm_apply_apply]

theorem southPairedProduct_nativeClass :
    sphereClass southPairedProductBasedMap = SixthStemSmashSquare.nativeClass := by
  rw [southPairedProductBasedMap_eq]
  exact southChartTube_suspendedSmashClass

theorem southPairedProduct_originalHopfClass :
    sphereClass southPairedProductBasedMap = suspendedSmashClass :=
  southPairedProduct_nativeClass.trans suspendedSmashClass_eq.symm

end NoExoticSixSphere.QuaternionicHopf
