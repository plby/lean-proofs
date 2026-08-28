import Wikipedia.NoExoticSixSphere.StereographicFiberTubeCollapse
import Wikipedia.NoExoticSixSphere.QuaternionicHopfUnitCoordinate
import Wikipedia.NoExoticSixSphere.QuaternionicHopfOriginalNormalFrame
import Wikipedia.NoExoticSixSphere.SphereBasedHomotopyComparison

/-!
# The actual canonical south-fiber tube represents the original Hopf class

The embedding is the stereographic image of the original regular fiber,
with its original regular-fiber atlas and induced equation frame. Its
certified chosen tube has a collapse homotopic to the literal polynomial
Hopf map. The comparison retains the native based class and hence the
original suspended smash-square class.

Comparison of this stereographic frame with the previously computed raw
ambient product frame remains a separate geometric obligation.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.QuaternionicHopf

open SmoothCube SphereComposition

theorem neg_south : -south = spherePole 4 := by
  apply Subtype.ext
  exact neg_neg (spherePole 4).val

theorem pole_maps_antipode_south : sphereMap (spherePole 7) = -south :=
  sphereMap_pole.trans neg_south.symm

local instance southChartedSpace :
    ChartedSpace (V 3) {x : Sphere 7 // sphereMap x = south} :=
  regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

local instance southIsManifold :
    IsManifold (𝓡 3) ∞ {x : Sphere 7 // sphereMap x = south} :=
  regularFiber_isManifold sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

local instance southCompactSpace : CompactSpace {x : Sphere 7 // sphereMap x = south} :=
  RegularSphereFiber.fiber_compact sphereMap south

local instance southNonempty : Nonempty {x : Sphere 7 // sphereMap x = south} :=
  ⟨⟨southFiberPoint (spherePole 3), sphereMap_southFiberPoint (spherePole 3)⟩⟩

def southChartEmbedding : EuclideanEmbedding 3 {x : Sphere 7 // sphereMap x = south} :=
  StereographicFiber.embedding (k := 3) sphereMap contMDiff_sphereMap south south_regular
    (spherePole 7) pole_maps_antipode_south

def southChartFrame : SmoothRangeFrame (𝓡 3) southChartEmbedding.normalProjection
    southChartEmbedding.NormalModel :=
  StereographicFiber.frame (k := 3) sphereMap contMDiff_sphereMap south south_regular
    (spherePole 7) pole_maps_antipode_south

def southChartTube : southChartEmbedding.FramedTubeData southChartFrame :=
  southChartEmbedding.framedTubeData southChartFrame

def southChartEquationsCollapse : southChartEmbedding.FramedCollapseData southChartFrame :=
  StereographicFiber.collapseData (k := 3) sphereMap contMDiff_sphereMap south south_regular
    (spherePole 7) pole_maps_antipode_south

def southChartTubeSphereMap : C(Sphere 7, Sphere 4) := southChartTube.collapseData.sphereMap

def southChartEquationsSphereMap : C(Sphere 7, Sphere 4) := southChartEquationsCollapse.sphereMap

theorem southChartEquationsCollapse_sphereMap :
    southChartEquationsSphereMap = sphereMap := by
  apply ContinuousMap.ext
  intro y
  change euclideanOnePointSphere 4
    ((StereographicFiber.normalCoordinates 4 3).symm.toHomeomorph.onePointCongr
      ((SpherePoleCompactification.homeomorph (-south)).symm
        (sphereMap (SpherePoleCompactification.homeomorph (spherePole 7)
          ((euclideanOnePointSphere 7).symm y))))) = sphereMap y
  rw [neg_south]
  have hQ (z : OnePoint (V 4)) :
      (StereographicFiber.normalCoordinates 4 3).symm.toHomeomorph.onePointCongr z = z := by
    induction z using OnePoint.rec <;> rfl
  rw [hQ]
  change euclideanOnePointSphere 4 ((euclideanOnePointSphere 4).symm
    (sphereMap (euclideanOnePointSphere 7 ((euclideanOnePointSphere 7).symm y)))) = sphereMap y
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem southChartTube_sphereMap_homotopic :
    southChartTubeSphereMap.Homotopic sphereMap := by
  have h : southChartTubeSphereMap.Homotopic southChartEquationsSphereMap :=
    southChartTube.collapseData.sphereMap_homotopic southChartEquationsCollapse
  obtain ⟨H⟩ := h
  exact ⟨H.cast rfl southChartEquationsCollapse_sphereMap⟩

def southChartTubeBasedMap : Based 7 4 := by
  refine ⟨southChartTubeSphereMap, ?_⟩
  have h : southChartTubeSphereMap (euclideanOnePointSphere 7 OnePoint.infty) =
      euclideanOnePointSphere 4 OnePoint.infty := southChartTube.collapseData.sphereMap_infty
  simpa only [euclideanOnePointSphere_infty] using h

theorem southChartTube_nativeClass : sphereClass southChartTubeBasedMap = nativeClass := by
  apply (sphereClass_eq_iff (by decide : 0 < 7) southChartTubeBasedMap basedMap).mpr
  apply (sphere_homotopicRel_point_iff (spherePole 7)
    (southChartTubeBasedMap.property.trans basedMap.property.symm)).mpr
  exact southChartTube_sphereMap_homotopic

theorem southChartTube_hopfCoordinate :
    (OriginalHopfSixthSquare.hopfCoordinate (sphereClass southChartTubeBasedMap)).natAbs = 1 := by
  rw [southChartTube_nativeClass]
  exact hopfNumber_natAbs

theorem southChartTube_suspendedSmashClass :
    sphereClass (SphereSmash.basedSquare
      (CubicalSphereSuspension.productBasedMap southChartTubeBasedMap)) =
        SixthStemSmashSquare.nativeClass :=
  OriginalHopfSixthSquare.sphereClass_square southChartTubeBasedMap southChartTube_hopfCoordinate

end NoExoticSixSphere.QuaternionicHopf
