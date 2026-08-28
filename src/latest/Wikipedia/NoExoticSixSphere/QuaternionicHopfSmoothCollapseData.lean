import Wikipedia.NoExoticSixSphere.QuaternionicHopfPairedPartialDiffeomorph
import Wikipedia.NoExoticSixSphere.QuaternionicHopfEuclideanCollapseClass
import Wikipedia.NoExoticSixSphere.FramedCollapseFromPartialTube

/-!
# Smooth framed collapse data for the actual Hopf-product representative

The inverse coordinates come from the retained full-source partial
diffeomorphism. Its map is exactly the previously checked Euclidean tube
collapse. Thus the geometric data and the original native class agree.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open SmoothCube SphereComposition

local instance : ChartedSpace (V 6) (Sphere 3 × Sphere 3) := southPairEuclideanAtlas

def southPairFramedPartial :
    PartialDiffeomorph ((𝓡 6).prod 𝓘(ℝ, southPairEuclideanEmbedding.NormalModel))
      (𝓡 southPairEuclideanEmbedding.ambientDimension)
      ((Sphere 3 × Sphere 3) × southPairEuclideanEmbedding.NormalModel)
      (V southPairEuclideanEmbedding.ambientDimension) ∞ := southPairEuclideanPartial

theorem southPairFramedPartial_apply
    (p : (Sphere 3 × Sphere 3) × southPairEuclideanEmbedding.NormalModel) :
    southPairFramedPartial p = southPairEuclideanTube p := by
  simpa only [southPairFramedPartial, southPairEuclideanEmbedding] using
    southPairEuclideanPartial_apply p

theorem southPairFramedPartial_source : southPairFramedPartial.source = Set.univ :=
  southPairEuclideanPartial_source

theorem southPairFramedPartial_core (p : Sphere 3 × Sphere 3) :
    southPairFramedPartial (p, 0) = southPairEuclideanEmbedding.toFun p :=
  (southPairFramedPartial_apply (p, 0)).trans (southPairEuclideanTube_core p)

theorem hasFDerivAt_southPairFramedPartial_normal (p : Sphere 3 × Sphere 3) :
    HasFDerivAt (fun v : southPairEuclideanEmbedding.NormalModel ↦ southPairFramedPartial (p, v))
      (southPairEuclideanNormalFrame.ambient p) 0 := by
  have he : (fun v : southPairEuclideanEmbedding.NormalModel ↦ southPairFramedPartial (p, v)) =
      (fun v : V 10 ↦ southPairEuclideanTube (p, v)) := by
    funext v
    simpa only [southPairEuclideanEmbedding] using southPairFramedPartial_apply (p, v)
  rw [he]
  exact hasFDerivAt_southPairEuclideanTube_normal p

def southPairSmoothCollapseData :
    southPairEuclideanEmbedding.FramedCollapseData southPairEuclideanNormalFrame :=
  southPairEuclideanEmbedding.framedCollapseDataOfPartialTube southPairEuclideanNormalFrame
    southPairFramedPartial southPairFramedPartial_source southPairFramedPartial_core
      hasFDerivAt_southPairFramedPartial_normal

theorem southPairSmoothCollapseData_map (z : OnePoint (V 16)) :
    southPairSmoothCollapseData.map z =
      OpenFiberCollapse.collapseOnePoint southPairEuclideanTube z := by
  have he : (fun p : (Sphere 3 × Sphere 3) × southPairEuclideanEmbedding.NormalModel ↦
      southPairFramedPartial p) = southPairEuclideanTube := funext southPairFramedPartial_apply
  simp only [southPairSmoothCollapseData]
  exact congrArg (fun τ ↦ OpenFiberCollapse.collapseOnePoint τ z) he

theorem southPairSmoothCollapseData_sphereMap :
    southPairSmoothCollapseData.sphereMap = southPairEuclideanCollapseSphereMap := by
  apply ContinuousMap.ext
  intro y
  change euclideanOnePointSphere 10
    (southPairSmoothCollapseData.map ((euclideanOnePointSphere 16).symm y)) = _
  rw [southPairSmoothCollapseData_map]
  rfl

def southPairSmoothCollapseBasedMap : Based 16 10 := by
  refine ⟨southPairSmoothCollapseData.sphereMap, ?_⟩
  rw [southPairSmoothCollapseData_sphereMap]
  exact southPairEuclideanCollapseBasedMap.property

theorem southPairSmoothCollapse_nativeClass :
    sphereClass southPairSmoothCollapseBasedMap = SixthStemSmashSquare.nativeClass := by
  have he : southPairSmoothCollapseBasedMap = southPairEuclideanCollapseBasedMap :=
    Subtype.ext southPairSmoothCollapseData_sphereMap
  rw [he]
  exact southPairEuclideanCollapse_nativeClass

end NoExoticSixSphere.QuaternionicHopf
