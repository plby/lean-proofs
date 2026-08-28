import Wikipedia.NoExoticSixSphere.StabilizedPairSphereCoordinates
import Wikipedia.NoExoticSixSphere.PairedTubeCollapse
import Wikipedia.NoExoticSixSphere.FramedCollapseProductSuspension
import Wikipedia.NoExoticSixSphere.CubicalSuspensionProductMap
import Wikipedia.NoExoticSixSphere.SphereSmashSquare

/-!
# The original suspended smash is the actual paired stabilized-tube collapse

The chosen tube, both added real normal coordinates, and the original
source and target compactification orderings are retained. The resulting
sphere-map equality is proved on the whole compactification.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedTubeData

open SphereComposition SuspensionProductComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedTubeData a)

local notation "E" => EuclideanSpace ℝ (Fin e.ambientDimension)

theorem compactMap_of_sphereMap (B : Based e.ambientDimension (e.ambientDimension - n))
    (hB : B.val = d.collapseData.sphereMap) :
    CubicalSphereSuspension.compactMap B = d.collapseData.map := by
  apply ContinuousMap.ext
  intro z
  change (euclideanOnePointSphere (e.ambientDimension - n)).symm
    (B.val (euclideanOnePointSphere e.ambientDimension z)) = d.collapseData.map z
  rw [hB]
  change (euclideanOnePointSphere (e.ambientDimension - n)).symm
    (euclideanOnePointSphere (e.ambientDimension - n)
      (d.collapseData.map ((euclideanOnePointSphere e.ambientDimension).symm
        (euclideanOnePointSphere e.ambientDimension z)))) = d.collapseData.map z
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

theorem productBasedMap_collapse (B : Based e.ambientDimension (e.ambientDimension - n))
    (hB : B.val = d.collapseData.sphereMap) (z : OnePoint (E × ℝ)) :
    (CubicalSphereSuspension.productBasedMap B).val (productSphereHomeomorph e.ambientDimension z) =
      productSphereHomeomorph (e.ambientDimension - n)
        (OpenFiberCollapse.collapseOnePoint (OpenFiberCollapse.productTube d.tube) z) := by
  change productSphereHomeomorph (e.ambientDimension - n)
    (OnePointProduct.productMap (CubicalSphereSuspension.compactMap B)
      (ContinuousMap.id (OnePoint ℝ)) (CubicalSphereSuspension.compactMap_infty B) rfl
      ((productSphereHomeomorph e.ambientDimension).symm
        (productSphereHomeomorph e.ambientDimension z))) = _
  rw [Homeomorph.symm_apply_apply,
    OpenFiberCollapse.productTube_collapseOnePoint d.tube d.isOpenEmbedding]
  congr 1
  simp only [d.compactMap_of_sphereMap B hB]
  rfl

def pairedProductTube : (M × M) × ((e.NormalModel × ℝ) × (e.NormalModel × ℝ)) →
    (E × ℝ) × (E × ℝ) :=
  OpenFiberCollapse.pairedTube (OpenFiberCollapse.productTube d.tube)
    (OpenFiberCollapse.productTube d.tube)

omit [CompactSpace M] in
theorem pairedProductTube_isOpenEmbedding : Topology.IsOpenEmbedding d.pairedProductTube :=
  OpenFiberCollapse.pairedTube_isOpenEmbedding _ _
    (OpenFiberCollapse.productTube_isOpenEmbedding d.tube d.isOpenEmbedding)
    (OpenFiberCollapse.productTube_isOpenEmbedding d.tube d.isOpenEmbedding)

def pairedProductSphereMap :
    C(Sphere ((e.ambientDimension + 1) + (e.ambientDimension + 1)),
      Sphere ((e.ambientDimension - n + 1) + (e.ambientDimension - n + 1))) :=
  (productPairSphereHomeomorph (e.ambientDimension - n) : C(_, _)).comp
    ((⟨OpenFiberCollapse.collapseOnePoint d.pairedProductTube,
      OpenFiberCollapse.continuous_collapseOnePoint _ d.pairedProductTube_isOpenEmbedding⟩ :
        C(OnePoint ((E × ℝ) × (E × ℝ)),
          OnePoint ((e.NormalModel × ℝ) × (e.NormalModel × ℝ)))).comp
      ((productPairSphereHomeomorph e.ambientDimension).symm : C(_, _)))

theorem pairedProductSphereMap_pole :
    d.pairedProductSphereMap (spherePole ((e.ambientDimension + 1) + (e.ambientDimension + 1))) =
      spherePole ((e.ambientDimension - n + 1) + (e.ambientDimension - n + 1)) := by
  change productPairSphereHomeomorph (e.ambientDimension - n)
    (OpenFiberCollapse.collapseOnePoint d.pairedProductTube
      ((productPairSphereHomeomorph e.ambientDimension).symm
        (spherePole ((e.ambientDimension + 1) + (e.ambientDimension + 1))))) = _
  rw [← productPairSphereHomeomorph_infty e.ambientDimension, Homeomorph.symm_apply_apply,
    OpenFiberCollapse.collapseOnePoint_infty, productPairSphereHomeomorph_infty]

def pairedProductBasedMap : Based ((e.ambientDimension + 1) + (e.ambientDimension + 1))
    ((e.ambientDimension - n + 1) + (e.ambientDimension - n + 1)) :=
  ⟨d.pairedProductSphereMap, d.pairedProductSphereMap_pole⟩

theorem pairedProductSphereMap_eq (B : Based e.ambientDimension (e.ambientDimension - n))
    (hB : B.val = d.collapseData.sphereMap) :
    d.pairedProductSphereMap =
      SphereSmash.squareMap (CubicalSphereSuspension.productBasedMap B) := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨z, rfl⟩ := (productPairSphereHomeomorph e.ambientDimension).surjective y
  obtain ⟨⟨u, v⟩, rfl⟩ := OnePointProduct.map_surjective z
  change productPairSphereHomeomorph (e.ambientDimension - n)
    (OpenFiberCollapse.collapseOnePoint
      (OpenFiberCollapse.pairedTube (OpenFiberCollapse.productTube d.tube)
        (OpenFiberCollapse.productTube d.tube))
      ((productPairSphereHomeomorph e.ambientDimension).symm
        (productPairSphereHomeomorph e.ambientDimension (OnePointProduct.map (u, v))))) = _
  rw [Homeomorph.symm_apply_apply, OpenFiberCollapse.pairedTube_collapseOnePoint _ _
    (OpenFiberCollapse.productTube_isOpenEmbedding d.tube d.isOpenEmbedding)
    (OpenFiberCollapse.productTube_isOpenEmbedding d.tube d.isOpenEmbedding),
    OnePointProduct.productMap_apply]
  change productPairSphereHomeomorph (e.ambientDimension - n)
    (OnePointProduct.map
      (OpenFiberCollapse.collapseOnePoint (OpenFiberCollapse.productTube d.tube) u,
        OpenFiberCollapse.collapseOnePoint (OpenFiberCollapse.productTube d.tube) v)) = _
  rw [productPairSphereHomeomorph_map, productPairSphereHomeomorph_map,
    SphereSmash.squareMap_pairing, d.productBasedMap_collapse B hB u,
    d.productBasedMap_collapse B hB v]

theorem pairedProductBasedMap_eq (B : Based e.ambientDimension (e.ambientDimension - n))
    (hB : B.val = d.collapseData.sphereMap) :
    d.pairedProductBasedMap = SphereSmash.basedSquare (CubicalSphereSuspension.productBasedMap B) :=
  Subtype.ext (d.pairedProductSphereMap_eq B hB)

end NoExoticSixSphere.EuclideanEmbedding.FramedTubeData
