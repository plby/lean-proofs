import Wikipedia.NoExoticSixSphere.SphereProductSuspensionComparison
import Wikipedia.NoExoticSixSphere.LocalSphereCollapse

/-!
# Suspension commutes with the actual framed tube after product quotient

The tube is the original certified framed tube. Adding one real normal
coordinate gives its literal product tube, not an abstract stabilization
class. The exact diagram compares this tube's actual collapse with the
ordinary suspension of the original sphere-valued collapse, with coordinate
order explicitly accounted for by the product homeomorphisms.

No invertibility on homotopy classes is inferred for the meridian quotient.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedTubeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedTubeData a)

theorem product_collapse_suspension (y : Sphere (e.ambientDimension + 1)) :
    OpenFiberCollapse.collapseOnePoint (OpenFiberCollapse.productTube (T := ℝ) d.tube)
      (SuspensionProductComparison.rightQuotient e.ambientDimension y) =
    SuspensionProductComparison.rightQuotient (e.ambientDimension - n)
      (SphereMapSuspension.map d.collapseData.sphereMap y) := by
  rw [OpenFiberCollapse.productTube_collapseOnePoint d.tube d.isOpenEmbedding]
  exact (SuspensionProductComparison.rightQuotient_suspension d.collapseData.map
    d.collapseData.map_infty y).symm

end NoExoticSixSphere.EuclideanEmbedding.FramedTubeData
