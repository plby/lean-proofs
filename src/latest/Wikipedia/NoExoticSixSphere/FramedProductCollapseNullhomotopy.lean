import Wikipedia.NoExoticSixSphere.FramedCollapseProductSuspension
import Wikipedia.NoExoticSixSphere.ProductSphereSuspensionComparison

/-!
# The actual product-tube collapse and the suspended framed collapse

For a certified framed tube of the original manifold, its genuine product
with a real coordinate has nullhomotopic collapse exactly when the literal
suspension of the original collapse is nullhomotopic. No replacement of the
manifold's atlas or normal framing is involved.
-/

noncomputable section

open scoped OnePoint Manifold

namespace NoExoticSixSphere.EuclideanEmbedding.FramedTubeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedTubeData a)

theorem product_collapse_nullhomotopic_iff :
    (SphereMapSuspension.map d.collapseData.sphereMap).Nullhomotopic ↔
      (⟨OpenFiberCollapse.collapseOnePoint (OpenFiberCollapse.productTube (T := ℝ) d.tube),
        OpenFiberCollapse.continuous_collapseOnePoint
          (OpenFiberCollapse.productTube (T := ℝ) d.tube)
          (OpenFiberCollapse.productTube_isOpenEmbedding d.tube d.isOpenEmbedding)⟩ :
        C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension) × ℝ),
          OnePoint (e.NormalModel × ℝ))).Nullhomotopic := by
  have h := SuspensionProductComparison.suspension_nullhomotopic_iff_product
    d.collapseData.map d.collapseData.map_infty
  change (SphereMapSuspension.map d.collapseData.sphereMap).Nullhomotopic ↔ _ at h
  rw [OpenFiberCollapse.productTube_collapseMap d.tube d.isOpenEmbedding]
  exact h

/-- The literal product-tube collapse, written on standard spheres using explicit coordinates. -/
def productSphereCollapse :
    C(Sphere (e.ambientDimension + 1), Sphere ((e.ambientDimension - n) + 1)) :=
  (SuspensionProductComparison.productSphereHomeomorph
    (e.ambientDimension - n)).toHomotopyEquiv.toFun.comp
    ((⟨OpenFiberCollapse.collapseOnePoint (OpenFiberCollapse.productTube (T := ℝ) d.tube),
        OpenFiberCollapse.continuous_collapseOnePoint
          (OpenFiberCollapse.productTube (T := ℝ) d.tube)
          (OpenFiberCollapse.productTube_isOpenEmbedding d.tube d.isOpenEmbedding)⟩ :
        C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension) × ℝ),
          OnePoint (e.NormalModel × ℝ))).comp
      (SuspensionProductComparison.productSphereHomeomorph
        e.ambientDimension).symm.toHomotopyEquiv.toFun)

theorem productSphereCollapse_eq_productSphereMap :
    d.productSphereCollapse = SuspensionProductComparison.productSphereMap
      d.collapseData.map d.collapseData.map_infty := by
  unfold productSphereCollapse
  rw [OpenFiberCollapse.productTube_collapseMap d.tube d.isOpenEmbedding]
  rfl

theorem iterate_product_collapse_nullhomotopic_iff (r : ℕ) :
    (SphereMapSuspension.iterate
      (SphereMapSuspension.map d.collapseData.sphereMap) r).Nullhomotopic ↔
      (SphereMapSuspension.iterate d.productSphereCollapse r).Nullhomotopic := by
  rw [productSphereCollapse_eq_productSphereMap]
  exact SuspensionProductComparison.iterate_suspension_nullhomotopic_iff_product
    d.collapseData.map d.collapseData.map_infty r

end NoExoticSixSphere.EuclideanEmbedding.FramedTubeData
