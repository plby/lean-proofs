import Wikipedia.NoExoticSixSphere.AffineProductCollapseData
import Wikipedia.NoExoticSixSphere.IteratedEuclideanProductSuspension
import Wikipedia.NoExoticSixSphere.FramedCollapseHomotopyComparison

/-!
# Product-stabilized collapse data retain the original finite vanishing criterion

The affine coordinates, normal-coordinate isomorphism, and genuine
Euclidean product are all retained. Exact coordinate squares give the
comparison at every further suspension stage. The old positive radius
normalization is removed using the proved same-frame collapse homotopy.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.AffineProductCollapse

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (V n) M]
  {e e' : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 n) e'.normalProjection e'.NormalModel}
  (d : e.FramedCollapseData a)
  (S : V e'.ambientDimension ≃L[ℝ] (V e.ambientDimension × V q))
  (C : e'.NormalModel ≃L[ℝ] (e.NormalModel × V q)) (b : V e'.ambientDimension)

theorem productMap_coordinate_square (z : OnePoint (V e'.ambientDimension)) :
    (EuclideanFactorProduct.productCoordinates (e.ambientDimension - n) q).onePointCongr
      (C.toHomeomorph.onePointCongr (productMap d S C b z)) =
    EuclideanFactorProduct.compactMap d.normalizedMap d.normalizedMap_infty q
      ((EuclideanFactorProduct.productCoordinates e.ambientDimension q).onePointCongr
        ((ambientCoordinates S b).onePointCongr z)) := by
  change (EuclideanFactorProduct.productCoordinates (e.ambientDimension - n) q).onePointCongr
    (C.toHomeomorph.onePointCongr (C.toHomeomorph.onePointCongr.symm
      (OnePointProduct.addFactor d.normalizedMap d.normalizedMap_infty (V q)
        ((ambientCoordinates S b).onePointCongr z)))) = _
  rw [Homeomorph.apply_symm_apply, EuclideanFactorProduct.compactMap_apply]

variable (he : ∀ x, S (e'.toFun x - b) = (e.toFun x, 0))
  (ha : ∀ x v, S (a'.ambient x v) = (a.ambient x (C v).1, (C v).2))

theorem iterate_collapseData_nullhomotopic_iff_normalized (r : ℕ) :
    (SphereMapSuspension.iterate (collapseData d S C b he ha).sphereMap r).Nullhomotopic ↔
      (SphereMapSuspension.iterate
        (SphereMapSuspension.iterate d.normalized.sphereMap q) r).Nullhomotopic := by
  have h := SphereRepresentative.iterate_nullhomotopic_iff
    (euclideanOnePointSphere e'.ambientDimension)
    (euclideanOnePointSphere (e'.ambientDimension - n))
    (euclideanOnePointSphere (e.ambientDimension + q))
    (euclideanOnePointSphere ((e.ambientDimension - n) + q))
    ((ambientCoordinates S b).onePointCongr.trans
      (EuclideanFactorProduct.productCoordinates e.ambientDimension q).onePointCongr)
    (C.toHomeomorph.onePointCongr.trans
      (EuclideanFactorProduct.productCoordinates (e.ambientDimension - n) q).onePointCongr)
    (productMap d S C b)
    (EuclideanFactorProduct.compactMap d.normalizedMap d.normalizedMap_infty q)
    (productMap_coordinate_square d S C b) r
  exact h.trans (EuclideanFactorProduct.iterate_nullhomotopic_iff_product
    d.normalizedMap d.normalizedMap_infty q r).symm

theorem finite_collapseData_nullhomotopic_iff_normalized :
    (∃ r : ℕ, (SphereMapSuspension.iterate
      (collapseData d S C b he ha).sphereMap r).Nullhomotopic) ↔
    ∃ r : ℕ, (SphereMapSuspension.iterate d.normalized.sphereMap r).Nullhomotopic :=
  (exists_congr (fun r ↦ iterate_collapseData_nullhomotopic_iff_normalized
    d S C b he ha r)).trans
      (SphereMapSuspension.finite_iterate_nullhomotopic_iff d.normalized.sphereMap q)

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [Nonempty M]

theorem finite_collapseData_nullhomotopic_iff :
    (∃ r : ℕ, (SphereMapSuspension.iterate
      (collapseData d S C b he ha).sphereMap r).Nullhomotopic) ↔
    ∃ r : ℕ, (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic :=
  (finite_collapseData_nullhomotopic_iff_normalized d S C b he ha).trans
    (exists_congr (fun r ↦ d.normalized.iterate_sphereMap_nullhomotopic_iff d r))

end NoExoticSixSphere.EuclideanEmbedding.AffineProductCollapse
