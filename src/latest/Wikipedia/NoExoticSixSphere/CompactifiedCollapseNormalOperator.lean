import Wikipedia.NoExoticSixSphere.CompactifiedCollapseEquationDifferential
import Wikipedia.NoExoticSixSphere.StereographicNormalOperator
import Wikipedia.NoExoticSixSphere.CollapseInducedFrame

/-!
# Compactification retains the prescribed collapse normal operator

The canonical orthogonal right inverse of the genuine compactified
equations is the augmented stereographic differential applied to the
original prescribed frame, with the original tube radius and the exact
factor one-half in the new radial direction.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization StereographicEquator

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)
  (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)))
  (hg : ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) ∞ g)
  (x : M)
  (hgerm : (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
    =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap)

include hg hgerm in
theorem orthogonalRightInverse_compactified_equations (b : Sphere e.ambientDimension)
    (r : ℝ) (z : e.NormalModel) :
    orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart g
      (sphereZero (e.ambientDimension - n))
      (sphereProjectionDiffeomorph (e.ambientDimension - n)) b)
      (e.compactifiedEmbedding x).val) (WithLp.toLp 2 (r, z)) =
      augmentedEquiv e.ambientDimension (e.toFun x) (d.radius • a.ambient x z, r / 2) := by
  rw [← d.orthogonalRightInverse_coordinates_apply x z]
  exact normalOperator_of_augmented_equation_block (e.toFun x) _ _
    (d.surjective_differential _ (d.range_subset ⟨x, rfl⟩))
    (d.fderiv_compactified_equations g hg x hgerm b) r z

include hg hgerm in
theorem orthogonalRightInverse_compactified_equations_apply (b : Sphere e.ambientDimension)
    (r : ℝ) (z : e.NormalModel) :
    orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart g
      (sphereZero (e.ambientDimension - n))
      (sphereProjectionDiffeomorph (e.ambientDimension - n)) b)
      (e.compactifiedEmbedding x).val) (WithLp.toLp 2 (r, z)) =
      fderiv ℝ (finiteAmbient e.ambientDimension) (e.toFun x)
        (d.radius • a.ambient x z) + (r / 2) • (e.compactifiedEmbedding x).val := by
  rw [d.orthogonalRightInverse_compactified_equations g hg x hgerm, augmentedEquiv_apply]
  rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
