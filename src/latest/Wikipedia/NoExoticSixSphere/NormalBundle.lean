import Wikipedia.NoExoticSixSphere.NormalProjection
import Wikipedia.NoExoticSixSphere.ProjectionBundle

/-!
# The smooth normal bundle of a Euclidean embedding

The fibers here are the ranges of the orthogonal normal projections, with a
canonical identification with the orthogonal complements of the tangent images.
The topology and smooth vector-bundle structure come from the explicit local
projection transport. This construction does not assert that the bundle is
trivial or stably trivial.
-/

open scoped Manifold ContDiff Bundle
open Bundle

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (e : EuclideanEmbedding n M)

/-- Normal vectors at an embedded point, represented in the ambient Euclidean space. -/
abbrev NormalSpace (x : M) := ↥(e.normalProjection x).range

/-- The fixed Euclidean model of dimension equal to the embedding's codimension. -/
abbrev NormalModel := EuclideanSpace ℝ (Fin (e.ambientDimension - n))

/-- The normal-bundle fibers are canonically the orthogonal normal fibers. -/
noncomputable def normalSpaceEquiv (x : M) : e.NormalSpace x ≃L[ℝ] e.normalFiber x :=
  ContinuousLinearEquiv.ofEq _ _ (e.range_normalProjection x)

/-- Every normal-bundle fiber has the expected codimension. -/
theorem finrank_normalSpace (x : M) :
    Module.finrank ℝ (e.NormalSpace x) = e.ambientDimension - n := by
  have h := e.finrank_tangent_add_normal x
  rw [(e.normalSpaceEquiv x).toLinearEquiv.finrank_eq]
  omega

/-- A model-space identification at a chart center; no global smooth choice is assumed. -/
noncomputable def normalModelEquiv (x : M) : e.NormalSpace x ≃L[ℝ] e.NormalModel :=
  (LinearEquiv.ofFinrankEq (e.NormalSpace x) e.NormalModel (by
    rw [e.finrank_normalSpace x]
    exact finrank_euclideanSpace_fin.symm)).toContinuousLinearEquiv

variable [IsManifold (𝓡 n) ∞ M]

/-- The local normal-coordinate charts and their compatible linear transitions. -/
noncomputable def normalPrebundle : VectorPrebundle ℝ e.NormalModel e.NormalSpace :=
  ProjectionBundle.vectorPrebundle e.normalProjection e.normalProjection_idempotent
    e.normalModelEquiv e.contMDiff_normalProjection

/-- The normal prebundle has smooth transition functions. -/
instance normalPrebundle_isContMDiff : e.normalPrebundle.IsContMDiff (𝓡 n) ∞ :=
  ProjectionBundle.vectorPrebundle_isContMDiff e.normalProjection
    e.normalProjection_idempotent e.normalModelEquiv e.contMDiff_normalProjection

/-- The total space of the actual normal vector bundle. -/
abbrev NormalBundle := TotalSpace e.NormalModel e.NormalSpace

/-- Topology on the normal bundle supplied by its local normal-coordinate charts. -/
noncomputable instance normalBundleTopology : TopologicalSpace e.NormalBundle :=
  e.normalPrebundle.totalSpaceTopology

/-- The normal bundle is locally a product with the Euclidean codimension model. -/
noncomputable instance normalFiberBundle : FiberBundle e.NormalModel e.NormalSpace :=
  e.normalPrebundle.toFiberBundle

/-- The local normal-bundle trivializations are linear on fibers. -/
instance normalVectorBundle : VectorBundle ℝ e.NormalModel e.NormalSpace :=
  e.normalPrebundle.toVectorBundle

/-- The normal bundle is a genuine smooth vector bundle. -/
instance normalContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ e.NormalModel e.NormalSpace (𝓡 n) :=
  e.normalPrebundle.contMDiffVectorBundle (𝓡 n)

end NoExoticSixSphere.EuclideanEmbedding
