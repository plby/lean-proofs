import Wikipedia.NoExoticSixSphere.Definitions
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Euclidean embeddings and normal fibers of smooth sphere candidates

The framed-cobordism approach starts by embedding the candidate in Euclidean
space and considering its normal bundle. Here the embedding is constructed from
compactness using mathlib's Whitney theorem, and the normal fibers are the
actual orthogonal complements of the differential's image.

The tangent-normal splitting below is pointwise. It does not assert that the
normal bundle is trivial or framed, or that the splittings form a bundle map.
-/

open scoped Manifold ContDiff
open Function

namespace NoExoticSixSphere

universe u

/-- A closed smooth Euclidean embedding with injective differential. -/
structure EuclideanEmbedding (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] where
  ambientDimension : ℕ
  toFun : M → EuclideanSpace ℝ (Fin ambientDimension)
  smooth : ContMDiff (𝓡 n) (𝓡 ambientDimension) ∞ toFun
  closedEmbedding : Topology.IsClosedEmbedding toFun
  injective_mfderiv : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 ambientDimension) toFun x)

/-- Every smooth topological sphere admits an actual Euclidean embedding. -/
theorem nonempty_euclideanEmbedding_of_homeomorph {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (h : M ≃ₜ Sphere n) :
    Nonempty (EuclideanEmbedding n M) := by
  let _ := compactSpace_of_homeomorph h
  let _ := t2Space_of_homeomorph h
  obtain ⟨N, e, he, hc, hd⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  exact ⟨⟨N, e, he, hc, hd⟩⟩

namespace EuclideanEmbedding

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (e : EuclideanEmbedding n M)

local instance tangentSpaceT2 (x : M) : T2Space (TangentSpace (𝓡 n) x) :=
  inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin n)))

local instance tangentSpaceFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))

/-- The vector-valued differential remains injective after identifying the ambient
tangent space with the ambient Euclidean space. -/
theorem injective_mvfderiv (x : M) : Injective (mvfderiv (𝓡 n) e.toFun x) :=
  (NormedSpace.fromTangentSpace (e.toFun x)).injective.comp (e.injective_mfderiv x)

/-- The image of the tangent space under the differential of the embedding. -/
noncomputable def tangentImage (x : M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (mvfderiv (𝓡 n) e.toFun x).range

/-- The normal space at an embedded point, as an actual subspace of the ambient space. -/
noncomputable def normalFiber (x : M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.tangentImage x)ᗮ

/-- The differential identifies the tangent space with its image. -/
noncomputable def tangentImageEquiv (x : M) :
    TangentSpace (𝓡 n) x ≃L[ℝ] e.tangentImage x :=
  (LinearEquiv.ofInjective
    (mvfderiv (𝓡 n) e.toFun x).toLinearMap
    (e.injective_mvfderiv x)).toContinuousLinearEquiv

/-- Each tangent image has the manifold's dimension. -/
theorem finrank_tangentImage (x : M) : Module.finrank ℝ (e.tangentImage x) = n := by
  rw [← (e.tangentImageEquiv x).toLinearEquiv.finrank_eq]
  exact finrank_euclideanSpace_fin

/-- The dimension of a normal fiber is the ambient codimension. -/
theorem finrank_tangent_add_normal (x : M) :
    n + Module.finrank ℝ (e.normalFiber x) = e.ambientDimension := by
  change n + Module.finrank ℝ (e.tangentImage x)ᗮ = e.ambientDimension
  calc
    n + Module.finrank ℝ (e.tangentImage x)ᗮ =
        Module.finrank ℝ (e.tangentImage x) + Module.finrank ℝ (e.tangentImage x)ᗮ :=
      congrArg (fun k : ℕ ↦ k + Module.finrank ℝ (e.tangentImage x)ᗮ)
        (e.finrank_tangentImage x).symm
    _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
      (e.tangentImage x).finrank_add_finrank_orthogonal
    _ = e.ambientDimension := finrank_euclideanSpace_fin

/-- The ambient dimension is at least the dimension of the embedded manifold. -/
theorem dimension_le_ambient (x : M) : n ≤ e.ambientDimension := by
  rw [← e.finrank_tangent_add_normal x]
  exact Nat.le_add_right _ _

/-- The tangent and normal spaces together recover the ambient vector space.
This is a pointwise linear result, not a framing of the normal bundle. -/
noncomputable def tangentNormalEquiv (x : M) :
    (TangentSpace (𝓡 n) x × e.normalFiber x) ≃L[ℝ]
      EuclideanSpace ℝ (Fin e.ambientDimension) :=
  ((LinearEquiv.prodCongr (e.tangentImageEquiv x).toLinearEquiv
      (LinearEquiv.refl ℝ (e.normalFiber x))).trans
    ((e.tangentImage x).prodEquivOfIsCompl (e.normalFiber x)
      (e.tangentImage x).isCompl_orthogonal)).toContinuousLinearEquiv

end EuclideanEmbedding

end NoExoticSixSphere
