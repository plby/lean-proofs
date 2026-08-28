import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Euclidean embeddings retaining the original manifold model

Compactness supplies a genuine closed smooth Euclidean embedding with injective
native derivatives. No change of atlas or inner-product norm on the original
model is assumed. Tangent images are the ranges of the actual derivatives.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- A Euclidean embedding expressed using the given normed model and smooth atlas. -/
structure NativeEuclideanEmbedding where
  ambientDimension : ℕ
  toFun : M → EuclideanSpace ℝ (Fin ambientDimension)
  smooth : ContMDiff 𝓘(ℝ, E) (𝓡 ambientDimension) ∞ toFun
  closedEmbedding : Topology.IsClosedEmbedding toFun
  injective_mfderiv : ∀ x, Injective (mfderiv 𝓘(ℝ, E) (𝓡 ambientDimension) toFun x)

variable {E M}

/-- Compact smooth manifolds embed without any homotopy or homeomorphism assumption. -/
theorem nonempty_nativeEuclideanEmbedding [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    Nonempty (NativeEuclideanEmbedding E M) := by
  obtain ⟨n, f, hs, hc, hd⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  exact ⟨⟨n, f, hs, hc, hd⟩⟩

namespace NativeEuclideanEmbedding

variable (e : NativeEuclideanEmbedding E M)

/-- Vector-valued differentiation has the same injectivity as the native derivative. -/
theorem injective_mvfderiv (x : M) : Injective (mvfderiv 𝓘(ℝ, E) e.toFun x) :=
  (NormedSpace.fromTangentSpace (e.toFun x)).injective.comp (e.injective_mfderiv x)

/-- The embedded tangent space, not a prescribed auxiliary subspace. -/
def tangentImage (x : M) : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (mvfderiv 𝓘(ℝ, E) e.toFun x).range

/-- The dimension of the embedded tangent image is that of the original model. -/
theorem finrank_tangentImage (x : M) : finrank ℝ (e.tangentImage x) = finrank ℝ E := by
  exact LinearMap.finrank_range_of_inj (e.injective_mvfderiv x)

end NativeEuclideanEmbedding

end Wikipedia.SmoothSixDPoincare
