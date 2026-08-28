import Wikipedia.SmoothSixDPoincare.NativeTangentProjection

/-!
# The actual normal projection of the native Euclidean embedding

The normal fibers are the orthogonal complements of the actual tangent images.
Their projections are smooth on the original manifold. The tangent and normal
spaces together give an explicit continuous linear splitting of ambient space.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] (e : NativeEuclideanEmbedding E M)

/-- The true normal fiber of the Euclidean embedding. -/
def normalFiber (x : M) : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.tangentImage x)ᗮ

/-- Orthogonal projection onto the actual normal fiber. -/
def normalProjection (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
      EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.normalFiber x).starProjection

theorem normalProjection_eq (x : M) : e.normalProjection x = 1 - e.tangentProjection x :=
  Submodule.starProjection_orthogonal' (e.tangentImage x)

theorem range_normalProjection (x : M) : (e.normalProjection x).range = e.normalFiber x :=
  (e.normalFiber x).range_starProjection

theorem normalProjection_idempotent (x : M) : IsIdempotentElem (e.normalProjection x) :=
  (e.normalFiber x).isIdempotentElem_starProjection

/-- The normal fiber has the actual embedding codimension. -/
theorem finrank_tangent_add_normal (x : M) :
    finrank ℝ E + finrank ℝ (e.normalFiber x) = e.ambientDimension := by
  calc
    finrank ℝ E + finrank ℝ (e.normalFiber x) =
        finrank ℝ (e.tangentImage x) + finrank ℝ (e.tangentImage x)ᗮ :=
      congrArg (fun n => n + finrank ℝ (e.normalFiber x)) (e.finrank_tangentImage x).symm
    _ = finrank ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
      (e.tangentImage x).finrank_add_finrank_orthogonal
    _ = e.ambientDimension := finrank_euclideanSpace_fin

variable [FiniteDimensional ℝ E]

local instance tangentSpaceT2 (x : M) : T2Space (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (T2Space E)

local instance tangentSpaceFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- The native derivative identifies the original tangent space with its embedded image. -/
def tangentImageEquiv (x : M) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] e.tangentImage x :=
  (LinearEquiv.ofInjective (mvfderiv 𝓘(ℝ, E) e.toFun x).toLinearMap
    (e.injective_mvfderiv x)).toContinuousLinearEquiv

/-- The embedded tangent and actual normal spaces recover ambient Euclidean space. -/
def tangentNormalEquiv (x : M) : (TangentSpace 𝓘(ℝ, E) x × e.normalFiber x) ≃L[ℝ]
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  ((LinearEquiv.prodCongr (e.tangentImageEquiv x).toLinearEquiv
    (LinearEquiv.refl ℝ (e.normalFiber x))).trans
      ((e.tangentImage x).prodEquivOfIsCompl (e.normalFiber x)
        (e.tangentImage x).isCompl_orthogonal)).toContinuousLinearEquiv

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Normal projections vary smoothly on the original manifold, without changing its atlas. -/
theorem contMDiff_normalProjection :
    ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ, EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
        EuclideanSpace ℝ (Fin e.ambientDimension)) ∞ e.normalProjection := by
  have heq : e.normalProjection = fun x => 1 - e.tangentProjection x :=
    funext e.normalProjection_eq
  rw [heq]
  exact contMDiff_const.sub e.contMDiff_tangentProjection

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
