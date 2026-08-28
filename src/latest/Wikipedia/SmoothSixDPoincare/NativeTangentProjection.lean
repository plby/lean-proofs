import Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
import Wikipedia.NoExoticSixSphere.SmoothProjection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth tangent projections for the native Euclidean embedding

The derivative in a fixed tangent chart is precomposed with a fixed Euclidean
linear model. Its Gram projection equals the intrinsic embedded tangent
projection. This proves smoothness without altering the original norm or atlas.
-/

noncomputable section

open Function Filter Bundle
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)

/-- The derivative written in one fixed source tangent chart. -/
def localDifferential (x₀ : M) :
    M → E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  inTangentCoordinates 𝓘(ℝ, E) (𝓡 e.ambientDimension) id e.toFun
    (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun) x₀

/-- Fixed-chart derivatives vary smoothly near the center. -/
theorem contMDiffAt_localDifferential (x₀ : M) :
    ContMDiffAt 𝓘(ℝ, E)
      𝓘(ℝ, E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) ∞
      (e.localDifferential x₀) x₀ :=
  e.smooth.contMDiffAt.mfderiv_const (by simp)

/-- Only a source tangent-coordinate change remains for a vector-space target. -/
theorem localDifferential_eq (x₀ y : M) :
    e.localDifferential x₀ y = (mvfderiv 𝓘(ℝ, E) e.toFun y).comp
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y) := by
  simp only [localDifferential, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  rfl

private theorem localFiberMap_bijective (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) :
    Bijective ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y) := by
  have hy' : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hy']
  exact ContinuousLinearEquiv.bijective _

/-- These actual coordinate derivatives are injective. -/
theorem localDifferential_injective (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    Injective (e.localDifferential x₀ y) := by
  rw [e.localDifferential_eq]
  exact (e.injective_mvfderiv y).comp (localFiberMap_bijective x₀ y hy).1

/-- Source tangent-coordinate changes do not change the embedded tangent image. -/
theorem localDifferential_range (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    (e.localDifferential x₀ y).range = e.tangentImage y := by
  rw [e.localDifferential_eq]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr (localFiberMap_bijective x₀ y hy).2

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Orthogonal projection in the ambient Euclidean space onto the actual tangent image. -/
def tangentProjection (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
      EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.tangentImage x).starProjection

variable [FiniteDimensional ℝ E]

/-- The native manifold's embedded tangent projection is globally smooth. -/
theorem contMDiff_tangentProjection :
    ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ, EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
        EuclideanSpace ℝ (Fin e.ambientDimension)) ∞ e.tangentProjection := by
  let φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  intro x
  let A (y : M) := (e.localDifferential x y).comp φ.toContinuousLinearMap
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, _ →L[ℝ] _) ∞ A x :=
    (e.contMDiffAt_localDifferential x).clm_comp contMDiffAt_const
  have hi (y : M) (hy : y ∈ (chartAt E x).source) : Injective (A y) :=
    (e.localDifferential_injective x y hy).comp φ.injective
  have hr (y : M) (hy : y ∈ (chartAt E x).source) :
      (A y).range = e.tangentImage y := by
    calc
      (A y).range = (e.localDifferential x y).range :=
        LinearMap.range_comp_of_range_eq_top _
          (LinearMap.range_eq_top.mpr φ.surjective)
      _ = e.tangentImage y := e.localDifferential_range x y hy
  have h := NoExoticSixSphere.contMDiffAt_gramProjection hs
    (hi x (mem_chart_source _ _))
  have heq : e.tangentProjection =ᶠ[𝓝 x]
      (fun y => NoExoticSixSphere.gramProjection (A y)) := by
    filter_upwards [chart_source_mem_nhds E x] with y hy
    simpa only [tangentProjection, hr y hy] using
      (NoExoticSixSphere.gramProjection_eq_starProjection _ (hi y hy)).symm
  exact heq.contMDiffAt_iff.mpr h

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The tangent projection has exactly the required range. -/
theorem range_tangentProjection (x : M) :
    (e.tangentProjection x).range = e.tangentImage x :=
  (e.tangentImage x).range_starProjection

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The actual tangent projection is idempotent. -/
theorem tangentProjection_idempotent (x : M) : IsIdempotentElem (e.tangentProjection x) :=
  (e.tangentImage x).isIdempotentElem_starProjection

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
