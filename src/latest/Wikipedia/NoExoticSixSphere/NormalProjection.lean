import Wikipedia.NoExoticSixSphere.EuclideanEmbedding
import Wikipedia.NoExoticSixSphere.SmoothProjection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth dependence of the embedded tangent spaces

The differential of an embedding is written in one fixed tangent chart near a
base point. Its range is independent of that choice of chart. Combining this
with the Gram projection formula gives a globally smooth family of orthogonal
projections onto the embedded tangent spaces.
-/

open scoped Manifold ContDiff Topology
open Function Filter Bundle

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M)

/-- The derivative written in the tangent chart centered at `x₀`. -/
noncomputable def localDifferential (x₀ : M) :
    M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  inTangentCoordinates (𝓡 n) (𝓡 e.ambientDimension) id e.toFun
    (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun) x₀

/-- The fixed-chart differential is smooth at its center. -/
theorem contMDiffAt_localDifferential (x₀ : M) :
    ContMDiffAt (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
      ∞ (e.localDifferential x₀) x₀ :=
  e.smooth.contMDiffAt.mfderiv_const (by simp)

/-- With a Euclidean target, only the source tangent-coordinate change remains. -/
theorem localDifferential_eq (x₀ y : M) :
    e.localDifferential x₀ y = (mvfderiv (𝓡 n) e.toFun y).comp
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀).symmL ℝ y) := by
  simp only [localDifferential, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  rfl

/-- Inside a tangent chart, its inverse fiber map is a genuine linear isomorphism. -/
private theorem localFiberMap_bijective (x₀ y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source) :
    Bijective ((trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x₀).symmL ℝ y) := by
  have hy' : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hy']
  exact ContinuousLinearEquiv.bijective _

/-- Changing source tangent coordinates preserves injectivity. -/
theorem localDifferential_injective (x₀ y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source) :
    Injective (e.localDifferential x₀ y) := by
  rw [e.localDifferential_eq]
  exact (e.injective_mvfderiv y).comp (localFiberMap_bijective x₀ y hy).1

/-- The range of the fixed-chart differential is the intrinsic embedded tangent image. -/
theorem localDifferential_range (x₀ y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source) :
    (e.localDifferential x₀ y).range = e.tangentImage y := by
  rw [e.localDifferential_eq]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr (localFiberMap_bijective x₀ y hy).2

/-- Orthogonal projection onto the embedded tangent space at a point. -/
noncomputable def tangentProjection (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.tangentImage x).starProjection

/-- The embedded tangent-space projection is globally smooth, even though the
unadjusted coordinate expression for the derivative need not be globally continuous. -/
theorem contMDiff_tangentProjection :
    ContMDiff (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
        EuclideanSpace ℝ (Fin e.ambientDimension)) ∞ e.tangentProjection := by
  intro x
  have h := contMDiffAt_gramProjection (e.contMDiffAt_localDifferential x)
    (e.localDifferential_injective x x (mem_chart_source _ _))
  have heq : e.tangentProjection =ᶠ[𝓝 x] (fun y ↦ gramProjection (e.localDifferential x y)) := by
    filter_upwards [chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) x] with y hy
    simpa only [tangentProjection, e.localDifferential_range x y hy] using
      (gramProjection_eq_starProjection _ (e.localDifferential_injective x y hy)).symm
  exact heq.contMDiffAt_iff.mpr h

/-- Orthogonal projection onto the actual normal fiber. -/
noncomputable def normalProjection (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.normalFiber x).starProjection

omit [IsManifold (𝓡 n) ∞ M] in
/-- Normal projection is the complement of tangent projection. -/
theorem normalProjection_eq (x : M) :
    e.normalProjection x = 1 - e.tangentProjection x :=
  Submodule.starProjection_orthogonal' (e.tangentImage x)

/-- The normal projection varies smoothly over the entire manifold. -/
theorem contMDiff_normalProjection :
    ContMDiff (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
        EuclideanSpace ℝ (Fin e.ambientDimension)) ∞ e.normalProjection := by
  have heq : e.normalProjection = fun x ↦ 1 - e.tangentProjection x :=
    funext e.normalProjection_eq
  rw [heq]
  exact
    (contMDiff_const.sub e.contMDiff_tangentProjection :
      ContMDiff (𝓡 n) _ ∞ (fun x ↦ (1 : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
        EuclideanSpace ℝ (Fin e.ambientDimension)) - e.tangentProjection x))

omit [IsManifold (𝓡 n) ∞ M] in
/-- Its image is the normal fiber defined as an orthogonal complement. -/
theorem range_normalProjection (x : M) :
    (e.normalProjection x).range = e.normalFiber x :=
  (e.normalFiber x).range_starProjection

omit [IsManifold (𝓡 n) ∞ M] in
/-- Normal projection is idempotent. -/
theorem normalProjection_idempotent (x : M) : IsIdempotentElem (e.normalProjection x) :=
  (e.normalFiber x).isIdempotentElem_starProjection

end NoExoticSixSphere.EuclideanEmbedding
