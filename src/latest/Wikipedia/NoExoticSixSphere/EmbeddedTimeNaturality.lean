import Wikipedia.NoExoticSixSphere.EmbeddedTimeGradient
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Intrinsic time-gradients under actual isometric seam parametrizations

Two native parametrizations of the same embedded time neighborhood determine
the same gradient, after the specified ambient linear isometry. The proof
differentiates the actual embedding and time identities and uses the native
local-diffeomorphism differentials. No compatibility of tubular choices is
assumed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (Vector n) M₁] [IsManifold (𝓡 n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (Vector n) M₂] [IsManifold (𝓡 n) ∞ M₂]
  (e₁ : EuclideanEmbedding n M₁) (e₂ : EuclideanEmbedding n M₂)
  (r₁ : e₁.TubularRetraction) (r₂ : e₂.TubularRetraction)
  (t₁ : M₁ → ℝ) (t₂ : M₂ → ℝ)
  (ht₁ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t₁)
  (ht₂ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t₂)

include ht₁ ht₂ in
theorem gradient_of_differential_comparison (x₁ : M₁) (x₂ : M₂)
    (J : Vector e₁.ambientDimension →ₗᵢ[ℝ] Vector e₂.ambientDimension)
    (L₁ L₂ : Vector n →L[ℝ] Vector n) (h₁ : Surjective L₁) (h₂ : Surjective L₂)
    (he : ∀ v, embeddingDerivative e₂ x₂ (L₂ v) = J (embeddingDerivative e₁ x₁ (L₁ v)))
    (ht : ∀ v, timeDerivative (n := n) t₂ x₂ (L₂ v) =
      timeDerivative (n := n) t₁ x₁ (L₁ v)) :
    gradient e₂ r₂ t₂ x₂ = J (gradient e₁ r₁ t₁ x₁) := by
  symm
  apply gradient_unique e₂ r₂ t₂ ht₂ x₂
  · obtain ⟨w, hw⟩ := gradient_mem_tangent e₁ r₁ t₁ x₁
    obtain ⟨v, hv⟩ := h₁ w
    refine ⟨L₂ v, ?_⟩
    change embeddingDerivative e₂ x₂ (L₂ v) = J (gradient e₁ r₁ t₁ x₁)
    rw [he, hv]
    exact congrArg J hw
  · intro w
    obtain ⟨v, rfl⟩ := h₂ w
    rw [he, J.inner_map_map, inner_gradient_native e₁ r₁ t₁ ht₁, ht]

include ht₁ in
theorem gradient_neg (x : M₁) :
    gradient e₁ r₁ (fun y ↦ -t₁ y) x = -gradient e₁ r₁ t₁ x := by
  symm
  apply gradient_unique e₁ r₁ (fun y ↦ -t₁ y) ht₁.neg x
  · exact (e₁.tangentImage x).neg_mem (gradient_mem_tangent e₁ r₁ t₁ x)
  · intro v
    rw [inner_neg_left, inner_gradient_native e₁ r₁ t₁ ht₁]
    have hneg : timeDerivative (n := n) (fun y ↦ -t₁ y) x =
        -timeDerivative (n := n) t₁ x := by
      change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (-t₁) x = -mfderiv (𝓡 n) 𝓘(ℝ, ℝ) t₁ x
      rw [mfderiv_neg]
    exact (congrArg (fun L : Vector n →L[ℝ] ℝ ↦ L v) hneg).symm

variable {P : Type*} [TopologicalSpace P] [ChartedSpace (Vector n) P]
  [IsManifold (𝓡 n) ∞ P]

def parameterDerivative (f : P → M₁) (p : P) : Vector n →L[ℝ] Vector n :=
  mfderiv (𝓡 n) (𝓡 n) f p

def ambientParameterDerivative {N : ℕ} (F : P → Vector N) (p : P) :
    Vector n →L[ℝ] Vector N := mfderiv (𝓡 n) (𝓡 N) F p

theorem parameterDerivative_surjective (f : P → M₁) (p : P)
    (hf : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ f p) :
    Surjective (parameterDerivative (n := n) f p) :=
  (hf.mfderivToContinuousLinearEquiv (by simp)).surjective

theorem embedding_parameter_differential (f : P → M₁) (p : P)
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f p) :
    (mfderiv (𝓡 n) (𝓡 e₁.ambientDimension) (e₁.toFun ∘ f) p :
      Vector n →L[ℝ] Vector e₁.ambientDimension) =
        (embeddingDerivative e₁ (f p)).comp (parameterDerivative f p) :=
  mfderiv_comp p (e₁.smooth.mdifferentiableAt (by simp)) hf

include ht₁ in
theorem time_parameter_differential (f : P → M₁) (p : P)
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f p) :
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (t₁ ∘ f) p : Vector n →L[ℝ] ℝ) =
      (timeDerivative (n := n) t₁ (f p)).comp (parameterDerivative f p) :=
  mfderiv_comp p (ht₁.mdifferentiableAt (by simp)) hf

include ht₁ ht₂ in
theorem gradient_natural (f₁ : P → M₁) (f₂ : P → M₂) (p : P)
    (hf₁ : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ f₁ p)
    (hf₂ : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ f₂ p)
    (J : Vector e₁.ambientDimension →ₗᵢ[ℝ] Vector e₂.ambientDimension)
    (he : ∀ q, e₂.toFun (f₂ q) = J (e₁.toFun (f₁ q)))
    (ht : ∀ q, t₂ (f₂ q) = t₁ (f₁ q)) :
    gradient e₂ r₂ t₂ (f₂ p) = J (gradient e₁ r₁ t₁ (f₁ p)) := by
  have h₁ := hf₁.mdifferentiableAt (by simp)
  have h₂ := hf₂.mdifferentiableAt (by simp)
  have hcomp : e₂.toFun ∘ f₂ = J ∘ (e₁.toFun ∘ f₁) := funext he
  have hJ : MDifferentiableAt (𝓡 e₁.ambientDimension) (𝓡 e₂.ambientDimension)
      J (e₁.toFun (f₁ p)) := J.toContinuousLinearMap.differentiableAt.mdifferentiableAt
  have hJd : (mfderiv (𝓡 e₁.ambientDimension) (𝓡 e₂.ambientDimension) J
      (e₁.toFun (f₁ p)) : Vector e₁.ambientDimension →L[ℝ] Vector e₂.ambientDimension) =
        J.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact J.toContinuousLinearMap.fderiv
  have hdiff : (embeddingDerivative e₂ (f₂ p)).comp (parameterDerivative f₂ p) =
      J.toContinuousLinearMap.comp
        ((embeddingDerivative e₁ (f₁ p)).comp (parameterDerivative f₁ p)) := by
    have hc : (mfderiv (𝓡 n) (𝓡 e₂.ambientDimension) (J ∘ (e₁.toFun ∘ f₁)) p :
        Vector n →L[ℝ] Vector e₂.ambientDimension) =
          (mfderiv (𝓡 e₁.ambientDimension) (𝓡 e₂.ambientDimension) J
            (e₁.toFun (f₁ p)) : Vector e₁.ambientDimension →L[ℝ]
              Vector e₂.ambientDimension).comp
            (mfderiv (𝓡 n) (𝓡 e₁.ambientDimension) (e₁.toFun ∘ f₁) p :
              Vector n →L[ℝ] Vector e₁.ambientDimension) :=
      mfderiv_comp p hJ ((e₁.smooth.mdifferentiableAt (by simp)).comp p h₁)
    have hc' := congrArg (fun F : P → Vector e₂.ambientDimension ↦
      ambientParameterDerivative (n := n) F p) hcomp
    exact (embedding_parameter_differential e₂ f₂ p h₂).symm.trans
      (hc'.trans (hc.trans (congrArg₂
        (fun (L : Vector e₁.ambientDimension →L[ℝ] Vector e₂.ambientDimension)
          (K : Vector n →L[ℝ] Vector e₁.ambientDimension) ↦ L.comp K)
        hJd (embedding_parameter_differential e₁ f₁ p h₁))))
  have htime : (timeDerivative (n := n) t₂ (f₂ p)).comp (parameterDerivative f₂ p) =
      (timeDerivative (n := n) t₁ (f₁ p)).comp (parameterDerivative f₁ p) := by
    rw [← time_parameter_differential t₂ ht₂ f₂ p h₂,
      ← time_parameter_differential t₁ ht₁ f₁ p h₁]
    exact congrArg (fun t : P → ℝ ↦ timeDerivative (n := n) t p) (funext ht)
  apply gradient_of_differential_comparison e₁ e₂ r₁ r₂ t₁ t₂ ht₁ ht₂ (f₁ p) (f₂ p) J
    (parameterDerivative f₁ p) (parameterDerivative f₂ p)
    (parameterDerivative_surjective f₁ p hf₁) (parameterDerivative_surjective f₂ p hf₂)
  · intro v
    exact congrArg (fun L : Vector n →L[ℝ] Vector e₂.ambientDimension ↦ L v) hdiff
  · intro v
    exact congrArg (fun L : Vector n →L[ℝ] ℝ ↦ L v) htime

end NoExoticSixSphere.EmbeddedTime
