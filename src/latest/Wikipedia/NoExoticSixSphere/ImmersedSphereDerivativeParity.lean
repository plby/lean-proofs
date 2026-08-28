import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity
import Wikipedia.NoExoticSixSphere.ManifoldFamilyEndpointHomotopy

/-!
# The derivative-frame obstruction and its actual singularity relation

This is the untwisted obstruction of the original normal-plus-derivative
operator. For an actual parity-ball system, the sum of its endpoint values
is the number of actual singular parameters modulo two. No evenness of
that singularity count or injectivity of the endpoint maps is assumed.
Comparison with the source-twisted disk obstruction is separate.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

def sphereDerivativeParity (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) : ZMod 2 :=
  Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
    (by have h := e.dimension_le_ambient (f (pole 3)); omega) (by omega)
    (e.sphereFrameOperatorMap a f hf hd)

variable (g : ℝ → Sphere 3 → M)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (P : SphereFamily.ParityBallSystem g)

theorem familyBoundaryObstruction_zero_eq_derivativeParity
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0))
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s)) :
    e.familyBoundaryObstruction a g hg P (.inl false) =
      e.sphereDerivativeParity a (g 0) hf hd := rfl

theorem familyBoundaryObstruction_one_eq_derivativeParity
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1))
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s)) :
    e.familyBoundaryObstruction a g hg P (.inl true) =
      e.sphereDerivativeParity a (g 1) hf hd := rfl

include hg P in
theorem sphereDerivativeParity_endpoint_sum
    (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0))
    (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s))
    (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1))
    (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s)) :
    e.sphereDerivativeParity a (g 0) hf₀ hd₀ + e.sphereDerivativeParity a (g 1) hf₁ hd₁ =
      (Nat.card (SphereFamily.singularParameters (n := 6) g) : ZMod 2) := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (SphereFamily.singularParameters (n := 6) g)
  have h := e.sum_familyBoundaryObstruction_zero a g hg P
  rw [Fintype.sum_sum_type, Fintype.sum_bool] at h
  simp only [familyBoundaryObstruction_link, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at h
  rw [e.familyBoundaryObstruction_zero_eq_derivativeParity a g hg P hf₀ hd₀,
    e.familyBoundaryObstruction_one_eq_derivativeParity a g hg P hf₁ hd₁] at h
  have he := eq_neg_of_add_eq_zero_left h
  rw [ZMod.neg_eq_self_mod_two] at he
  simpa only [add_comm, Nat.card_eq_fintype_card] using he

end NoExoticSixSphere.EuclideanEmbedding
