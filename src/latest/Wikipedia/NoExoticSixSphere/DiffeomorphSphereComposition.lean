import Wikipedia.NoExoticSixSphere.FramedEmbeddingReparametrization

/-!
# Sphere representatives under a native diffeomorphism

Composition preserves the original smooth map, injectivity, and injective
manifold differential. Both independently supplied manifold atlases are
retained in these statements.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiffeomorphSphereComposition

open GLOrthonormalization

variable {n : ℕ} {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [TopologicalSpace M'] [ChartedSpace (Vector n) M']
  (D : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M') (f : Sphere 3 → M)
  (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)

include hf in
theorem smooth : ContMDiff (𝓡 3) (𝓡 n) ∞ (D ∘ f) := D.contMDiff.comp hf

theorem injective (hi : Injective f) : Injective (D ∘ f) := D.injective.comp hi

include hf in
theorem mfderiv_injective (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s)) (s : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 n) (D ∘ f) s) := by
  rw [mfderiv_comp s (D.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  exact ((D.isLocalDiffeomorph (f s)).mfderivToContinuousLinearEquiv
    (by simp)).injective.comp (hd s)

end NoExoticSixSphere.DiffeomorphSphereComposition
