import Wikipedia.NoExoticSixSphere.ImmersedDerivativeCorrection
import Wikipedia.NoExoticSixSphere.SmoothCollaredManifoldHomotopy

/-!
# Corrected derivative parity is invariant under ordinary homotopy

Only the endpoint sphere maps must be smooth self-transverse immersions.
The original continuous homotopy is smoothed relative to its endpoint
collars, then the proved generic-family construction supplies all interior
regularity, parity balls, and compact unordered boundary counts.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem derivativeCorrectedParity_homotopic (f g : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s))
    (ht₀ : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    (ht₁ : ∀ x y, x ≠ y → g x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y)))
    (H : f.Homotopic g) :
    e.immersedDerivativeCorrectedParity a f hf hd =
      e.immersedDerivativeCorrectedParity a g hg hgd := by
  let : Nonempty M := ⟨f (pole 3)⟩
  obtain ⟨r⟩ := e.nonempty_tubularRetraction a
  obtain ⟨K⟩ := H
  obtain ⟨G, hG, hleft, hright⟩ := e.exists_smoothCollaredHomotopy r f g hf hg K
  let u : ℝ → Sphere 3 → M := fun t s ↦ G (t, s)
  have hu : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry u) := hG
  have hl (t : ℝ) (ht : t ≤ 0) : u t = f := funext (hleft t (by linarith))
  have hr (t : ℝ) (ht : 1 ≤ t) : u t = g := funext (hright t (by linarith))
  have hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 6) (u t) s) := by
    intro t ht
    rcases ht with ht | ht
    · rw [hl t ht]
      exact hd
    · rw [hr t ht]
      exact hgd
  have ht : ∀ t, t = 0 ∨ t = 1 → ∀ x y, x ≠ y → u t x = u t y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (u t) x).coprod (mfderiv (𝓡 3) (𝓡 6) (u t) y)) := by
    intro t ht
    rcases ht with rfl | rfl
    · rw [hl 0 le_rfl]
      exact ht₀
    · rw [hr 1 le_rfl]
      exact ht₁
  have hu₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (u 0) :=
    hu.comp (contMDiff_const.prodMk contMDiff_id)
  have hu₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (u 1) :=
    hu.comp (contMDiff_const.prodMk contMDiff_id)
  have Hfamily := e.derivativeCorrectedParity_eq_of_smooth_family a r u hu hext ht
  have H₀ := e.immersedDerivativeCorrectedParity_congr a (hl 0 le_rfl) hu₀ hf
    (hext 0 (.inl le_rfl)) hd
  have H₁ := e.immersedDerivativeCorrectedParity_congr a (hr 1 le_rfl) hu₁ hg
    (hext 1 (.inr le_rfl)) hgd
  exact H₀.symm.trans (Hfamily.trans H₁)

end NoExoticSixSphere.EuclideanEmbedding
