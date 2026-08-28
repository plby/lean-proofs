import Wikipedia.NoExoticSixSphere.ManifoldGenericSphereParity
import Wikipedia.NoExoticSixSphere.SmoothCollaredManifoldHomotopy

/-!
# Geometric sphere parity is invariant under ordinary continuous homotopy

The endpoints are the original smooth embedded immersive spheres. No
immersion assumption is imposed on the homotopy. The actual tubular
retraction, relative smoothing, generic family, parity balls, and endpoint
operator homotopy are all supplied by proved constructions.
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

theorem sphereParity_homotopic (f g : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hi : Injective f) (hgi : Injective g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) (H : f.Homotopic g) :
    e.sphereParity a f hf hi hd = e.sphereParity a g hg hgi hgd := by
  let : Nonempty M := ⟨f (pole 3)⟩
  obtain ⟨r⟩ := e.nonempty_tubularRetraction a
  obtain ⟨K⟩ := H
  obtain ⟨G, hG, hleft, hright⟩ := e.exists_smoothCollaredHomotopy r f g hf hg K
  let u : ℝ → Sphere 3 → M := fun t s ↦ G (t, s)
  have hu : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry u) := hG
  have hl (t : ℝ) (ht : t ≤ 0) : u t = f :=
    funext (hleft t (by linarith))
  have hr (t : ℝ) (ht : 1 ≤ t) : u t = g :=
    funext (hright t (by linarith))
  have hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 6) (u t) s) := by
    intro t ht
    rcases ht with ht | ht
    · rw [hl t ht]
      exact hd
    · rw [hr t ht]
      exact hgd
  have hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (u t) := by
    intro t ht
    rcases ht with ht | ht
    · rw [hl t ht]
      exact hi
    · rw [hr t ht]
      exact hgi
  have hu₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (u 0) :=
    hu.comp (contMDiff_const.prodMk contMDiff_id)
  have hu₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (u 1) :=
    hu.comp (contMDiff_const.prodMk contMDiff_id)
  have Hfamily := e.sphereParity_eq_of_smooth_family_exterior a r u hu hext hinj
  have H₀ := e.sphereParity_congr a (hl 0 le_rfl) hu₀ hf (hinj 0 (.inl le_rfl)) hi
    (hext 0 (.inl le_rfl)) hd
  have H₁ := e.sphereParity_congr a (hr 1 le_rfl) hu₁ hg (hinj 1 (.inr le_rfl)) hgi
    (hext 1 (.inr le_rfl)) hgd
  exact H₀.symm.trans (Hfamily.trans H₁)

end NoExoticSixSphere.EuclideanEmbedding
