import Wikipedia.NoExoticSixSphere.ManifoldFamilyEndpointHomotopy
import Wikipedia.NoExoticSixSphere.ManifoldAffineParityBallSystem

/-!
# Geometric sphere parity agrees across an actual smooth family

The interior slices need not be immersive. The small generic-family theorem
chooses the perturbation and all parity balls, supplies the even singularity
count, and fixes every exterior slice exactly. The actual endpoint homotopy
comparison therefore proves equality of the original geometric sphere parity.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_congr {f g : Sphere 3 → M} (hfg : f = g)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hi : Injective f) (hgi : Injective g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) :
    e.sphereParity a f hf hi hd = e.sphereParity a g hg hgi hgd := by
  subst g
  rfl

variable [IsManifold (𝓡 6) ∞ M] [CompactSpace M]

theorem sphereParity_eq_of_smooth_family_exterior (r : TubularRetraction e)
    (f : ℝ → Sphere 3 → M)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f t) s))
    (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t)) :
    e.sphereParity a (f 0) (hf.comp (contMDiff_const.prodMk contMDiff_id))
      (hinj 0 (.inl le_rfl)) (hext 0 (.inl le_rfl)) =
    e.sphereParity a (f 1) (hf.comp (contMDiff_const.prodMk contMDiff_id))
      (hinj 1 (.inr le_rfl)) (hext 1 (.inr le_rfl)) := by
  obtain ⟨p, _, hg, _, heq, ⟨P⟩, heven⟩ :=
    ManifoldAffineSphereFamily.exists_small_family_with_parityBalls e r f hf hext hinj
      (by norm_num : (0 : ℝ) < 1)
  let g := ManifoldAffineSphereFamily.map e r f p
  have h₀ : g 0 = f 0 := funext (heq 0 (.inl le_rfl))
  have h₁ : g 1 = f 1 := funext (heq 1 (.inr le_rfl))
  have hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (f 0) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (f 1) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hg₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  have hg₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  have hdi₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s) := by
    rw [h₀]
    exact hext 0 (.inl le_rfl)
  have hdi₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s) := by
    rw [h₁]
    exact hext 1 (.inr le_rfl)
  have hi₀ : Injective (g 0) := by rw [h₀]; exact hinj 0 (.inl le_rfl)
  have hi₁ : Injective (g 1) := by rw [h₁]; exact hinj 1 (.inr le_rfl)
  have H := e.endpoint_sphereParity_eq a g hg P hg₀ hdi₀ hg₁ hdi₁ heven hi₀ hi₁
  have H₀ := e.sphereParity_congr a h₀ hg₀ hf₀ hi₀ (hinj 0 (.inl le_rfl))
    hdi₀ (hext 0 (.inl le_rfl))
  have H₁ := e.sphereParity_congr a h₁ hg₁ hf₁ hi₁ (hinj 1 (.inr le_rfl))
    hdi₁ (hext 1 (.inr le_rfl))
  exact H₀.symm.trans (H.trans H₁)

end NoExoticSixSphere.EuclideanEmbedding
