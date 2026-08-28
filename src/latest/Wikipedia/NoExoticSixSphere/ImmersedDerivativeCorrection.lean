import Wikipedia.NoExoticSixSphere.ImmersedSphereDerivativeParity
import Wikipedia.NoExoticSixSphere.ImmersedEndpointParityBalls

/-!
# Cancellation of derivative-frame and unordered-double-point changes

The two actual endpoint-sum theorems have the same singularity count.
Their sum therefore proves invariance of the corrected untwisted value
through a generic perturbation of any smooth family with immersed exterior
slices and self-transverse endpoints. All genericity and parity-ball data
are constructed here, not hypotheses of the final family theorem.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

def immersedDerivativeCorrectedParity (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) : ZMod 2 :=
  e.sphereDerivativeParity a f hf hd + SphereSelfIntersections.unorderedParity f

theorem immersedDerivativeCorrectedParity_congr {f g : Sphere 3 → M} (hfg : f = g)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) :
    e.immersedDerivativeCorrectedParity a f hf hd =
      e.immersedDerivativeCorrectedParity a g hg hgd := by
  subst g
  rfl

variable [IsManifold (𝓡 6) ∞ M] [CompactSpace M]

theorem derivativeCorrectedParity_eq_of_smooth_family (r : TubularRetraction e)
    (f : ℝ → Sphere 3 → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ s,
      Injective (mfderiv (𝓡 3) (𝓡 6) (f t) s))
    (ht : ∀ t, t = 0 ∨ t = 1 → ∀ x y, x ≠ y → f t x = f t y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod (mfderiv (𝓡 3) (𝓡 6) (f t) y))) :
    e.immersedDerivativeCorrectedParity a (f 0)
        (hf.comp (contMDiff_const.prodMk contMDiff_id)) (hext 0 (.inl le_rfl)) =
      e.immersedDerivativeCorrectedParity a (f 1)
        (hf.comp (contMDiff_const.prodMk contMDiff_id)) (hext 1 (.inr le_rfl)) := by
  obtain ⟨p, _, hg, _, heq, ⟨P⟩, hcount⟩ :=
    ManifoldAffineSphereFamily.exists_small_family_with_immersed_parityBalls e r f hf hext ht
      (by norm_num : (0 : ℝ) < 1)
  let g := ManifoldAffineSphereFamily.map e r f p
  have h₀ : g 0 = f 0 := funext (heq 0 (.inl le_rfl))
  have h₁ : g 1 = f 1 := funext (heq 1 (.inr le_rfl))
  have hg₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  have hg₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  have hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s) := by
    rw [h₀]
    exact hext 0 (.inl le_rfl)
  have hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s) := by
    rw [h₁]
    exact hext 1 (.inr le_rfl)
  have hframe := e.sphereDerivativeParity_endpoint_sum a g hg P hg₀ hd₀ hg₁ hd₁
  have hsum := hframe.trans hcount.symm
  have H : e.immersedDerivativeCorrectedParity a (g 0) hg₀ hd₀ =
      e.immersedDerivativeCorrectedParity a (g 1) hg₁ hd₁ := by
    let u := e.sphereDerivativeParity a (g 0) hg₀ hd₀
    let v := e.sphereDerivativeParity a (g 1) hg₁ hd₁
    let x := SphereSelfIntersections.unorderedParity (g 0)
    let y := SphereSelfIntersections.unorderedParity (g 1)
    change u + x = v + y
    have hs : u + v = x + y := hsum
    rw [eq_sub_of_add_eq hs, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    calc
      x + y + v + x = (v + y) + (x + x) := by abel
      _ = v + y := by rw [ZModModule.add_self, add_zero]
  have H₀ := e.immersedDerivativeCorrectedParity_congr a h₀ hg₀
    (hf.comp (contMDiff_const.prodMk contMDiff_id)) hd₀ (hext 0 (.inl le_rfl))
  have H₁ := e.immersedDerivativeCorrectedParity_congr a h₁ hg₁
    (hf.comp (contMDiff_const.prodMk contMDiff_id)) hd₁ (hext 1 (.inr le_rfl))
  exact H₀.symm.trans (H.trans H₁)

end NoExoticSixSphere.EuclideanEmbedding
