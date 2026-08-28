import Wikipedia.NoExoticSixSphere.ManifoldIntersectionGenericParameter
import Wikipedia.NoExoticSixSphere.IntersectionTraceRegularParity
import Wikipedia.NoExoticSixSphere.SmoothCollaredManifoldHomotopy

/-!
# Actual mod-two intersection counts are invariant under ordinary homotopy

Relative smoothing supplies smooth real-time families with the original
endpoint maps. The proved small perturbation makes all interior intersections
regular while leaving those endpoints unchanged. The actual compact trace
then proves equality of its endpoint counts. No transversality or immersion
assumption is imposed on the given homotopies, and no collar is required of
the perturbed family.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization MapIntersections ManifoldAffineSphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem intersectionParity_eq_of_smooth_families (f g : ℝ → Sphere 3 → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
    (ht : ∀ t : unitInterval, t = 0 ∨ t = 1 → ∀ x y, f t x = g t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g t) y))) :
    (pairs (f 0) (g 0)).Finite ∧ (pairs (f 1) (g 1)).Finite ∧
      parity (f 0) (g 0) = parity (f 1) (g 1) := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  obtain ⟨p, _, _, hF, hext, hreg⟩ :=
    ManifoldIntersectionFamily.exists_small_regular_manifold_intersections e r f g hf hg
      (show (0 : ℝ) < 1 from zero_lt_one)
  let F := ManifoldAffineSphereFamily.map e r f p
  have he0 : F 0 = f 0 := funext (hext 0 (Or.inl le_rfl))
  have he1 : F 1 = f 1 := funext (hext 1 (Or.inr le_rfl))
  have htF : ∀ t : unitInterval, t = 0 ∨ t = 1 → ∀ x y, F t x = g t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (F t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g t) y)) := by
    intro t htc x y hxy
    rcases htc with rfl | rfl
    · change F 0 x = g 0 y at hxy
      change Surjective ((mfderiv (𝓡 3) (𝓡 6) (F 0) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g 0) y))
      rw [he0] at hxy ⊢
      exact ht 0 (Or.inl rfl) x y hxy
    · change F 1 x = g 1 y at hxy
      change Surjective ((mfderiv (𝓡 3) (𝓡 6) (F 1) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g 1) y))
      rw [he1] at hxy ⊢
      exact ht 1 (Or.inr rfl) x y hxy
  have h := IntersectionTrace.parity_eq_of_regular_family F g hF hg hreg htF
  rwa [he0, he1] at h

include e r in
theorem intersectionParity_homotopic (f₀ f₁ g₀ g₁ : C(Sphere 3, M))
    (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₀) (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₁)
    (hg₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ g₀) (hg₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ g₁)
    (ht₀ : ∀ x y, f₀ x = g₀ y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f₀ x).coprod (mfderiv (𝓡 3) (𝓡 6) g₀ y)))
    (ht₁ : ∀ x y, f₁ x = g₁ y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f₁ x).coprod (mfderiv (𝓡 3) (𝓡 6) g₁ y)))
    (Hf : f₀.Homotopic f₁) (Hg : g₀.Homotopic g₁) :
    parity f₀ g₀ = parity f₁ g₁ := by
  obtain ⟨Hf⟩ := Hf
  obtain ⟨Hg⟩ := Hg
  obtain ⟨F, hF, hFleft, hFright⟩ := e.exists_smoothCollaredHomotopy r f₀ f₁ hf₀ hf₁ Hf
  obtain ⟨G, hG, hGleft, hGright⟩ := e.exists_smoothCollaredHomotopy r g₀ g₁ hg₀ hg₁ Hg
  let f : ℝ → Sphere 3 → M := fun t x ↦ F (t, x)
  let g : ℝ → Sphere 3 → M := fun t x ↦ G (t, x)
  have hf0 : f 0 = f₀ := funext (hFleft 0 (by norm_num))
  have hf1 : f 1 = f₁ := funext (hFright 1 (by norm_num))
  have hg0 : g 0 = g₀ := funext (hGleft 0 (by norm_num))
  have hg1 : g 1 = g₁ := funext (hGright 1 (by norm_num))
  have ht : ∀ t : unitInterval, t = 0 ∨ t = 1 → ∀ x y, f t x = g t y →
      Surjective ((mfderiv (𝓡 3) (𝓡 6) (f t) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g t) y)) := by
    intro t htc x y hxy
    rcases htc with rfl | rfl
    · change f 0 x = g 0 y at hxy
      change Surjective ((mfderiv (𝓡 3) (𝓡 6) (f 0) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g 0) y))
      rw [hf0, hg0] at hxy ⊢
      exact ht₀ x y hxy
    · change f 1 x = g 1 y at hxy
      change Surjective ((mfderiv (𝓡 3) (𝓡 6) (f 1) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g 1) y))
      rw [hf1, hg1] at hxy ⊢
      exact ht₁ x y hxy
  have he := (e.intersectionParity_eq_of_smooth_families r f g hF hG ht).2.2
  rwa [hf0, hf1, hg0, hg1] at he

/-- For a framed manifold, the tubular retraction is constructed internally. -/
theorem intersectionParity_homotopic_of_normalFrame
    (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
    (f₀ f₁ g₀ g₁ : C(Sphere 3, M))
    (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₀) (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₁)
    (hg₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ g₀) (hg₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ g₁)
    (ht₀ : ∀ x y, f₀ x = g₀ y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f₀ x).coprod (mfderiv (𝓡 3) (𝓡 6) g₀ y)))
    (ht₁ : ∀ x y, f₁ x = g₁ y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f₁ x).coprod (mfderiv (𝓡 3) (𝓡 6) g₁ y)))
    (Hf : f₀.Homotopic f₁) (Hg : g₀.Homotopic g₁) :
    parity f₀ g₀ = parity f₁ g₁ := by
  let : Nonempty M := ⟨f₀ (Classical.choice
    (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one))⟩
  obtain ⟨r⟩ := e.nonempty_tubularRetraction a
  exact e.intersectionParity_homotopic r f₀ f₁ g₀ g₁ hf₀ hf₁ hg₀ hg₁ ht₀ ht₁ Hf Hg

end NoExoticSixSphere.EuclideanEmbedding
