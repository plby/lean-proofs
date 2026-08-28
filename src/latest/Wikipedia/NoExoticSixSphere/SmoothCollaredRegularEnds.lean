import Wikipedia.NoExoticSixSphere.SmoothCollaredSphereHomotopy
import Wikipedia.NoExoticSixSphere.CylinderSliceRegularity

/-!
# Smooth collared homotopies preserve endpoint regularity

If the specified value is regular for both smooth endpoint maps, the smooth
collared representative has that value regular throughout its protected
closed ends. Regularity in the middle of the homotopy is a separate, still
unproved transversality requirement.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem exists_smoothCollaredSphereHomotopy_regularEnds {n : ℕ} {f₀ f₁ : C(M, Sphere n)}
    (h₀ : ContMDiff I (𝓡 n) ∞ f₀) (h₁ : ContMDiff I (𝓡 n) ∞ f₁)
    (H : f₀.Homotopy f₁) (b : Sphere n)
    (hreg₀ : ∀ x, f₀ x = b → Function.Surjective (mfderiv I (𝓡 n) f₀ x))
    (hreg₁ : ∀ x, f₁ x = b → Function.Surjective (mfderiv I (𝓡 n) f₁ x)) :
    ∃ G : C(ℝ × M, Sphere n), ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ G ∧
      (∀ t : ℝ, t ≤ 1 / 4 → ∀ x, G (t, x) = f₀ x) ∧
      (∀ t : ℝ, 3 / 4 ≤ t → ∀ x, G (t, x) = f₁ x) ∧
      H.toContinuousMap.HomotopicRel (G.comp CylinderTime.inclusion) CylinderTime.boundary ∧
      ∀ p, (p.1 ≤ 1 / 4 ∨ 3 / 4 ≤ p.1) → G p = b →
        Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) G p) := by
  obtain ⟨G, hG, hleft, hright, hhom⟩ := exists_smoothCollaredSphereHomotopy h₀ h₁ H
  refine ⟨G, hG, hleft, hright, hhom, ?_⟩
  rintro ⟨t, x⟩ ht hx
  rcases ht with ht | ht
  · exact mfderiv_cylinder_surjective_of_slice G f₀ hG t (hleft t ht) x
      (hreg₀ x ((hleft t ht x).symm.trans hx))
  · exact mfderiv_cylinder_surjective_of_slice G f₁ hG t (hright t ht) x
      (hreg₁ x ((hright t ht x).symm.trans hx))

end NoExoticSixSphere
