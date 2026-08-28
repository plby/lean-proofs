import Wikipedia.SmoothSixDPoincare.AmbientBumpTranslations
import Wikipedia.SmoothSixDPoincare.SupportedBumpIsotopy

/-!
# Actual smooth ambient isotopies and their composition

The recorded maps are jointly smooth and every time slice is an actual
diffeomorphism. Small bump-family endpoints have such isotopies, constructed
by the existing smooth cutoff translations, and composition retains them.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- An actual jointly smooth isotopy from the identity to the given diffeomorphism. -/
def IsotopicToIdentity (e : Diffeomorph J J M M ∞) : Prop :=
  ∃ A : ℝ × M → M, ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
    (∀ y, A (0, y) = y) ∧ (∀ y, A (1, y) = e y) ∧
    ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y

theorem isotopicToIdentity_refl : IsotopicToIdentity (Diffeomorph.refl J M ∞) := by
  refine ⟨Prod.snd, contMDiff_snd, fun _ => rfl, fun _ => rfl, ?_⟩
  exact fun _ => ⟨Diffeomorph.refl J M ∞, fun _ => rfl⟩

/-- Compose the actual time slices; smoothness and both endpoints are preserved. -/
theorem IsotopicToIdentity.trans {e d : Diffeomorph J J M M ∞}
    (he : IsotopicToIdentity e) (hd : IsotopicToIdentity d) :
    IsotopicToIdentity (e.trans d) := by
  obtain ⟨A, hA, hA₀, hA₁, hAd⟩ := he
  obtain ⟨B, hB, hB₀, hB₁, hBd⟩ := hd
  refine ⟨fun p => B (p.1, A p), hB.comp (contMDiff_fst.prodMk hA), ?_, ?_, ?_⟩
  · intro y
    change B (0, A (0, y)) = y
    rw [hA₀, hB₀]
  · intro y
    change B (1, A (1, y)) = d (e y)
    rw [hA₁, hB₁]
  · intro t
    obtain ⟨e', he'⟩ := hAd t
    obtain ⟨d', hd'⟩ := hBd t
    refine ⟨e'.trans d', ?_⟩
    intro y
    change B (t, A (t, y)) = d' (e' y)
    rw [he', hd']

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)

/-- Every sufficiently small endpoint of the explicit ambient bump family is smoothly
isotopic to the identity, with an actual diffeomorphism at every intermediate time. -/
theorem exists_radius_bumpFamily_isotopy {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E, ‖a‖ < ε →
      ∀ e : Diffeomorph J J M M ∞, (∀ y, e y = bumpFamily Φ β (a, y)) →
        IsotopicToIdentity e := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  refine ⟨A, hA, hzero, ?_, hdiff⟩
  intro y
  rw [he]
  by_cases hy : y ∈ Φ.target
  · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
    have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
    rw [hpoint] at hh
    change A (1, y) = extendMap Φ (fun x => x + β x • a) y
    rw [extendMap_of_mem Φ _ hy]
    exact hh
  · have hnot : y ∉ Φ '' tsupport β := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hsupport hx))
    rw [hfix 1 y hnot, bumpFamily_fixed_outside Φ β a hnot]

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
