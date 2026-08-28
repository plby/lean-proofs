import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopyExtension

/-!
# Transporting both transverse corrections to the native cylinder labels

Source and target corrections of a relative endpoint chart are conjugated
through the two actual transverse charts and extended by identity. Their
composition is one global supported diffeomorphism of the common cylinder
labels, with an actual supported isotopy fixing the reference label.
The exact corrected transition formula holds on the original domain.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compose two actual common-support isotopies with the same fixed set. -/
def compose_supported_isotopies
    {D₁ D₂ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} {K₁ K₂ S : Set E}
    (A : SupportedRelativeIsotopy D₁ K₁ S) (B : SupportedRelativeIsotopy D₂ K₂ S) :
    SupportedRelativeIsotopy (D₁.trans D₂) (K₁ ∪ K₂) S where
  family := fun p => B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero := fun x => by rw [A.zero, B.zero]
  one := fun x => by change B.family (1, A.family (1, x)) = D₂ (D₁ x); rw [A.one, B.one]
  slices := by
    intro t
    obtain ⟨d₁, hd₁⟩ := A.slices t
    obtain ⟨d₂, hd₂⟩ := B.slices t
    refine ⟨d₁.trans d₂, ?_⟩
    intro x
    change d₂ (d₁ x) = B.family (t, A.family (t, x))
    rw [hd₁, hd₂]
  fixedOutside := by
    intro t x hx
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)),
      B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn := by
    intro t x hx
    rw [A.fixedOn t x hx, B.fixedOn t x hx]

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

open Classical in
/-- Conjugate the actual source and target corrections into one supported
correction of the common cylinder coordinates, retaining its exact formula. -/
theorem exists_transported_transition_correction
    (Q P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hQ0 : (0 : E) ∈ Q.source) (hP0 : (0 : E) ∈ P.source)
    (hQzero : Q 0 = 0) (hPzero : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {Kₛ Kₜ Sₛ Sₜ : Set E} (hKₛ : IsCompact Kₛ) (hKₜ : IsCompact Kₜ)
    (hKs : Kₛ ⊆ H.source) (hKt : Kₜ ⊆ H.target)
    (hSₛ : (0 : E) ∈ Sₛ) (hSₜ : (0 : E) ∈ Sₜ)
    (A : SupportedRelativeIsotopy Dₛ Kₛ Sₛ)
    (B : SupportedRelativeIsotopy Dₜ Kₜ Sₜ) :
    ∃ (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (K : Set Z),
      IsCompact K ∧ K = Q '' Kₛ ∪ P '' Kₜ ∧ K ⊆ Q.target ∩ P.target ∧
      Nonempty (SupportedRelativeIsotopy D K {(0 : Z)}) ∧ D 0 = 0 ∧
      ∀ z ∈ H.source, D (Q z) = P (Dₜ (H (Dₛ z))) := by
  have hKQ : Kₛ ⊆ Q.source := hKs.trans hHs
  have hKP : Kₜ ⊆ P.source := hKt.trans hHt
  have hfixedQ (z : E) (hz : z ∈ Q.source)
      (h : Q z ∈ ({(0 : Z)} : Set Z)) : z ∈ Sₛ := by
    have he : z = 0 := Q.toOpenPartialHomeomorph.injOn hz hQ0
      ((mem_singleton_iff.mp h).trans hQzero.symm)
    exact he.symm ▸ hSₛ
  have hfixedP (z : E) (hz : z ∈ P.source)
      (h : P z ∈ ({(0 : Z)} : Set Z)) : z ∈ Sₜ := by
    have he : z = 0 := P.toOpenPartialHomeomorph.injOn hz hP0
      ((mem_singleton_iff.mp h).trans hPzero.symm)
    exact he.symm ▸ hSₜ
  let A' := A.extension Q hKₛ hKQ hfixedQ
  let B' := B.extension P hKₜ hKP hfixedP
  let DQ := SupportedDiffeomorph.extension Q Dₛ hKₛ hKQ A.endpoint_fixed_outside
  let DP := SupportedDiffeomorph.extension P Dₜ hKₜ hKP B.endpoint_fixed_outside
  let D := DQ.trans DP
  let K := Q '' Kₛ ∪ P '' Kₜ
  have hK : IsCompact K :=
    (hKₛ.image_of_continuousOn (Q.contMDiffOn_toFun.continuousOn.mono hKQ)).union
      (hKₜ.image_of_continuousOn (P.contMDiffOn_toFun.continuousOn.mono hKP))
  have I : SupportedRelativeIsotopy D K {(0 : Z)} := compose_supported_isotopies A' B'
  have hKU : K ⊆ Q.target ∩ P.target := by
    rintro y (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨Q.map_source' (hKQ hz), ?_⟩
      rw [← hdiagram z (hKs hz)]
      exact P.map_source' (hHt (H.map_source' (hKs hz)))
    · refine ⟨?_, P.map_source' (hKP hz)⟩
      have hh := hdiagram (H.symm z) (H.map_target' (hKt hz))
      have hi : H (H.symm z) = z := H.right_inv' (hKt hz)
      rw [hi] at hh
      rw [hh]
      exact Q.map_source' (hHs (H.map_target' (hKt hz)))
  refine ⟨D, K, hK, rfl, hKU, ⟨I⟩, I.endpoint_fixed_on 0 rfl, ?_⟩
  intro z hz
  have hDz : Dₛ z ∈ H.source :=
    mapsTo_source H Dₛ.toEquiv hKs A.endpoint_fixed_outside hz
  change DP (DQ (Q z)) = P (Dₜ (H (Dₛ z)))
  rw [SupportedDiffeomorph.extension_chart Q Dₛ hKₛ hKQ A.endpoint_fixed_outside (hHs hz)]
  rw [← hdiagram (Dₛ z) hDz]
  exact SupportedDiffeomorph.extension_chart P Dₜ hKₜ hKP B.endpoint_fixed_outside
    (hHt (H.map_source' hDz))

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
