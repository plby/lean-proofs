import Wikipedia.SmoothSixDPoincare.FiniteMorseCancellationStep
import Mathlib.Data.Set.Card

/-!
# Iterate the actual signed Morse-belt Whitney moves

Induction on the actual finite crossing set composes the constructed native
isotopies. Each step removes two opposite signs, retains all surviving map
germs, and preserves the integer sum. The resulting sphere has no opposite
pair and keeps all native smoothness and transversality properties.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (D : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- Compose actual cancellation steps until no opposite pair remains in the actual crossing set. -/
theorem exists_finite_belt_reduction
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (P : Finset (Hemisphere.Sphere 2)) (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel), ∃ P' : Finset (Hemisphere.Sphere 2),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ x, g' x = e (g x)) ∧
        D.IsTransverseBeltSphere hf hdim hindex g' ∧
        (P' : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g' ∧ P' ⊆ P ∧
        (∀ x ∈ P', (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
        (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)) =
          ∑ x ∈ P, (D.beltIntersectionSign 2 r g x : ℤ) ∧
        ∀ x ∈ P', ∀ y ∈ P', D.beltIntersectionSign 2 r g' x *
          D.beltIntersectionSign 2 r g' y ≠ -1 := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  induction P using Finset.strongInductionOn generalizing g with
  | _ P ih =>
    by_cases hpair : ∃ x ∈ P, ∃ y ∈ P,
        D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hpair
      obtain ⟨e₁, g₁, hiso₁, heq₁, hgood₁, hR, hgerm₁, hsum₁⟩ :=
        D.exists_finite_belt_cancellation_step hf hdim hindex hnull r P g hP hgood x y hx hy hxy
      let R : Finset (Hemisphere.Sphere 2) := P \ {x, y}
      have hsubpair : ({x, y} : Finset (Hemisphere.Sphere 2)) ⊆ P := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · exact Finset.mem_singleton.mp hz ▸ hy
      have hRlt : R ⊂ P := Finset.sdiff_ssubset hsubpair ⟨x, by simp⟩
      obtain ⟨e₂, g₂, P₂, hiso₂, heq₂, hgood₂, hP₂, hsub₂, hgerm₂, hsum₂, hno₂⟩ :=
        ih R hRlt g₁ hR hgood₁
      refine ⟨e₁.trans e₂, g₂, P₂, hiso₁.trans hiso₂, ?_, hgood₂, hP₂,
        hsub₂.trans Finset.sdiff_subset, ?_, hsum₂.trans hsum₁, hno₂⟩
      · intro z
        change g₂ z = e₂ (e₁ (g z))
        rw [heq₂, heq₁]
      · intro z hz
        exact (hgerm₂ z hz).trans (hgerm₁ z (hsub₂ hz))
    · refine ⟨Diffeomorph.refl _ _ _, g, P, SupportedDiffeomorph.isotopicToIdentity_refl,
        fun _ => rfl, hgood, hP, fun _ hx => hx,
        fun _ _ => Filter.EventuallyEq.refl _ _, rfl, ?_⟩
      intro x hx y hy hxy
      exact hpair ⟨x, hx, y, hy, hxy⟩

open Classical in
/-- Isotope the original transverse sphere to the absolute signed intersection count. -/
theorem exists_minimal_signed_belt_sphere
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ x, g' x = e (g x)) ∧
        D.IsTransverseBeltSphere hf hdim hindex g' ∧
        D.beltIntersectionPoints 2 g' ⊆ D.beltIntersectionPoints 2 g ∧
        (∀ x ∈ D.beltIntersectionPoints 2 g',
          (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
        (∀ hfin' : (D.beltIntersectionPoints 2 g').Finite,
          D.beltIntersectionCount 2 r g' hfin' = D.beltIntersectionCount 2 r g
            (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)) ∧
        (D.beltIntersectionPoints 2 g').ncard =
          (D.beltIntersectionCount 2 r g
            (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let hfin := D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood
  obtain ⟨e, g', P', hiso, heq, hgood', hP', hsub, hgerm, hsum, hno⟩ :=
    D.exists_finite_belt_reduction hf hdim hindex hnull r hfin.toFinset g
      hfin.coe_toFinset hgood
  have hunit : ∀ x ∈ P', D.beltIntersectionSign 2 r g' x = 1 ∨
      D.beltIntersectionSign 2 r g' x = -1 := by
    obtain ⟨hg', _, _, ht'⟩ := hgood'
    intro x hx
    exact D.beltIntersectionSign_unit hf 3 2 hindex r g' hg' ht' x (hP' ▸ hx)
  have hmem (x : Hemisphere.Sphere 2) (hx : x ∈ D.beltIntersectionPoints 2 g') : x ∈ P' := by
    change x ∈ (P' : Set (Hemisphere.Sphere 2))
    rw [hP']
    exact hx
  refine ⟨e, g', hiso, heq, hgood', ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxP : x ∈ P' := hmem x hx
    exact hfin.mem_toFinset.mp (hsub hxP)
  · intro x hx
    exact hgerm x (hmem x hx)
  · intro hfin'
    have hPfin : hfin'.toFinset = P' := by
      apply Finset.coe_injective
      exact hfin'.coe_toFinset.trans hP'.symm
    change (∑ x ∈ hfin'.toFinset, (D.beltIntersectionSign 2 r g' x : ℤ)) = _
    rw [hPfin]
    exact hsum
  · calc
      (D.beltIntersectionPoints 2 g').ncard = P'.card := by
        rw [← hP', Set.ncard_coe_finset]
      _ = (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)).natAbs :=
        FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite P'
          (D.beltIntersectionSign 2 r g') hunit hno
      _ = _ := congrArg Int.natAbs hsum

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
