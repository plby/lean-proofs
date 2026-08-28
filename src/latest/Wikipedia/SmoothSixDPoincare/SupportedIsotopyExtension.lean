import Wikipedia.SmoothSixDPoincare.SupportedDiffeomorphFamily

/-! # Extend a uniformly compactly supported native isotopy through a partial chart -/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
  (Φ : PartialDiffeomorph I J X Y ∞)

/-- Joint smoothness, genuine slice inverses, exact chart action, and compact support all extend. -/
theorem exists_supported_isotopy_extension {A : ℝ × X → X}
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    (hA₀ : ∀ x, A (0, x) = x)
    (hdiff : ∀ t, ∃ D : Diffeomorph I I X X ∞, ∀ x, D x = A (t, x))
    {K : Set X} (hK : IsCompact K) (hKsource : K ⊆ Φ.source)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) :
    ∃ (B : ℝ × Y → Y) (L : Set Y),
      IsCompact L ∧ L ⊆ Φ.target ∧ ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B ∧
      (∀ y, B (0, y) = y) ∧
      (∀ t, ∃ D : Diffeomorph J J Y Y ∞, ∀ y, D y = B (t, y)) ∧
      (∀ t y, y ∉ L → B (t, y) = y) ∧
      (∀ t, MapsTo (fun x => A (t, x)) Φ.source Φ.source) ∧
      ∀ t x, x ∈ Φ.source → B (t, Φ x) = Φ (A (t, x)) := by
  have hsource : ∀ t, MapsTo (fun x => A (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    have heq : (fun x => A (t, x)) = D := funext (fun x => (hD x).symm)
    rw [heq]
    exact mapsTo_source Φ D.toEquiv hKsource hDfix
  let B : ℝ × Y → Y := fun q => extendMap Φ (fun x => A (q.1, x)) q.2
  refine ⟨B, Φ '' K,
    hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKsource),
    ?_, contMDiff_extendFamily Φ hA hK hKsource hfix hsource, ?_, ?_, ?_, hsource, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source' (hKsource hx)
  · intro y
    have heq : (fun x => A (0, x)) = id := funext hA₀
    change extendMap Φ (fun x => A (0, x)) y = y
    rw [heq]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨D, hD⟩ := hdiff t
    have hDfix : ∀ x ∉ K, D x = x := fun x hx => (hD x).trans (hfix t x hx)
    refine ⟨extension Φ D hK hKsource hDfix, ?_⟩
    intro y
    exact congrArg (fun f : X → X => extendMap Φ f y) (funext hD)
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro t x hx
    exact extendMap_chart Φ (fun z => A (t, z)) hx

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
