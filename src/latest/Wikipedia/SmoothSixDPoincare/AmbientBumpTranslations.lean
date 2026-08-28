import Wikipedia.SmoothSixDPoincare.SupportedDiffeomorphFamily
import Wikipedia.SmoothSixDPoincare.BumpTranslationDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Smooth vector-parameter families of actual ambient bump diffeomorphisms

Coordinate translation by a compactly supported cutoff is extended to the
original manifold. All sufficiently small parameters give genuine ambient
diffeomorphisms. The same explicit maps are jointly smooth in parameter
and point, including across the chart boundary.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)

/-- The original ambient map, defined by actual supported coordinate conjugation. -/
def bumpFamily (β : E → ℝ) (p : E × M) : M :=
  extendMap Φ (fun x => x + β x • p.1) p.2

theorem bumpFamily_zero (β : E → ℝ) (y : M) : bumpFamily Φ β (0, y) = y := by
  have heq : (fun x : E => x + β x • (0 : E)) = id := by funext x; simp
  change extendMap Φ (fun x => x + β x • (0 : E)) y = y
  rw [heq]
  exact extendMap_id Φ y

theorem bumpFamily_chart (β : E → ℝ) (a : E) {x : E} (hx : x ∈ Φ.source) :
    bumpFamily Φ β (a, Φ x) = Φ (x + β x • a) :=
  extendMap_chart Φ _ hx

theorem bumpFamily_mem_target (β : E → ℝ) (a : E)
    (hsource : MapsTo (fun x => x + β x • a) Φ.source Φ.source)
    {y : M} (hy : y ∈ Φ.target) : bumpFamily Φ β (a, y) ∈ Φ.target :=
  extendMap_mem_target Φ hsource hy

/-- The actual chart coordinates of the extended map retain the weighted translation. -/
theorem bumpFamily_coordinates (β : E → ℝ) (a : E)
    (hsource : MapsTo (fun x => x + β x • a) Φ.source Φ.source)
    {y : M} (hy : y ∈ Φ.target) :
    Φ.symm (bumpFamily Φ β (a, y)) = Φ.symm y + β (Φ.symm y) • a := by
  change Φ.symm (extendMap Φ (fun x => x + β x • a) y) = _
  rw [extendMap_of_mem Φ _ hy]
  exact Φ.left_inv' (hsource (Φ.map_target' hy))

theorem bumpFamily_fixed_outside (β : E → ℝ) (a : E) {y : M}
    (hy : y ∉ Φ '' tsupport β) : bumpFamily Φ β (a, y) = y := by
  apply extendMap_eq_of_notMem_image Φ (K := tsupport β) _ hy
  intro x hx
  have hzero : β x = 0 := by
    by_contra hn
    exact hx (subset_tsupport β hn)
  simp only [hzero, zero_smul, add_zero]

variable [FiniteDimensional ℝ E] [T2Space M]

/-- A single radius gives actual diffeomorphisms and joint smoothness of the explicit family. -/
theorem exists_radius_ambient_bumpFamily {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ a : E, ‖a‖ < ε → ∃ D : Diffeomorph J J M M ∞,
        ∀ y, D y = bumpFamily Φ β (a, y)) ∧
      (∀ p : E × M, ‖p.1‖ < ε →
        ContMDiffAt (𝓘(ℝ, E).prod J) J ∞ (bumpFamily Φ β) p) ∧
      ∀ a : E, ‖a‖ < ε → MapsTo (fun x => x + β x • a) Φ.source Φ.source := by
  obtain ⟨ε, hε, hsmall⟩ := SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let A : E × E → E := fun p => p.2 + β p.2 • p.1
  have hA : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hβ.contMDiff.comp contMDiff_snd).smul contMDiff_fst)
  have hfix : ∀ a x, x ∉ tsupport β → A (a, x) = x := by
    intro a x hx
    have hzero : β x = 0 := by
      by_contra hn
      exact hx (subset_tsupport β hn)
    simp only [A, hzero, zero_smul, add_zero]
  have hsource (a : E) (ha : ‖a‖ < ε) : MapsTo (fun x => A (a, x)) Φ.source Φ.source := by
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    have heq : (fun x => A (a, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupport hdfix
  refine ⟨ε, hε, ?_, ?_, hsource⟩
  · intro a ha
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    refine ⟨extension Φ d hcompact.isCompact hsupport hdfix, ?_⟩
    intro y
    change extendMap Φ d y = extendMap Φ (fun x => x + β x • a) y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext hd)
  · intro p hp
    exact contMDiffAt_extendFamily Φ hA hcompact.isCompact hsupport hfix (hsource p.1 hp)

variable {X : Type*} [TopologicalSpace X]

/-- Compact target-open constraints persist under the actual ambient family. -/
theorem eventually_bumpFamily_maps_compact_into_open {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) {f : X → M} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) {O : Set M} (hO : IsOpen O) (hmap : MapsTo f C O) :
    ∀ᶠ a in 𝓝 (0 : E), MapsTo (fun x => bumpFamily Φ β (a, f x)) C O := by
  obtain ⟨δ, hδ, -, hsmooth, -⟩ := exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  apply hC.eventually_forall_of_forall_eventually
  intro x hx
  have hpair : ContinuousAt (fun p : E × X => (p.1, f p.2)) (0, x) :=
    (continuous_fst.prodMk (hf.comp continuous_snd)).continuousAt
  have hbase : ContinuousAt (bumpFamily Φ β) (0, f x) :=
    (hsmooth (0, f x) (by simpa only [norm_zero] using hδ)).continuousAt
  have hfamily : ContinuousAt (fun p : E × X => bumpFamily Φ β (p.1, f p.2)) (0, x) :=
    ContinuousAt.comp (g := bumpFamily Φ β) (f := fun p : E × X => (p.1, f p.2)) hbase hpair
  apply hfamily.preimage_mem_nhds
  apply hO.mem_nhds
  rw [bumpFamily_zero]
  exact hmap hx

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
