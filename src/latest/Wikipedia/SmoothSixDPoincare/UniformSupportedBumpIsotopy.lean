import Wikipedia.SmoothSixDPoincare.SupportedBumpIsotopy
import Wikipedia.SmoothSixDPoincare.UniformBumpTranslation

/-!
# Uniform supported native isotopies for every spatial time slice

One positive displacement bound works for the whole jointly smooth compact
family. Every step is an actual smooth family of native diffeomorphisms with
the exact endpoint formula, and is supported in its genuine slice support.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)

/-- Construct all small native motions with one uniform displacement radius. -/
theorem exists_uniform_supported_bump_isotopy {β : ℝ × E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Prod.snd ⁻¹' Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, ∀ a : E, ‖a‖ < ε →
      ∃ A : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
        (∀ y, A (0, y) = y) ∧
        (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
        (∀ t y, y ∉ Φ '' tsupport (fun x : E => β (s, x)) → A (t, y) = y) ∧
        ∀ x ∈ Φ.source, A (1, Φ x) = Φ (x + β (s, x) • a) := by
  obtain ⟨ε, hε, hsmall⟩ := SmallPerturbation.exists_uniform_radius_bumpTranslation hs hcompact
  refine ⟨ε, hε, ?_⟩
  intro s a ha
  let βs : E → ℝ := fun x => β (s, x)
  have hslice : ContDiff ℝ ∞ βs := hs.comp (contDiff_const.prodMk contDiff_id)
  have hcompactSlice : HasCompactSupport βs := SmallPerturbation.hasCompactSupport_slice hcompact s
  have hsupportSlice : tsupport βs ⊆ Φ.source := by
    intro x hx
    exact hsupport (SmallPerturbation.tsupport_slice_subset β s hx)
  let B : ℝ × E → E := fun p => p.2 + βs p.2 • (Real.smoothTransition p.1 • a)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ B :=
    contMDiff_snd.add ((hslice.contMDiff.comp contMDiff_snd).smul
      ((hθ.comp contMDiff_fst).smul contMDiff_const))
  have hmodel : ∀ t : ℝ, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x, d x = B (t, x)) ∧ ∀ x ∉ tsupport βs, d x = x := by
    intro t
    have hnorm : ‖Real.smoothTransition t • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact mul_le_of_le_one_left (norm_nonneg a) (Real.smoothTransition.le_one t)
    exact hsmall s (Real.smoothTransition t • a) (hnorm.trans_lt ha)
  have hfix : ∀ t x, x ∉ tsupport βs → B (t, x) = x := by
    intro t x hx
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    exact (hd x).symm.trans (hdfix x hx)
  have hsource : ∀ t, MapsTo (fun x => B (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    have heq : (fun x => B (t, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupportSlice hdfix
  let A : ℝ × M → M := fun p => extendMap Φ (fun x => B (p.1, x)) p.2
  refine ⟨A, contMDiff_extendFamily Φ hB hcompactSlice.isCompact hsupportSlice hfix hsource,
    ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun x => B (0, x)) = id := by
      funext x
      simp only [B, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero, id_eq]
    change extendMap Φ (fun x => B (0, x)) y = y
    rw [hzero]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    refine ⟨extension Φ d hcompactSlice.isCompact hsupportSlice hdfix, ?_⟩
    intro y
    change extendMap Φ (fun x => B (t, x)) y = extendMap Φ d y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext (fun x => (hd x).symm))
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro x hx
    change extendMap Φ (fun y => B (1, y)) (Φ x) = _
    rw [extendMap_chart Φ (fun y => B (1, y)) hx]
    simp only [B, βs, Real.smoothTransition.one, one_smul]

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
