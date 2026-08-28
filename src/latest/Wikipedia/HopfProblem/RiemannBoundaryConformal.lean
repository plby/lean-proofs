import Wikipedia.HopfProblem.RiemannBoundaryExtension
import Wikipedia.HopfProblem.RiemannBoundaryNoncritical

/-!
# Noncritical boundary extension with the actual side correspondence

The analytic extension of a disc uniformization is conformal at a straight
boundary coordinate. Its interior-disc side is precisely the original upper
half-neighborhood. This supplies the local correspondence needed to recover
the inverse uniformization at a boundary point.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- Reflection and the strict interior-disc bound identify the side of
the boundary, without an assumed boundary inverse. -/
theorem norm_lt_one_iff_im_pos_eventually {H k : ℂ → ℂ} {x : ℝ}
    (hH : ContinuousAt H (x : ℂ)) (hcenter : ‖H (x : ℂ)‖ = 1)
    (hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖k z‖ < 1)
    (hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = k z)
    (hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 → H z = (conj (k (conj z)))⁻¹)
    (hr : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1) :
    ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  have hcenter0 : H (x : ℂ) ≠ 0 := by
    intro hzero
    simp [hzero] at hcenter
  have hnz := hH.eventually_ne hcenter0
  have hconj : Tendsto (conj : ℂ → ℂ) (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) := by
    simpa only [conj_ofReal] using continuous_conj.tendsto (x : ℂ)
  have hkc := hconj.eventually hk
  filter_upwards [hk, hu, hl, hr, hnz, hkc] with z hzk hzu hzl hzr hzne hzconj
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hw : ‖k (conj z)‖ < 1 := hzconj (by simpa using hneg)
    have hw0 : k (conj z) ≠ 0 := by
      intro heq
      apply hzne
      rw [hzl hneg, heq]
      simp
    have hlarge : 1 < ‖H z‖ := by
      rw [hzl hneg, norm_inv, norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hw
    exact iff_of_false (not_lt_of_ge hlarge.le) (not_lt_of_ge hneg.le)
  · rw [hzr hzero]
    simp only [lt_self_iff_false, hzero]
  · rw [hzu hpos]
    exact iff_of_true (hzk hpos) hpos

/-- The extension from a modulus limit is noncritical and has precisely
the upper interior side when the original map takes values strictly inside
the unit disc. -/
theorem exists_conformal_extension_of_modulus_one
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U)
    (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod : ∀ t : ℝ, (t : ℂ) ∈ U →
      Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1))
    (hdisc : ∀ z ∈ U ∩ {z : ℂ | 0 < z.im}, ‖f z‖ < 1) :
    ∃ r > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (x : ℂ) r) ∧
      EqOn H f (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn H (fun z => (conj (f (conj z)))⁻¹)
        (ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
      HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
      deriv H (x : ℂ) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨r, hr, H, hHa, hHe, hHl, hHc⟩ :=
    exists_analytic_extension_of_modulus_one hU hx hf hmod
  have hHx := hHa (x : ℂ) (mem_ball_self hr)
  have hcenter := hHc x (mem_ball_self hr)
  have hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖f z‖ < 1 := by
    filter_upwards [hU.mem_nhds hx] with z hz hpos
    exact hdisc z ⟨hz, hpos⟩
  have hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = f z := by
    filter_upwards [ball_mem_nhds (x : ℂ) hr] with z hz hpos
    exact hHe ⟨hz, hpos⟩
  have hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 →
      H z = (conj (f (conj z)))⁻¹ := by
    filter_upwards [ball_mem_nhds (x : ℂ) hr] with z hz hneg
    exact hHl ⟨hz, hneg⟩
  have hreal : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1 := by
    filter_upwards [ball_mem_nhds (x : ℂ) hr] with z hz hzero
    have heq : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzero.symm)
    simpa only [heq] using hHc z.re (by simpa only [heq] using hz)
  have hinside : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖H z‖ < 1 := by
    filter_upwards [hu, hk] with z heq hz hpos
    rw [heq hpos]
    exact hz hpos
  have hnonzero := RiemannMapping.deriv_ne_zero_of_upper_halfPlane_to_unitDisc hHx
    (by simp) hcenter hinside
  exact ⟨r, hr, H, hHa, hHe, hHl, hHc, hHx.hasStrictDerivAt, hnonzero,
    norm_lt_one_iff_im_pos_eventually hHx.continuousAt hcenter hk hu hl hreal⟩

/-- A genuine uniformization has a noncritical analytic boundary
extension in any continuous half-chart which straightens its boundary.
In addition to the exact reflected formula, this proves the actual local
interior-side correspondence. -/
theorem exists_conformal_extension_discHomeomorph_in_half_chart
    {D U : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f φ : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f D)
    (hφ : DifferentiableOn ℂ φ (U ∩ {z : ℂ | 0 < z.im}))
    (hφc : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D)
    (hout : ∀ t : ℝ, (t : ℂ) ∈ U → φ (t : ℂ) ∉ D)
    {x : ℝ} (hx : (x : ℂ) ∈ U) :
    ∃ r > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (x : ℂ) r) ∧
      EqOn H (f ∘ φ) (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn H (fun z => (conj (f (φ (conj z))))⁻¹)
        (ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
      HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
      deriv H (x : ℂ) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  apply exists_conformal_extension_of_modulus_one hU hx (hf.comp hφ hside)
  · intro t ht
    exact tendsto_norm_discHomeomorph_in_boundary_chart e he hU hφc hside ht (hout t ht)
  · intro z hz
    have hp := hside hz
    have hv := he ⟨φ z, hp⟩
    simpa only [Function.comp_def, mem_ball, dist_zero_right, ← hv] using
      (e ⟨φ z, hp⟩).property

end Wikipedia.HopfProblem.RiemannBoundary
