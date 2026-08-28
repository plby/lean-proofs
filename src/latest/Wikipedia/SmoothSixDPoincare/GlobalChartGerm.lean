import Wikipedia.SmoothSixDPoincare.RelativeGermLinearization
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Extending a chart germ into a fixed full-source chart

An invertible coordinate germ factors as its derivative followed by a global
supported diffeomorphism. Composing this factorization with a full-source
chart gives an extension of the original parametrization germ, with precisely
the same target as the full-source chart. No extension of an arbitrary disk
embedding is assumed.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PartialChart

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A prescribed native germ extends over the entire model without changing the chart target. -/
theorem exists_full_source_extension
    (Φ c : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)
    (hzero : (0 : E) ∈ Φ.source) (hcsource : c.source = univ)
    (hcenter : c 0 = Φ 0) :
    ∃ Ξ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞,
      Ξ.source = univ ∧ Ξ.target = c.target ∧
      (Ξ : E → M) =ᶠ[𝓝 (0 : E)] Φ := by
  have hc₀ : (0 : E) ∈ c.source := by rw [hcsource]; exact mem_univ _
  have ht₀ : Φ 0 ∈ c.target := hcenter ▸ c.map_source' hc₀
  let Ψ := Φ.trans c.symm
  have hΨ₀ : (0 : E) ∈ Ψ.source := ⟨hzero, ht₀⟩
  have hΨzero : Ψ (0 : E) = 0 := by
    change c.symm (Φ 0) = 0
    rw [← hcenter]
    exact c.left_inv' hc₀
  have hbij : Bijective (fderiv ℝ Ψ 0) := by
    have hb := bijective_mfderiv Ψ hΨ₀
    change Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ 0 : E →L[ℝ] E) at hb
    rwa [mfderiv_eq_fderiv] at hb
  have hfixed : ∀ x ∈ Ψ.source ∩ ((⊥ : Submodule ℝ E) : Set E), Ψ x = x := by
    intro x hx
    have hx₀ : x = 0 := hx.2
    simpa only [hx₀] using hΨzero
  obtain ⟨C, D, K, -, -, -, -, -, -, -, -, -, hgerm⟩ :=
    SmallPerturbation.exists_relative_germ_linearization Ψ.open_source hΨ₀
      Ψ.contMDiffOn_toFun.contDiffOn hΨzero hbij
      (0 : E →L[ℝ] ℝ) (fun _ _ => rfl) ⊥ hfixed
  let G := D.trans C.toDiffeomorph
  let Ξ := G.toPartialDiffeomorph.trans c
  have hsource : Ξ.source = univ := by
    ext x
    change (x ∈ (univ : Set E) ∧ G x ∈ c.source) ↔ x ∈ univ
    simp only [hcsource, mem_univ, and_self]
  have htarget : Ξ.target = c.target := by
    ext x
    change (x ∈ c.target ∧ c.symm x ∈ (univ : Set E)) ↔ x ∈ c.target
    simp only [mem_univ, and_true]
  refine ⟨Ξ, hsource, htarget, ?_⟩
  filter_upwards [hgerm, Ψ.open_source.mem_nhds hΨ₀] with x hx hxs
  change c (C (D x)) = Φ x
  rw [← hx]
  exact c.right_inv' hxs.2

end Wikipedia.SmoothSixDPoincare.PartialChart
