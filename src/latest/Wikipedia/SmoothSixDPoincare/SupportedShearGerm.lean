import Wikipedia.SmoothSixDPoincare.NormalPreservingBumpIsotopy
import Wikipedia.SmoothSixDPoincare.SmallSupportedGerm
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphProduct
import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-!
# A compactly supported realization of a linear shear germ

The transverse parameter is retained exactly. A small supported extension
of its linear displacement, combined with a cutoff in the first coordinate,
realizes the shear near zero inside any prescribed open neighborhood. Every
time slice is a native diffeomorphism, and the entire core is fixed.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A prescribed shear has a supported smooth isotopy realizing its full germ. -/
theorem exists_supported_shear_isotopy (L : F →L[ℝ] E)
    {U : Set (E × F)} (hU : IsOpen U) (hzero : (0 : E × F) ∈ U) :
    ∃ (A : ℝ × (E × F) → E × F) (K : Set (E × F)),
      IsCompact K ∧ K ⊆ U ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A ∧
      (∀ p, A (0, p) = p) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞,
        ∀ p, D p = A (t, p)) ∧
      (∀ t p, p ∉ K → A (t, p) = p) ∧
      (∀ t p, (A (t, p)).2 = p.2) ∧
      (∀ t x, A (t, (x, (0 : F))) = (x, 0)) ∧
      (fun p => A (1, p)) =ᶠ[𝓝 (0 : E × F)] (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, -⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : E)}) isCompact_singleton isOpen_ball
      (singleton_subset_iff.mpr (mem_ball_self hρ))
  let Φ := (Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph
  obtain ⟨ε, hε, hfamily⟩ := exists_radius_normalBumpFamily (P := F) Φ hβ hβcompact
    (show tsupport β ⊆ Φ.source from subset_univ _)
  obtain ⟨b, hb, hbcompact, hbsupport, hbsmall, hbeq, hbzero⟩ :=
    exists_small_supported_germ isOpen_ball (mem_ball_self hρ)
      (show ContDiffOn ℝ ∞ (fun y : F => -(L y)) (ball 0 ρ) from
        L.contDiff.neg.contDiffOn)
      (show -(L (0 : F)) = 0 by simp) hε
  obtain ⟨hAprod, hdiffprod, hK⟩ := hfamily b hb hbcompact hbsmall
  let A := normalBumpFamily Φ β b
  let K : Set (E × F) := (Φ '' tsupport β) ×ˢ tsupport b
  let V := PartialChart.vectorProduct E F
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A :=
    V.symm.contMDiff.comp (hAprod.comp
      (contMDiff_fst.prodMk (V.contMDiff.comp contMDiff_snd)))
  have hdiff (t : ℝ) : ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F)
      (E × F) (E × F) ∞, ∀ p, D p = A (t, p) := by
    obtain ⟨D, hD⟩ := hdiffprod t
    exact ⟨(V.trans D).trans V.symm, hD⟩
  have hKU : K ⊆ U := by
    rintro ⟨x, y⟩ ⟨⟨w, hw, rfl⟩, hy⟩
    apply hρU
    change (w, y) ∈ ball (0 : E × F) ρ
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨mem_ball_zero_iff.mp (hβsupport hw), mem_ball_zero_iff.mp (hbsupport hy)⟩
  have hplateau : ∀ᶠ x in 𝓝 (0 : E), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (mem_singleton (0 : E)))
  have hfirst : ∀ᶠ p in 𝓝 (0 : E × F), β p.1 = 1 :=
    (continuous_fst.tendsto (0 : E × F)) hplateau
  have hsecond : ∀ᶠ p in 𝓝 (0 : E × F), b p.2 = -(L p.2) :=
    (continuous_snd.tendsto (0 : E × F)) hbeq
  refine ⟨A, K, hK, hKU, hA, normalBumpFamily_zero Φ β b, hdiff,
    normalBumpFamily_fixed_outside Φ β b, normalBumpFamily_normal Φ β b,
    fun t x => normalBumpFamily_fixed_fiber Φ β b hbzero t x, ?_⟩
  filter_upwards [hfirst, hsecond] with p hp₁ hp₂
  have hh := normalBumpFamily_chart Φ β b (show p.1 ∈ Φ.source from mem_univ _) p.2
  change A (1, p) = (p.1 - β p.1 • b p.2, p.2) at hh
  rwa [hp₁, one_smul, hp₂, sub_neg_eq_add] at hh

/-- The endpoint is a supported native diffeomorphism with the exact prescribed shear germ. -/
theorem exists_supported_shear_diffeomorph (L : F →L[ℝ] E)
    {U : Set (E × F)} (hU : IsOpen U) (hzero : (0 : E × F) ∈ U) :
    ∃ (D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞) (K : Set (E × F)),
      IsCompact K ∧ K ⊆ U ∧ IsotopicToIdentity D ∧
      (∀ p ∉ K, D p = p) ∧ (∀ p, (D p).2 = p.2) ∧
      (∀ x, D (x, (0 : F)) = (x, 0)) ∧
      (D : (E × F) → (E × F)) =ᶠ[𝓝 (0 : E × F)] (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hsecond, hcore, hgerm⟩ :=
    exists_supported_shear_isotopy L hU hzero
  obtain ⟨D, hD⟩ := hdiff 1
  refine ⟨D, K, hK, hKU, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨A, hA, hA₀, fun p => (hD p).symm, fun t => by
      obtain ⟨d, hd⟩ := hdiff t
      exact ⟨d, fun p => (hd p).symm⟩⟩
  · intro p hp
    exact (hD p).trans (hfix 1 p hp)
  · intro p
    rw [hD, hsecond]
  · intro x
    rw [hD, hcore]
  · filter_upwards [hgerm] with p hp
    exact (hD p).trans hp

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
