import Util.Bernays.VerticalFourierBounds

/-!
# A quantitative Fourier decay estimate from holomorphy of the square
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

theorem verticalProduct_scaled_deriv_integral_le {f : ℂ → ℂ} {ψ : ℝ → ℂ} {δ T C : ℝ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hδ : 0 < δ) (hψ : ContDiff ℝ 1 ψ) (hsupp : tsupport ψ ⊆ Icc (-T) T)
    (hψ₀ : ∀ t : ℝ, ‖ψ t‖ ≤ C) (hψ₁ : ∀ t : ℝ, ‖deriv ψ t‖ ≤ C) :
    Real.sqrt δ * (∫ t : ℝ, ‖deriv (verticalProduct f ψ (1 + δ)) t‖) ≤
      C * ((∫ t : ℝ in Icc (-T) T, Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖) +
        ∫ t : ℝ in Icc (-T) T, Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖) := by
  let S := Icc (-T) T
  let g := verticalProduct f ψ (1 + δ)
  have hσ : 1 < 1 + δ := by linarith
  have hs : tsupport g ⊆ S := tsupport_mul_subset_right.trans hsupp
  have hzero : ∀ t : ℝ, t ∉ S → ‖deriv g t‖ = 0 := by
    intro t ht
    rw [deriv_of_notMem_tsupport (fun h => ht (hs h)), norm_zero]
  have hcut := setIntegral_eq_integral_of_forall_compl_eq_zero hzero (μ := volume)
  change Real.sqrt δ * (∫ t : ℝ, ‖deriv g t‖) ≤ _
  rw [← hcut, ← integral_const_mul]
  have hdint : IntegrableOn (fun t : ℝ => Real.sqrt δ * ‖deriv g t‖) S :=
    ((verticalProduct_deriv_continuous hf hσ hψ).norm.const_mul _).continuousOn.integrableOn_compact
      isCompact_Icc
  have h₀ : IntegrableOn (fun t : ℝ => Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖) S :=
    ((halfPlane_vertical_continuous (halfPlane_deriv_continuousOn hf) hσ).norm.const_mul
      _).continuousOn.integrableOn_compact isCompact_Icc
  have h₁ : IntegrableOn (fun t : ℝ => Real.sqrt δ * ‖f ((1 + δ : ℝ) + t * Complex.I)‖) S :=
    ((halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn hσ).norm.const_mul
      _).continuousOn.integrableOn_compact isCompact_Icc
  rw [← integral_add h₀ h₁, ← integral_const_mul]
  apply integral_mono hdint ((h₀.add h₁).const_mul C)
  intro t
  have hbound := verticalProduct_deriv_norm_le (σ := 1 + δ) (hf _ (by simpa using hσ))
    ((hψ.differentiable (by norm_num)) t) (hψ₀ t) (hψ₁ t)
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg δ)
  change Real.sqrt δ * ‖deriv g t‖ ≤ _
  dsimp only [g] at *
  simp only [Pi.add_apply]
  nlinarith

theorem halfPlane_square_verticalProduct_integral_tendsto {f F : ℂ → ℂ} {ψ : ℝ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0)
    (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Tendsto (fun δ : ℝ => Real.sqrt δ * ∫ t : ℝ, ‖deriv (verticalProduct f ψ (1 + δ)) t‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨T, _, hT⟩ := hsupp.isBounded.exists_pos_norm_le
  have hTS : tsupport ψ ⊆ Icc (-T) T := fun t ht => abs_le.mp (by simpa using hT t ht)
  obtain ⟨C₀, h₀⟩ := hψ.continuous.bounded_above_of_compact_support hsupp
  obtain ⟨C₁, h₁⟩ := hψ.continuous_deriv_one.bounded_above_of_compact_support hsupp.deriv
  let C := max C₀ C₁
  have hlim := ((halfPlane_square_scaled_deriv_integral_tendsto hf hF heq hne T).add
    (halfPlane_square_scaled_norm_integral_tendsto hf hF heq T)).const_mul C
  simp only [add_zero, mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun δ =>
    mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (fun _ => norm_nonneg _)))) _ hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact verticalProduct_scaled_deriv_integral_le hf hδ hψ hTS
    (fun t => (h₀ t).trans (le_max_left _ _)) (fun t => (h₁ t).trans (le_max_right _ _))

theorem halfPlane_square_fourier_decay {f F : ℂ → ℂ} {ψ : ℝ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2)
    (hne : ∃ z : ℂ, (1 / 2 : ℝ) < z.re ∧ F z ≠ 0)
    (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Tendsto (fun δ : ℝ => ‖𝓕 (verticalProduct f ψ (1 + δ)) (-1 / (2 * Real.pi * δ))‖ / Real.sqrt δ)
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun δ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))) _
    (halfPlane_square_verticalProduct_integral_tendsto hf hF heq hne hψ hsupp)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  have hσ : 1 < 1 + δ := by linarith
  obtain ⟨hg, hg'⟩ := verticalProduct_integrable hf hσ hψ hsupp
  have hgd : Differentiable ℝ (verticalProduct f ψ (1 + δ)) := fun t =>
    (verticalProduct_hasDerivAt (hf _ (by simpa using hσ)) ((hψ.differentiable (by norm_num)) t)).differentiableAt
  have hbound := fourier_deriv_norm_bound hg hgd hg' (-1 / (2 * Real.pi * δ))
  have hfactor : 2 * Real.pi * |(-1 : ℝ) / (2 * Real.pi * δ)| = 1 / δ := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
    field_simp
  rw [hfactor] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg δ)
  have hid : Real.sqrt δ * (1 / δ) = 1 / Real.sqrt δ := by
    have hs := Real.sq_sqrt hδ.le
    have hsp := Real.sqrt_pos.mpr hδ
    field_simp [hδ.ne', hsp.ne']
    nlinarith
  rw [← mul_assoc, hid, one_div_mul_eq_div] at hmul
  exact hmul

end Bernays
