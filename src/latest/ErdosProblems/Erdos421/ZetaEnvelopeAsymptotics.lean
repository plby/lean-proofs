import ErdosProblems.Erdos421.ZetaEnvelopePower

/-! # Choosing the amplitude and radius in the zero detector -/

namespace Erdos421

open Filter Topology

noncomputable def zetaDetectionAmplitude (r : ℕ) (R T : ℝ) : ℝ :=
  2 * (R / ((r : ℝ) + 1)) * Real.log T

noncomputable def zetaDetectionRadius (r : ℕ) (R B T : ℝ) : ℝ :=
  R / (100 * (zetaDetectionAmplitude r R T + B * R + 1))

theorem zetaDetectionAmplitude_tendsto_atTop (r : ℕ) {R : ℝ} (hR : 0 < R) :
    Tendsto (zetaDetectionAmplitude r R) atTop atTop := by
  exact Tendsto.const_mul_atTop (by positivity : 0 < 2 * (R / ((r : ℝ) + 1)))
    Real.tendsto_log_atTop

theorem zetaDetectionRadius_tendsto_zero (r : ℕ) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B) :
    Tendsto (zetaDetectionRadius r R B) atTop (𝓝 0) := by
  have ha := zetaDetectionAmplitude_tendsto_atTop r hR
  have hden : Tendsto (fun T ↦ 100 * (zetaDetectionAmplitude r R T + B * R + 1))
      atTop atTop := by
    apply tendsto_atTop_mono _ (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 100) ha)
    intro T
    nlinarith only [mul_nonneg hB hR.le]
  exact hden.const_div_atTop R

theorem zetaStripEnvelope_exp_bound_eventually (r K : ℕ) {R B : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop,
      zetaStripEnvelope r K R (2 * T + R) * (1 + 1 / zetaDetectionRadius r R B T) ≤
        Real.exp (zetaDetectionAmplitude r R T) := by
  let α := R / ((r : ℝ) + 1)
  let C₁ : ℝ := 131072 * K * ((2 ^ r : ℕ) : ℝ) + 64
  let C₂ : ℝ := 1 + 100 * (2 * α + B * R + 1) / R
  have hα : 0 < α := by dsimp only [α]; positivity
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp only [C₂]; positivity
  have hlim := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hα).tendsto_div_nhds_zero).const_mul
    (C₁ * C₂)
  simp only [Real.rpow_two, mul_zero] at hlim
  have hsmall : ∀ᶠ T : ℝ in atTop, C₁ * C₂ * Real.log T ^ 2 / T ^ α ≤ 1 := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with T hT
    simpa only [mul_div_assoc] using hT.le
  have hlogs : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hsmall, eventually_ge_atTop (3 : ℝ), hlogs] with T hsmall hT hlog
  have hTp : 0 < T := by linarith
  have hpow : 0 < T ^ α := Real.rpow_pos_of_pos hTp α
  have hpoly : C₁ * C₂ * Real.log T ^ 2 ≤ T ^ α := (div_le_one hpow).mp hsmall
  have hA : 0 < zetaDetectionAmplitude r R T := by
    change 0 < 2 * α * Real.log T
    positivity
  have hu : 0 < zetaDetectionRadius r R B T := by
    unfold zetaDetectionRadius
    positivity
  have hQ : 1 + 1 / zetaDetectionRadius r R B T =
      1 + 100 * (2 * α * Real.log T + B * R + 1) / R := by
    unfold zetaDetectionRadius zetaDetectionAmplitude
    rw [one_div_div]
  have hQbound : 1 + 1 / zetaDetectionRadius r R B T ≤ C₂ * Real.log T := by
    rw [hQ]
    have hc : 0 ≤ 1 + 100 * (B * R + 1) / R := by positivity
    have hm := le_mul_of_one_le_right hc hlog
    calc
      _ = (200 * α / R) * Real.log T + (1 + 100 * (B * R + 1) / R) := by ring
      _ ≤ (200 * α / R) * Real.log T +
          (1 + 100 * (B * R + 1) / R) * Real.log T := add_le_add le_rfl hm
      _ = C₂ * Real.log T := by dsimp only [C₂]; ring
  have henv := zetaStripEnvelope_dilated_bound r K hR.le hR1 hT hlog
  have hexp : T ^ α * T ^ α = Real.exp (zetaDetectionAmplitude r R T) := by
    rw [← Real.rpow_add hTp, Real.rpow_def_of_pos hTp]
    congr 1
    unfold zetaDetectionAmplitude
    dsimp only [α]
    ring
  calc
    _ ≤ (C₁ * T ^ α * Real.log T) * (C₂ * Real.log T) :=
      mul_le_mul henv hQbound (by positivity) (by positivity)
    _ = (C₁ * C₂ * Real.log T ^ 2) * T ^ α := by ring
    _ ≤ T ^ α * T ^ α := mul_le_mul_of_nonneg_right hpoly hpow.le
    _ = _ := hexp

theorem zetaDetectionRadius_log_lower_eventually (r : ℕ) {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop, ((r : ℝ) + 1) / (4000 * Real.log T) ≤
      zetaDetectionRadius r R B T / 10 := by
  have ha := zetaDetectionAmplitude_tendsto_atTop r hR
  have hlogs : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [ha.eventually (eventually_ge_atTop (B * R + 1)), hlogs] with T hA hlog
  have hlogp : 0 < Real.log T := by linarith
  have hAp : 0 < zetaDetectionAmplitude r R T := by
    unfold zetaDetectionAmplitude
    positivity
  have hden : 100 * (zetaDetectionAmplitude r R T + B * R + 1) ≤
      200 * zetaDetectionAmplitude r R T := by linarith only [hA]
  have hd := div_le_div_of_nonneg_left hR.le
    (by positivity : 0 < 100 * (zetaDetectionAmplitude r R T + B * R + 1)) hden
  have hh := div_le_div_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 10)
  have he : (R / (200 * zetaDetectionAmplitude r R T)) / 10 =
      ((r : ℝ) + 1) / (4000 * Real.log T) := by
    unfold zetaDetectionAmplitude
    have hr : (r : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rwa [he] at hh

end Erdos421
