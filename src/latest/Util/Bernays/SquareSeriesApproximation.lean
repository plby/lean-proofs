import Util.Bernays.SmoothedFunctional

/-!
# Removal of compact frequency support by Sobolev approximation
-/

open Filter Topology

namespace Bernays

theorem smoothedSeries_scaled_norm_le {a : ℕ → ℂ} (ha : cheby a) (ψ : W21)
    {δ K : ℝ} (hδ : 0 < δ)
    (hK : logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤ K) :
    ‖smoothedSeries a ψ δ‖ / Real.sqrt δ ≤ W21.norm ψ * K := by
  apply (div_le_div_of_nonneg_right (smoothedSeries_norm_le ha ψ hδ.le) (Real.sqrt_nonneg _)).trans
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hK W21.norm_nonneg

theorem smoothedSeries_scaled_sub_le {a : ℕ → ℂ} (ha : cheby a) (ψ φ : W21)
    {δ K : ℝ} (hδ : 0 < δ)
    (hK : logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤ K) :
    ‖smoothedSeries a ψ δ‖ / Real.sqrt δ ≤ W21.norm (ψ - φ) * K +
      ‖smoothedSeries a φ δ‖ / Real.sqrt δ := by
  have hnorm : ‖smoothedSeries a ψ δ‖ ≤
      ‖smoothedSeries a (ψ - φ) δ‖ + ‖smoothedSeries a φ δ‖ := by
    rw [smoothedSeries_sub ha ψ φ hδ.le]
    calc
      _ = ‖(smoothedSeries a ψ δ - smoothedSeries a φ δ) + smoothedSeries a φ δ‖ := by
        rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  apply (div_le_div_of_nonneg_right hnorm (Real.sqrt_nonneg _)).trans
  rw [add_div]
  exact add_le_add (smoothedSeries_scaled_norm_le ha (ψ - φ) hδ hK) le_rfl

theorem LSeries_square_W21_cancellation (a : ℕ → ℂ) (F : ℂ → ℂ)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (had : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries a) s)
    (hF : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s)
    (heq : ∀ s : ℂ, 1 < s.re → F s = LSeries a s ^ 2)
    (hne : ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0)
    (hcheby : cheby a) {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      logarithmicKernelMass a (Real.exp (1 / δ)) / Real.sqrt δ ≤ K) (ψ : W21) :
    Tendsto (fun δ : ℝ => ‖smoothedSeries a ψ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
  obtain g := exists_trunc
  let Ψ (R : ℝ) : CS 2 ℂ := g.scale R * ψ
  have happrox : Tendsto (fun R : ℝ => W21.norm (ψ - (Ψ R : W21))) atTop (𝓝 0) :=
    W21_approximation ψ g
  have hcompact (R : ℝ) : Tendsto
      (fun δ : ℝ => ‖smoothedSeries a (Ψ R) δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0) :=
    LSeries_square_smoothed_cancellation a F ha had hF heq hne (Ψ R)
      ((Ψ R).h1.of_le (by norm_num)) (Ψ R).h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htol : 0 < ε / (2 * (K + 1)) := by positivity
  obtain ⟨R, hR⟩ := (happrox.eventually (gt_mem_nhds htol)).exists
  have hsmall := (hcompact R).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hK, hsmall] with δ hδ hKδ hsmallδ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
  have hbound := smoothedSeries_scaled_sub_le hcheby ψ (Ψ R) hδ hKδ
  have hscale : W21.norm (ψ - (Ψ R : W21)) * K < ε / 2 := by
    have hn := W21.norm_nonneg (f := (ψ - (Ψ R : W21) : W21))
    have hprod := (lt_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp hR
    nlinarith
  change ‖smoothedSeries a (Ψ R) δ‖ / Real.sqrt δ < ε / 2 at hsmallδ
  simp only [W21.ofCS2_toFun] at hbound hscale
  exact hbound.trans_lt (by linarith)

end Bernays
