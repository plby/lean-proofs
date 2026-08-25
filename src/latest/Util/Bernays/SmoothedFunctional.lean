import Util.Bernays.SquareSeriesSmoothing

/-!
# Uniform bounds for the smoothed Dirichlet functional
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

noncomputable def logarithmicKernel (x : ℝ) (n : ℕ) : ℝ :=
  (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)) ^ 2)⁻¹

noncomputable def logarithmicKernelMass (a : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ / n * logarithmicKernel x n

noncomputable def dirichletTwist (a : ℕ → ℂ) (δ : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * LSeries.term a (1 + δ) n

noncomputable def smoothedSeries (a : ℕ → ℂ) (ψ : ℝ → ℂ) (δ : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term a (1 + δ) n *
    𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ)))

theorem dirichletTwist_div (a : ℕ → ℂ) (δ : ℝ) (n : ℕ) :
    dirichletTwist a δ n / (n : ℂ) = LSeries.term a (1 + δ) n := by
  by_cases hn : n = 0
  · simp [hn, dirichletTwist]
  · exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

theorem dirichletTwist_norm_le (a : ℕ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ‖dirichletTwist a δ n‖ ≤ ‖a n‖ := by
  by_cases hn : n = 0
  · simp [hn, dirichletTwist]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [dirichletTwist, norm_mul, Complex.norm_natCast, norm_term_eq_nterm_re]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, nterm, if_neg hn]
  rw [Real.rpow_add hnR, Real.rpow_one]
  have hcancel : (n : ℝ) * (‖a n‖ / ((n : ℝ) * (n : ℝ) ^ δ)) = ‖a n‖ / (n : ℝ) ^ δ := by
    field_simp
  rw [hcancel]
  exact div_le_self (norm_nonneg _) (Real.one_le_rpow hn₁ hδ)

theorem dirichletTwist_cheby {a : ℕ → ℂ} (ha : cheby a) {δ : ℝ} (hδ : 0 ≤ δ) :
    cheby (dirichletTwist a δ) := by
  obtain ⟨C, hC⟩ := ha
  refine ⟨C, fun N => ?_⟩
  apply (Finset.sum_le_sum (fun n _ => dirichletTwist_norm_le a hδ n)).trans (hC N)

theorem logarithmicKernelMass_summable {a : ℕ → ℂ} (ha : cheby a) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖a n‖ / n * logarithmicKernel x n) := by
  simpa only [logarithmicKernel, Complex.ofReal_one, Complex.one_re, Real.rpow_one, one_div] using
    limiting_fourier_lim1_aux ha hx 1 (zero_le_one' ℝ)

theorem logarithmicKernelMass_mono {a b : ℕ → ℂ} (ha : cheby a) (hb : cheby b)
    (hab : ∀ n : ℕ, ‖a n‖ ≤ ‖b n‖) {x : ℝ} (hx : 0 < x) :
    logarithmicKernelMass a x ≤ logarithmicKernelMass b x := by
  apply Summable.tsum_mono (logarithmicKernelMass_summable ha hx)
    (logarithmicKernelMass_summable hb hx)
  intro n
  apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hab n) (Nat.cast_nonneg _))
  exact inv_nonneg.mpr (by positivity)

theorem smoothedSeries_eq_twist (a : ℕ → ℂ) (ψ : ℝ → ℂ) (δ : ℝ) :
    smoothedSeries a ψ δ = ∑' n : ℕ, dirichletTwist a δ n / n *
      𝓕 ψ (1 / (2 * Real.pi) * Real.log ((n : ℝ) / Real.exp (1 / δ))) := by
  unfold smoothedSeries
  simp only [dirichletTwist_div]

theorem smoothedSeries_norm_le {a : ℕ → ℂ} (ha : cheby a) (ψ : W21) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖smoothedSeries a ψ δ‖ ≤ W21.norm ψ * logarithmicKernelMass a (Real.exp (1 / δ)) := by
  rw [smoothedSeries_eq_twist]
  have ht := dirichletTwist_cheby ha hδ
  have hbound := bound_I1 (Real.exp (1 / δ)) (Real.exp_pos _) ψ ht
  change _ ≤ W21.norm ψ * logarithmicKernelMass (dirichletTwist a δ) (Real.exp (1 / δ)) at hbound
  apply hbound.trans
  exact mul_le_mul_of_nonneg_left (logarithmicKernelMass_mono ht ha
    (dirichletTwist_norm_le a hδ) (Real.exp_pos _)) W21.norm_nonneg

theorem smoothedSeries_sub {a : ℕ → ℂ} (ha : cheby a) (ψ φ : W21) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothedSeries a (ψ - φ) δ = smoothedSeries a ψ δ - smoothedSeries a φ δ := by
  rw [smoothedSeries_eq_twist, smoothedSeries_eq_twist, smoothedSeries_eq_twist]
  have ht := dirichletTwist_cheby ha hδ
  have hs₁ := (summable_fourier (Real.exp (1 / δ)) (Real.exp_pos _) ψ ht).of_norm
  have hs₂ := (summable_fourier (Real.exp (1 / δ)) (Real.exp_pos _) φ ht).of_norm
  rw [← hs₁.tsum_sub hs₂]
  apply tsum_congr
  intro n
  simp only [Pi.sub_def]
  rw [F_sub ψ.hf φ.hf, mul_sub]

end Bernays
