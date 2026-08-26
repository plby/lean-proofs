import ErdosProblems.Erdos67b.MRAuxiliaryDensity
import ErdosProblems.Erdos67b.MRAuxiliarySchedule
import ErdosProblems.Erdos67b.MRAuxiliaryMissingEnergy

/-!
# Vanishing missing-prime error at the original MR auxiliary scale

The finite beta-sieve remainder is paid at the actual moving interval.
All thresholds precede the original typical family and the coefficient.
These are arithmetic error estimates, not the exceptional prime energy.
-/

open Filter MeasureTheory
open scoped Topology Interval

namespace Erdos67b

noncomputable section

def mrSourceAuxiliaryInterval (X : ℕ) : ℕ × ℕ :=
  mrLogPrimeInterval (mrAuxiliaryLogLower (Real.log (X : ℝ)))
    (mrAuxiliaryLogUpper (Real.log (X : ℝ)))

theorem mrExists_sourceAuxiliary_missing_density_small
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      ((missingPrimeBlockSet (mrSourceAuxiliaryInterval X) (2 * X)).card : ℝ) / X ≤ epsilon := by
  obtain ⟨C, hC, S, hS, hfinite⟩ := mrExists_auxiliaryMissing_normalized_density_bound
  have hratio := mrTendsto_auxiliary_log_ratio.comp EulerSubpower.tendsto_log_nat_atTop
  have hhalf := Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    EulerSubpower.tendsto_log_nat_atTop
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf
  have herr : Tendsto (fun X : ℕ ↦
      2 * C * (mrAuxiliaryLogLower (Real.log (X : ℝ)) /
        mrAuxiliaryLogUpper (Real.log (X : ℝ))) + Real.exp (-Real.log (X : ℝ) / 2))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, zero_add, neg_div] using
      (hratio.const_mul (2 * C)).add hexp
  have hsmall := (tendsto_order.1 herr).2 epsilon hepsilon
  have hloglog := Real.tendsto_log_atTop.comp EulerSubpower.tendsto_log_nat_atTop
  have hall : ∀ᶠ X : ℕ in atTop,
      1 ≤ X ∧ ((missingPrimeBlockSet (mrSourceAuxiliaryInterval X) (2 * X)).card : ℝ) / X ≤
        epsilon := by
    filter_upwards [eventually_ge_atTop 1,
      EulerSubpower.tendsto_log_nat_atTop.eventually mrEventually_auxiliary_schedule,
      hloglog.eventually (eventually_ge_atTop (4 * (S : ℝ))), hsmall]
      with X hX hschedule hLL herror
    obtain ⟨_, _, ha, hab, _, _⟩ := hschedule
    refine ⟨hX, ?_⟩
    have hb := hfinite (by omega : 0 < X)
      (mrAuxiliaryLogLower (Real.log (X : ℝ)))
      (mrAuxiliaryLogUpper (Real.log (X : ℝ))) (by linarith) hab le_rfl hLL
    exact hb.trans herror.le
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hall
  refine ⟨max X₁ 1, le_max_right _ _, ?_⟩
  intro X hX
  exact (hX₁ X ((le_max_left _ _).trans hX)).2

theorem mrExists_sourceAuxiliary_missing_energy_small
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      ∀ (blocks : Finset (ℕ × ℕ)) {f : ℕ → ℂ},
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → ∀ {T : ℝ}, 0 ≤ T →
        (∫ t in -T..T,
          ‖mrAuxiliaryMissingPolynomial blocks (mrSourceAuxiliaryInterval X) f X t‖ ^ 2) ≤
            epsilon * (T / X + 1) := by
  let delta := epsilon / (4 * (1 + Real.pi))
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  obtain ⟨X₀, hX₀, hdensity⟩ := mrExists_sourceAuxiliary_missing_density_small hdelta
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX blocks f hbound T hT
  have hXpos : 0 < X := lt_of_lt_of_le (by omega : 0 < X₀) hX
  have hXr : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hcard := hdensity X hX
  have hmean := intervalIntegral_mrAuxiliaryMissingPolynomial_le blocks
    (mrSourceAuxiliaryInterval X) hXpos hbound hT
  have htau : 0 ≤ T / X := by positivity
  have hscalar : 2 * (T / X) + 4 * Real.pi ≤
      4 * (1 + Real.pi) * (T / X + 1) := by
    nlinarith [Real.pi_pos, mul_nonneg htau Real.pi_pos.le]
  calc
    _ ≤ (2 * T + 4 * Real.pi * X) *
        (missingPrimeBlockSet (mrSourceAuxiliaryInterval X) (2 * X)).card / (X : ℝ) ^ 2 := hmean
    _ = (2 * (T / X) + 4 * Real.pi) *
        ((missingPrimeBlockSet (mrSourceAuxiliaryInterval X) (2 * X)).card / X) := by
      field_simp
    _ ≤ (4 * (1 + Real.pi) * (T / X + 1)) * delta :=
      mul_le_mul hscalar hcard (by positivity) (by positivity)
    _ = epsilon * (T / X + 1) := by
      dsimp only [delta]
      have hne : 4 * (1 + Real.pi) ≠ 0 := by positivity
      field_simp

end

end Erdos67b
