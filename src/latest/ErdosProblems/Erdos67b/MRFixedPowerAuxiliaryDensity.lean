import ErdosProblems.Erdos67b.MRAuxiliarySourceDensity

/-! # Fixed-power auxiliary density, with the ratio chosen before the exponent -/

open Filter MeasureTheory
open scoped Topology Interval

namespace Erdos67b

noncomputable section

def mrFixedPowerAuxiliaryInterval (r theta : ℝ) (X : ℕ) : ℕ × ℕ :=
  mrLogPrimeInterval (r * (theta * Real.log (X : ℝ))) (theta * Real.log (X : ℝ))

theorem mrFixedPowerAuxiliaryInterval_eq_rpow (r theta : ℝ) {X : ℕ} (hX : 0 < X) :
    mrFixedPowerAuxiliaryInterval r theta X =
      (⌈(X : ℝ) ^ (r * theta)⌉₊, ⌊(X : ℝ) ^ theta⌋₊) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  unfold mrFixedPowerAuxiliaryInterval mrLogPrimeInterval
  rw [Real.rpow_def_of_pos hXr, Real.rpow_def_of_pos hXr]
  congr 3 <;> ring

theorem mrExists_fixedPower_missing_density_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ {r theta : ℝ}, 0 < r → r ≤ 1 / 2 → 0 < theta → 4 * (S : ℝ) * theta ≤ 1 →
      ∀ {X : ℕ}, 1 < X → 2 ≤ r * (theta * Real.log (X : ℝ)) →
        ((missingPrimeBlockSet (mrFixedPowerAuxiliaryInterval r theta X) (2 * X)).card : ℝ) /
            X ≤ 2 * C * r + Real.exp (-Real.log (X : ℝ) / 2) := by
  obtain ⟨C, hC, S, hS, hfinite⟩ := mrExists_auxiliaryMissing_finite_density_bound
  refine ⟨C, hC, S, hS, ?_⟩
  intro r theta hr hrHalf htheta hcutoff X hX ha
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < theta * Real.log (X : ℝ) := mul_pos htheta hlog
  have hab : 2 * (r * (theta * Real.log (X : ℝ))) ≤ theta * Real.log (X : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hrHalf hb.le]
  have hbase := hfinite (r * (theta * Real.log (X : ℝ))) (theta * Real.log (X : ℝ))
    (2 * X) ha hab
  have hratio : r * (theta * Real.log (X : ℝ)) / (theta * Real.log (X : ℝ)) = r := by
    exact mul_div_cancel_right₀ _ hb.ne'
  rw [hratio] at hbase
  have hpaid : 2 * (S : ℝ) * (theta * Real.log (X : ℝ)) ≤ Real.log (X : ℝ) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcutoff hlog.le]
  have hrem : Real.exp (2 * (S : ℝ) * (theta * Real.log (X : ℝ))) / X ≤
      Real.exp (-Real.log (X : ℝ) / 2) := by
    calc
      _ ≤ Real.exp (Real.log (X : ℝ) / 2) / X :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpaid) hXr.le
      _ = Real.exp (Real.log (X : ℝ) / 2 - Real.log (X : ℝ)) := by
        rw [Real.exp_sub, Real.exp_log hXr]
      _ = _ := by congr 1; ring
  calc
    _ ≤ (C * r * (2 * X : ℕ) + Real.exp (2 * (S : ℝ) * (theta * Real.log (X : ℝ)))) /
        X := div_le_div_of_nonneg_right hbase hXr.le
    _ = 2 * C * r + Real.exp (2 * (S : ℝ) * (theta * Real.log (X : ℝ))) / X := by
      push_cast
      field_simp
    _ ≤ _ := add_le_add le_rfl hrem

theorem mrExists_fixedPower_missing_density_small {delta : ℝ} (hdelta : 0 < delta) :
    ∃ r thetaMax : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ 0 < thetaMax ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax →
      ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀,
        ((missingPrimeBlockSet (mrFixedPowerAuxiliaryInterval r theta X) (2 * X)).card : ℝ) /
          X ≤ delta := by
  obtain ⟨C, hC, S, hS, hfinite⟩ := mrExists_fixedPower_missing_density_bound
  let r := min (1 / 2 : ℝ) (delta / (4 * C))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrHalf : r ≤ 1 / 2 := min_le_left _ _
  have hratio : 2 * C * r ≤ delta / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * C)).1
      (min_le_right (1 / 2 : ℝ) (delta / (4 * C)))
    change r * (4 * C) ≤ delta at hh
    nlinarith
  have hSr : (0 : ℝ) < S := by exact_mod_cast (show 0 < S by omega)
  refine ⟨r, 1 / (4 * S), hr, hrHalf, by positivity, ?_⟩
  intro theta htheta hthetaMax
  have hcutoff : 4 * (S : ℝ) * theta ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (S : ℝ))).1 hthetaMax
    nlinarith
  have hhalf := Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    EulerSubpower.tendsto_log_nat_atTop
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf
  have heventual : ∀ᶠ X : ℕ in atTop,
      2 ≤ X ∧ 2 ≤ r * (theta * Real.log (X : ℝ)) ∧
        Real.exp (-Real.log (X : ℝ) / 2) ≤ delta / 2 := by
    filter_upwards [eventually_ge_atTop 2,
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (2 / (r * theta))),
      hexp.eventually (gt_mem_nhds (half_pos hdelta))] with X hX hlog herr
    have hh := (div_le_iff₀ (mul_pos hr htheta)).1 hlog
    refine ⟨hX, by nlinarith, ?_⟩
    simpa only [Function.comp_apply, neg_div] using herr.le
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 heventual
  refine ⟨max X₁ 2, le_max_right _ _, ?_⟩
  intro X hX
  obtain ⟨hXtwo, ha, herr⟩ := hX₁ X ((le_max_left _ _).trans hX)
  exact (hfinite hr hrHalf htheta hcutoff (by omega : 1 < X) ha).trans (by linarith)

theorem mrExists_fixedPower_missing_energy_small {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r thetaMax : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ 0 < thetaMax ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax →
      ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀,
      ∀ (blocks : Finset (ℕ × ℕ)) {f : ℕ → ℂ}, (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ {T : ℝ}, 0 ≤ T →
        (∫ t in -T..T, ‖mrAuxiliaryMissingPolynomial blocks
          (mrFixedPowerAuxiliaryInterval r theta X) f X t‖ ^ 2) ≤ epsilon * (T / X + 1) := by
  let delta := epsilon / (4 * (1 + Real.pi))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨r, thetaMax, hr, hrHalf, hthetaMax, hdensity⟩ :=
    mrExists_fixedPower_missing_density_small hdelta
  refine ⟨r, thetaMax, hr, hrHalf, hthetaMax, ?_⟩
  intro theta htheta hthetaUpper
  obtain ⟨X₀, hX₀, hcard⟩ := hdensity theta htheta hthetaUpper
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX blocks f hbound T hT
  have hXpos : 0 < X := by omega
  have hXr : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hmass := hcard X hX
  have htau : 0 ≤ T / X := by positivity
  have hscalar : 2 * (T / X) + 4 * Real.pi ≤
      4 * (1 + Real.pi) * (T / X + 1) := by
    nlinarith [Real.pi_pos, mul_nonneg htau Real.pi_pos.le]
  calc
    _ ≤ (2 * T + 4 * Real.pi * X) *
        (missingPrimeBlockSet (mrFixedPowerAuxiliaryInterval r theta X) (2 * X)).card /
          (X : ℝ) ^ 2 := intervalIntegral_mrAuxiliaryMissingPolynomial_le blocks _ hXpos hbound hT
    _ = (2 * (T / X) + 4 * Real.pi) *
        ((missingPrimeBlockSet (mrFixedPowerAuxiliaryInterval r theta X) (2 * X)).card / X) := by
      field_simp
    _ ≤ (4 * (1 + Real.pi) * (T / X + 1)) * delta :=
      mul_le_mul hscalar hmass (by positivity) (by positivity)
    _ = _ := by
      dsimp [delta]
      field_simp

end

end Erdos67b
