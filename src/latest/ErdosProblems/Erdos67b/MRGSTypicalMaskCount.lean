import ErdosProblems.Erdos67b.MRBlockSchedule
import ErdosProblems.Erdos67b.MRCofactorPowerCutoff

/-!
# The source inclusion-exclusion count is smaller than every log power

The ambient threshold precedes the initial logarithmic endpoint and the
number of scheduled blocks. Large indices are paid by `J log J`; the
finitely many small indices are absorbed by a growing logarithmic power.
-/

open Filter

namespace Erdos67b

noncomputable section

theorem mrGS_log_schedule_upper_ge_four_mul_log {q₁ : ℝ} (hq : 1 ≤ q₁)
    {J : ℕ} (hJ : 1 ≤ J) :
    4 * (J : ℝ) * Real.log (J : ℝ) ≤ Real.log (mrLogScheduleUpper q₁ J) := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hqpos : 0 < q₁ := by linarith
  have hlogJ : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have hlogq : 0 ≤ Real.log q₁ := Real.log_nonneg hq
  unfold mrLogScheduleUpper
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg J : (0 : ℝ) ≤ J) hlogq]

theorem mrGS_maskCount_le_of_large_index
    {kappa q₁ L : ℝ} (hkappa : 0 < kappa) (hq : 1 ≤ q₁) (hL : 0 < L)
    {J : ℕ} (hJ : 1 ≤ J)
    (hupper : mrLogScheduleUpper q₁ J ≤ Real.sqrt L)
    (hindex : Real.log 2 ≤ 8 * kappa * Real.log (J : ℝ)) :
    (2 : ℝ) ^ J ≤ L ^ kappa := by
  have hQpos : 0 < mrLogScheduleUpper q₁ J :=
    (show 0 < q₁ by linarith).trans_le (mrLogScheduleUpper_ge hq hJ)
  have hlogUpper := Real.log_le_log hQpos hupper
  rw [Real.log_sqrt hL.le] at hlogUpper
  have hmain := (mrGS_log_schedule_upper_ge_four_mul_log hq hJ).trans hlogUpper
  have hscale := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 2 * kappa by positivity)
  have hindexJ := mul_le_mul_of_nonneg_left hindex (Nat.cast_nonneg J)
  have hcost : (J : ℝ) * Real.log 2 ≤ Real.log L * kappa := by nlinarith
  calc
    _ = (Real.exp (Real.log 2)) ^ J := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp ((J : ℝ) * Real.log 2) := (Real.exp_nat_mul _ J).symm
    _ ≤ Real.exp (Real.log L * kappa) := Real.exp_le_exp.mpr hcost
    _ = L ^ kappa := (Real.rpow_def_of_pos hL _).symm

theorem mrExists_eventually_source_maskCount_le_log_rpow
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      ∀ {q₁ : ℝ}, 1 ≤ q₁ → ∀ J : ℕ,
        mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
          (2 : ℝ) ^ J ≤ (Real.log (X : ℝ)) ^ kappa := by
  let J₀ : ℕ := ⌈Real.exp (Real.log 2 / (8 * kappa))⌉₊ + 2
  have hJ₀ : 2 ≤ J₀ := by dsimp only [J₀]; omega
  have hlargeIndex : ∀ J : ℕ, J₀ ≤ J →
      Real.log 2 ≤ 8 * kappa * Real.log (J : ℝ) := by
    intro J hJ
    have hceil : ⌈Real.exp (Real.log 2 / (8 * kappa))⌉₊ ≤ J := by
      dsimp only [J₀] at hJ
      omega
    have hexp : Real.exp (Real.log 2 / (8 * kappa)) ≤ (J : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have hlog := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at hlog
    have hh := (div_le_iff₀ (show 0 < 8 * kappa by positivity)).mp hlog
    nlinarith
  have hpower : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ)) ^ kappa) atTop atTop :=
    (tendsto_rpow_atTop hkappa).comp EulerSubpower.tendsto_log_nat_atTop
  have hall : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) ∧
      (2 : ℝ) ^ J₀ ≤ (Real.log (X : ℝ)) ^ kappa := by
    filter_upwards [EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1),
      hpower.eventually (eventually_ge_atTop ((2 : ℝ) ^ J₀))] with X hlog hcount
    exact ⟨hlog, hcount⟩
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hall
  refine ⟨max X₁ 1, le_max_right _ _, ?_⟩
  intro X hX q₁ hq J hupper
  obtain ⟨hlog, hsmall⟩ := hX₁ X ((le_max_left _ _).trans hX)
  by_cases hJ : J₀ ≤ J
  · exact mrGS_maskCount_le_of_large_index hkappa hq (by linarith)
      (by omega : 1 ≤ J) hupper (hlargeIndex J hJ)
  · exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by omega : J ≤ J₀)).trans hsmall

end

end Erdos67b
