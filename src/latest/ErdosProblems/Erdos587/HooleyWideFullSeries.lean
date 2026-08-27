import ErdosProblems.Erdos587.HooleyCenteredFullMean
import ErdosProblems.Erdos587.HooleyWideScale
import ErdosProblems.Erdos587.HooleyWideTail

/-! # The complete positive-frequency error in the power-separated branch -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_wide_full_positive_mean (f g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a q H : ℕ, 0 < q → 0 < H → H ≤ q → q.Coprime a →
        (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) →
        (q : ℝ) * (max 1 (Real.log (Real.log T))) ^ 7 ≤ H * T ^ (1 / 4 : ℝ) →
        let σ := ((q : ℝ) / H)⁻¹
        let M := ⌊T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ 6⌋₊
        Summable (fun n : ℕ => ‖((σ : ℂ) * g (σ * (n + 1))) *
          deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * (n + 1))‖) ∧
        (∑' n : ℕ, ‖((σ : ℂ) * g (σ * (n + 1))) *
          deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * (n + 1))‖) ≤
          C * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4 := by
  obtain ⟨C, hC, D, hD, hmean⟩ :=
    exists_delta_centered_full_positive_mean f (κ := 1 / 100000) (by norm_num)
  obtain ⟨B, hB, hdecay⟩ := exists_scaled_schwartz_decay_bound g 2
  refine ⟨C * B * 9 ^ 4 + 1, by positivity, ?_⟩
  filter_upwards [eventually_delta_wide_cutoff_bounds 6, eventually_delta_wide_schwartz_tail g,
    eventually_ge_atTop (max 2 D),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2]
    with T hcut htailT hT hlog
  intro a q H hq hH hHq hcop hqhi hbudget
  let Λ := max 1 (Real.log (Real.log T))
  let M := ⌊T ^ (1 / 4 : ℝ) / Λ ^ 6⌋₊
  let N := ⌊T ^ 2⌋₊
  let X := ⌊T ^ 8⌋₊
  let r := (q : ℝ) / H
  let σ := r⁻¹
  let w : ℕ → ℂ := fun m => (σ : ℂ) * g (σ * m)
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hDT : D ≤ T := (le_max_right _ _).trans hT
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛ2 : 2 ≤ Λ := by
    change 2 ≤ Real.log (Real.log T) at hlog
    exact hlog.trans (le_max_right _ _)
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHR1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hr : 1 ≤ r := (le_div_iff₀ hHR).mpr (by
    simpa only [one_mul] using (show (H : ℝ) ≤ q by exact_mod_cast hHq))
  have hrpos : 0 < r := by linarith
  have hσ : 0 < σ := inv_pos.mpr hrpos
  have hqT : (q : ℝ) ≤ T := by
    apply hqhi.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show (3 / 4 - 1 / 1000 : ℝ) ≤ 1 by norm_num)
  have hrT : r ≤ T := (div_le_self (Nat.cast_nonneg q) hHR1).trans hqT
  obtain ⟨hM, hMlo, hMhi, hMhalf, hMT⟩ := hcut
  obtain ⟨hMN, hsize, hsep, _, _⟩ := delta_wide_centered_scale_conditions hT2 hqhi hMlo hMT
  have hσM : 1 ≤ σ * M := delta_wide_frequency_base hq hΛ2 hbudget hMhalf
  have hsqrt1 : 1 ≤ Real.sqrt T := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT1
  have hsqrtsqrt1 : 1 ≤ Real.sqrt (Real.sqrt T) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hsqrt1
  have htail := htailT r hr hrT
  have htailSum : Summable (fun n : ℕ => if N < n + 1 then ‖w (n + 1)‖ else 0) := by
    simpa only [w, Nat.cast_add, Nat.cast_one] using htail.1
  have hwSum : Summable (fun n : ℕ => ‖w (n + 1)‖) :=
    (summable_and_tsum_le_prefix_add_tail (fun n : ℕ => ‖w (n + 1)‖) N
      (fun _ => norm_nonneg _) htailSum).1
  have htailBound : (∑' n : ℕ, if N < n + 1 then ‖w (n + 1)‖ else 0) ≤ 1 / T ^ 2 := by
    simpa only [w, Nat.cast_add, Nat.cast_one] using htail.2
  have hfull := hmean a q M N X hq hcop hM hMN (Real.sqrt T) hsqrt1 hsize hsep
    σ B (1 / T ^ 2) hσ hB.le hσM w hwSum (fun m _ => hdecay σ hσ m) htailBound
  have htailCost : D * Real.sqrt T * (1 / T ^ 2) ≤ 1 := by
    have hsqrtT : Real.sqrt T ≤ T := (Real.sqrt_le_iff).mpr ⟨hTpos.le, by nlinarith⟩
    have hh := mul_le_mul hDT hsqrtT (Real.sqrt_nonneg T) hTpos.le
    rw [← mul_div_assoc, mul_one]
    apply (div_le_one₀ (sq_pos_of_pos hTpos)).mpr
    simpa only [pow_two] using hh
  have hcost : (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) ≤ 9 ^ 4 * Λ ^ 4 :=
    delta_wide_loglog_mean_cost hT2
  have hunit : 1 ≤ σ * M * Real.sqrt (Real.sqrt T) * Λ ^ 4 := by
    have hΛpow : 1 ≤ Λ ^ 4 := one_le_pow₀ hΛ1
    calc
      (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ (σ * M) * Real.sqrt (Real.sqrt T) * Λ ^ 4 := by gcongr
  have hbound : (∑' n : ℕ, ‖w (n + 1) *
      deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * (n + 1))‖) ≤
      (C * B * 9 ^ 4 + 1) * σ * M * Real.sqrt (Real.sqrt T) * Λ ^ 4 := by
    apply hfull.2.trans
    calc
      _ ≤ C * B * σ * M * Real.sqrt (Real.sqrt T) * (9 ^ 4 * Λ ^ 4) + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hcost (by positivity)) htailCost
      _ ≤ C * B * σ * M * Real.sqrt (Real.sqrt T) * (9 ^ 4 * Λ ^ 4) +
          σ * M * Real.sqrt (Real.sqrt T) * Λ ^ 4 := add_le_add le_rfl hunit
      _ = _ := by ring
  simpa only [w, Nat.cast_add, Nat.cast_one] using And.intro hfull.1 hbound

end Erdos587
