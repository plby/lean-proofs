import ErdosProblems.Erdos587.HooleyWideCutoff
import ErdosProblems.Erdos587.CriticalCutoffs

/-! # The quadratic frequency cutoff controls the whole Schwartz tail -/

open Filter
open scoped SchwartzMap

namespace Erdos587

lemma delta_wide_frequency_base {q H M : ℕ} (hq : 0 < q) {Λ P : ℝ}
    (hΛ : 2 ≤ Λ) (hbudget : (q : ℝ) * Λ ^ 7 ≤ H * P)
    (hhalf : (P / Λ ^ 6) / 2 ≤ M) :
    1 ≤ ((q : ℝ) / H)⁻¹ * M := by
  have hqHM : q ≤ H * M := wide_cutoff_product_budget (F := 6) hΛ hbudget hhalf
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  rw [inv_div]
  have hmul : (q : ℝ) ≤ (H : ℝ) * M := by exact_mod_cast hqHM
  calc
    (1 : ℝ) = (q : ℝ) / q := (div_self hqR.ne').symm
    _ ≤ ((H : ℝ) * M) / q := div_le_div_of_nonneg_right hmul hqR.le
    _ = _ := by ring

theorem eventually_delta_wide_schwartz_tail (g : 𝓢(ℝ, ℂ)) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 1 ≤ r → r ≤ T →
      let N := ⌊T ^ 2⌋₊
      Summable (fun n : ℕ => if N < n + 1 then
        ‖((r⁻¹ : ℝ) : ℂ) * g (r⁻¹ * (n + 1))‖ else 0) ∧
      (∑' n : ℕ, if N < n + 1 then
        ‖((r⁻¹ : ℝ) : ℂ) * g (r⁻¹ * (n + 1))‖ else 0) ≤ 1 / T ^ 2 := by
  obtain ⟨C, _hC, htail⟩ := exists_scaled_schwartz_positive_tail_bound g 0
  filter_upwards [eventually_scaled_schwartz_power_tail g, eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 100 by norm_num)).eventually_ge_atTop 4]
    with T htailT hT hpower
  intro r hr hrT
  let N := ⌊T ^ 2⌋₊
  let N₁ := ⌊r * T ^ (1 / 100 : ℝ)⌋₊
  have hrpos : 0 < r := by linarith
  have hσ : 0 < r⁻¹ := inv_pos.mpr hrpos
  obtain ⟨hM, hMN₁, _, _, hσlo, hσhi, _⟩ := normalized_frequency_cutoffs hr hpower
  have hN₁ : 0 < N₁ := hM.trans_le hMN₁
  have hN₁N : N₁ ≤ N := by
    apply Nat.floor_mono
    have hpow : T ^ (1 / 100 : ℝ) ≤ T := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hT (show (1 / 100 : ℝ) ≤ 1 by norm_num)
    calc
      r * T ^ (1 / 100 : ℝ) ≤ T * T := mul_le_mul hrT hpow (by positivity) (by linarith)
      _ = T ^ 2 := by ring
  have hN : 0 < N := hN₁.trans_le hN₁N
  have hs₁ := (htail r⁻¹ ⌈r⌉₊ N₁ hσ hM hN₁ hσlo hσhi).1
  have hs := (htail r⁻¹ ⌈r⌉₊ N hσ hM hN hσlo hσhi).1
  refine ⟨hs, ?_⟩
  apply (hs.tsum_le_tsum ?_ hs₁).trans (htailT r hr)
  intro n
  by_cases hbig : N < n + 1
  · have hbig₁ : N₁ < n + 1 := hN₁N.trans_lt hbig
    simp only [if_pos hbig, if_pos hbig₁]
    exact le_rfl
  · simp only [if_neg hbig]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl

end Erdos587
