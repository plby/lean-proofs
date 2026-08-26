import ErdosProblems.Erdos67b.MRTLogPowerTail
import ErdosProblems.Erdos67b.MRTLogPowerRounding
import ErdosProblems.Erdos67b.MRFixedTypicalShortIntervals

/-! # Quantitative typical short sums for the logarithmic MRT parameters -/

open Filter Finset MeasureTheory
open scoped Topology Interval

namespace Erdos67b

noncomputable section

theorem mrtScaledCost_le_quarter {C m : ℝ} (hC : 0 ≤ C) (hm : 0 < m) :
    m * C * (1 / (4 * m * (C + 1))) ≤ 1 / 4 := by
  have hden : 0 < C + 1 := by positivity
  calc
    _ = (1 / 4 : ℝ) * (C / (C + 1)) := by field_simp
    _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one hden).2 (by linarith)) (by norm_num)
    _ = _ := by ring

theorem mrtExists_logPower_typical_short_meanSquare {rho : ℝ} (hrho : 0 < rho) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      mrtLogPowerLower (Real.log (H : ℝ)) / mrtLogPowerUpper (Real.log (H : ℝ)) ≤ rho ∧
      ∃ K M₀ X₀ : ℕ, 0 < K ∧ 0 < M₀ ∧ H ≤ X₀ ∧
        ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
        ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
        ∀ {h Z : ℕ},
          (H : ℝ) / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 ≤ h → h ≤ H → 2 * X ≤ Z →
          (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
            (typicalModulatedShortSum
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z f n h 0)) ≤
              (h : ℝ) ^ 2 * X / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 6 := by
  let C₀ := lemma14UniversalScaledLowConstant
  let C₁ := lemma14UniversalScaledHighConstant
  have hC₀ : 0 ≤ C₀ := lemma14UniversalScaledLowConstant_nonneg
  have hC₁ : 0 ≤ C₁ := lemma14UniversalScaledHighConstant_nonneg
  have henergySmall := mrtTendsto_logPower_weighted_budget.eventually
    (gt_mem_nhds (by positivity : 0 < 1 / (32 * (C₀ + 1))))
  have htailSmall := mrtTendsto_logPower_tail_budget.eventually
    (gt_mem_nhds (by positivity : 0 < 1 / (2048 * (C₁ + 1))))
  have hconditions := (mrtEventually_logPower_source hrho).and (henergySmall.and htailSmall)
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually hconditions)
  refine ⟨max H₁ 10, le_max_right _ _, ?_⟩
  intro H hH
  have hHpos : 0 < H := by omega
  have hHR : (0 : ℝ) < H := by exact_mod_cast hHpos
  let L := Real.log (H : ℝ)
  let W := mrtLogPowerWindow L
  let p := mrtLogPowerLower L
  let q := mrtLogPowerUpper L
  let c := mrtLogPowerCutoff L
  let B := mrFirstSmallRelativeBudget (1 / 12) p q c
  obtain ⟨hsource, hBsmall, htailsmall⟩ := hH₁ H ((le_max_left _ _).trans hH)
  obtain ⟨hL, hW, hp, hq, hpq, hlogq, hbudget, hmertens, hratio, hc0, hc1⟩ := hsource
  have hWpos : 0 < W := mrtLogPowerWindow_pos L
  have hN : 0 < W ^ 6 := pow_pos hWpos 6
  let e : ℝ := 1 / (16 * (C₀ + 1) * W ^ 6)
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨K, M₀, X₂, hK, hM₀, _, hshort⟩ := mrExists_fixed_typical_short_meanSquare
    (by norm_num : (0 : ℝ) < 1 / 12) (le_refl _) hp
    ((Real.one_le_exp_iff.2 (by norm_num : (0 : ℝ) ≤ 1)).trans hq)
    hpq hlogq hbudget hmertens hc0 hc1 he
  let X₀ := max X₂ (max H ⌈4 * (H : ℝ) * W ^ 6⌉₊)
  refine ⟨hW, hratio, K, M₀, X₀, hK, hM₀, ?_, ?_⟩
  · dsimp only [X₀]
    omega
  intro M X hM hX f hmul hbound hnonpret h Z hlength hhH hZ
  have hX₂ : X₂ ≤ X := by dsimp only [X₀] at hX; omega
  have hHX : H ≤ X := by dsimp only [X₀] at hX; omega
  have hhposR : (0 : ℝ) < h := (div_pos hHR (pow_pos hWpos 3)).trans_le hlength
  have hhpos : 0 < h := by exact_mod_cast hhposR
  have hhX : h ≤ X := hhH.trans hHX
  have hhHreal : (h : ℝ) ≤ H := by exact_mod_cast hhH
  have hXR : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hXscale : 4 * (H : ℝ) * W ^ 6 ≤ X :=
    Nat.le_of_ceil_le (by dsimp only [X₀] at hX; omega)
  have hbase := hshort hM hX₂ hmul hbound hnonpret hhpos hhX hZ
  change _ ≤ 4 * C₀ * (2 * B + e) * (h : ℝ) ^ 2 * X +
    512 * C₁ * X * (c⁻¹ + Real.pi / c ^ 2) + (h : ℝ) ^ 3 at hbase
  change W ^ 6 * B < 1 / (32 * (C₀ + 1)) at hBsmall
  have hBpaid : 8 * C₀ * B * W ^ 6 ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hBsmall.le (show 0 ≤ 8 * C₀ by positivity)
    have hconst := mrtScaledCost_le_quarter hC₀ (by norm_num : (0 : ℝ) < 8)
    norm_num only [show (4 : ℝ) * 8 = 32 by norm_num] at hconst
    nlinarith only [hh, hconst]
  have hepaid : 4 * C₀ * e * W ^ 6 ≤ 1 / 4 := by
    have hconst := mrtScaledCost_le_quarter hC₀ (by norm_num : (0 : ℝ) < 4)
    norm_num only [show (4 : ℝ) * 4 = 16 by norm_num] at hconst
    convert hconst using 1
    dsimp only [e]
    field_simp
  have hcentral : W ^ 6 * (4 * C₀ * (2 * B + e)) ≤ 1 / 2 := by
    nlinarith only [hBpaid, hepaid]
  have htailRatio : W ^ 6 * (c⁻¹ + Real.pi / c ^ 2) / (h : ℝ) ^ 2 ≤
      1 / (2048 * (C₁ + 1)) := by
    have hlength' : Real.exp L / W ^ 3 ≤ (h : ℝ) := by
      simpa only [L, Real.exp_log hHR] using hlength
    exact (mrtLogPower_partialLength_tail_le hL (by linarith) hlength').trans htailsmall.le
  have htail : W ^ 6 * (512 * C₁ * X * (c⁻¹ + Real.pi / c ^ 2)) ≤
      (1 / 4 : ℝ) * (h : ℝ) ^ 2 * X := by
    have hraw := (div_le_iff₀ (sq_pos_of_pos hhposR)).1 htailRatio
    have hh := mul_le_mul_of_nonneg_left hraw (show 0 ≤ 512 * C₁ by positivity)
    have hconst := mrtScaledCost_le_quarter hC₁ (by norm_num : (0 : ℝ) < 512)
    norm_num only [show (4 : ℝ) * 512 = 2048 by norm_num] at hconst
    have hconst' := mul_le_mul_of_nonneg_right hconst (sq_nonneg (h : ℝ))
    have hscalar : W ^ 6 * (512 * C₁ * (c⁻¹ + Real.pi / c ^ 2)) ≤
        (1 / 4 : ℝ) * (h : ℝ) ^ 2 := by nlinarith only [hh, hconst']
    calc
      _ = (W ^ 6 * (512 * C₁ * (c⁻¹ + Real.pi / c ^ 2))) * X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscalar hXR
  have hboundary : W ^ 6 * (h : ℝ) ^ 3 ≤ (1 / 4 : ℝ) * (h : ℝ) ^ 2 * X := by
    have hh : 4 * (h : ℝ) * W ^ 6 ≤ X :=
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhHreal (by norm_num)) hN.le).trans hXscale
    calc
      _ = ((1 / 4 : ℝ) * (h : ℝ) ^ 2) * (4 * (h : ℝ) * W ^ 6) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
  have hcentral' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcentral (sq_nonneg (h : ℝ))) hXR
  apply (le_div_iff₀ hN).2
  have hscaled := mul_le_mul_of_nonneg_left hbase hN.le
  nlinarith only [hscaled, hcentral', htail, hboundary]

theorem mrtExists_logPower_typical_short_firstMoment {rho : ℝ} (hrho : 0 < rho) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      mrtLogPowerLower (Real.log (H : ℝ)) / mrtLogPowerUpper (Real.log (H : ℝ)) ≤ rho ∧
      ∃ K M₀ X₀ : ℕ, 0 < K ∧ 0 < M₀ ∧ H ≤ X₀ ∧
        ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
        ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
        ∀ {h Z : ℕ},
          (H : ℝ) / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 ≤ h → h ≤ H → 2 * X ≤ Z →
          (∑ n ∈ Finset.Ioc X (2 * X),
            ‖typicalModulatedShortSum
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z f n h 0‖) ≤
              (h : ℝ) * X / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 := by
  obtain ⟨H₀, hH₀, hmain⟩ := mrtExists_logPower_typical_short_meanSquare hrho
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨hW, hratio, K, M₀, X₀, hK, hM₀, hX₀, hsquare⟩ := hmain H hH
  refine ⟨hW, hratio, K, M₀, X₀, hK, hM₀, hX₀, ?_⟩
  intro M X hM hX f hmul hbound hnonpret h Z hlength hhH hZ
  let W := mrtLogPowerWindow (Real.log (H : ℝ))
  have hWpos : 0 < W := mrtLogPowerWindow_pos _
  have h₂ := hsquare hM hX hmul hbound hnonpret hlength hhH hZ
  let F := fun n ↦ typicalModulatedShortSum
    (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
      (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z f n h 0
  have hbound₂ : (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (F n)) ≤
      ((h : ℝ) / W ^ 3) ^ 2 * (Finset.Ioc X (2 * X)).card := by
    rw [card_Ioc_self_two_mul]
    calc
      _ ≤ (h : ℝ) ^ 2 * X / W ^ 6 := h₂
      _ = _ := by ring
  have hfirst := sum_norm_le_of_sum_normSq_le (Finset.Ioc X (2 * X)) F
    ((h : ℝ) / W ^ 3) (by positivity) hbound₂
  rw [card_Ioc_self_two_mul] at hfirst
  calc
    _ ≤ ((h : ℝ) / W ^ 3) * X := hfirst
    _ = _ := by ring

end

end Erdos67b
