import ErdosProblems.Erdos587.ThirdDifferenceScales

/-! The one-sixth exponential-sum estimate from second and third differences. -/

open scoped BigOperators

namespace Erdos587

lemma third_power_sixth_root {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 3) ^ (1 / 6 : ℝ) = Real.sqrt x := by
  rw [← Real.rpow_natCast_mul hx, Real.sqrt_eq_rpow]
  congr 1
  norm_num

lemma one_sixth_small_scale_comparison {n F : ℝ} (hn : 1 ≤ n) (hnF : n ≤ F)
    (hF : F ≤ n ^ (3 / 2 : ℝ)) :
    Real.sqrt F ≤ F ^ (1 / 6 : ℝ) * Real.sqrt n ∧
      n / Real.sqrt F ≤ F ^ (1 / 6 : ℝ) * Real.sqrt n := by
  have hnpos : 0 < n := by linarith
  have hFpos : 0 < F := hnpos.trans_le hnF
  have hF1 : 1 ≤ F := hn.trans hnF
  have hthird : F ^ (1 / 3 : ℝ) ≤ Real.sqrt n := by
    have hh := Real.rpow_le_rpow hFpos.le hF (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_mul hnpos.le] at hh
    norm_num at hh
    simpa only [Real.sqrt_eq_rpow] using hh
  constructor
  · calc
      Real.sqrt F = F ^ (1 / 6 : ℝ) * F ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hFpos, Real.sqrt_eq_rpow]
        congr 1
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hthird (Real.rpow_nonneg hFpos.le _)
  · calc
      n / Real.sqrt F ≤ n / Real.sqrt n :=
        div_le_div_of_nonneg_left hnpos.le (Real.sqrt_pos.mpr hnpos) (Real.sqrt_le_sqrt hnF)
      _ = Real.sqrt n := Real.div_sqrt
      _ ≤ _ := le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_rpow hF1 (by norm_num))

theorem norm_phase_sum_le_one_sixth_pair (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {F C : ℝ} (hNF : (N : ℝ) ≤ F) (hC : 1 ≤ C)
    (hsecondLo : ∀ n, n + 1 < N → -(C * (F / (N : ℝ) ^ 2)) ≤ phaseIncrement (phaseIncrement f) n)
    (hsecondHi : ∀ n, n + 1 < N → phaseIncrement (phaseIncrement f) n ≤ -(F / (N : ℝ) ^ 2))
    (hthirdLo : ∀ n, n + 2 < N → F / (N : ℝ) ^ 3 ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hthirdHi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * (F / (N : ℝ) ^ 3)) :
    ‖∑ n ∈ Finset.range N, phase (f n)‖ ≤ 100 * C * F ^ (1 / 6 : ℝ) * Real.sqrt N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hFpos : 0 < F := hNR.trans_le hNF
  have hCpos : 0 < C := by linarith
  have hrootN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  have hrootF : 0 < Real.sqrt F := Real.sqrt_pos.mpr hFpos
  have hFpower : 0 < F ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hFpos _
  by_cases hsmall : F ≤ (N : ℝ) ^ (3 / 2 : ℝ)
  · have hh := norm_phase_sum_le_negative_second_difference f N
      (by positivity : 0 < F / (N : ℝ) ^ 2) hC hsecondLo hsecondHi
    have heq : (N : ℝ) * Real.sqrt (F / (N : ℝ) ^ 2) + (Real.sqrt (F / (N : ℝ) ^ 2))⁻¹ =
        Real.sqrt F + (N : ℝ) / Real.sqrt F := by
      rw [Real.sqrt_div hFpos.le, Real.sqrt_sq hNR.le]
      field_simp
    rw [heq] at hh
    obtain ⟨hroot, hquot⟩ := one_sixth_small_scale_comparison hN1 hNF hsmall
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hroot hquot)
      (show 0 ≤ 10 * C by positivity)
    have hnonneg : 0 ≤ C * (F ^ (1 / 6 : ℝ) * Real.sqrt N) := by positivity
    nlinarith
  by_cases hlarge : (N : ℝ) ^ 3 ≤ F
  · have hroot : Real.sqrt (N : ℝ) ≤ F ^ (1 / 6 : ℝ) := by
      have hh := Real.rpow_le_rpow (show 0 ≤ (N : ℝ) ^ 3 by positivity) hlarge
        (by norm_num : (0 : ℝ) ≤ 1 / 6)
      rwa [third_power_sixth_root hNR.le] at hh
    have hsum : ‖∑ n ∈ Finset.range N, phase (f n)‖ ≤ N := by
      calc
        _ ≤ ∑ n ∈ Finset.range N, ‖phase (f n)‖ := norm_sum_le _ _
        _ = N := by simp
    have hscale : (N : ℝ) ≤ F ^ (1 / 6 : ℝ) * Real.sqrt N := by
      calc
        (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNR.le).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hroot hrootN.le
    apply hsum.trans (hscale.trans _)
    have hh := le_mul_of_one_le_left (mul_nonneg hFpower.le hrootN.le)
      (show 1 ≤ 100 * C by linarith)
    simpa only [mul_assoc] using hh
  · let lam : ℝ := F / (N : ℝ) ^ 3
    have hlam : 0 < lam := by dsimp [lam]; positivity
    have hlam1 : lam ≤ 1 := (div_le_one (pow_pos hNR 3)).mpr (le_of_not_ge hlarge)
    have hlamlo : (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ lam := by
      apply (le_div_iff₀ (pow_pos hNR 3)).mpr
      calc
        _ = (N : ℝ) ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hNR]
          congr 1
          norm_num
        _ ≤ F := le_of_not_ge hsmall
    have hh := norm_phase_sum_le_middle_third_difference f hN hlam hlam1 hlamlo hC hthirdLo hthirdHi
    apply hh.trans_eq
    dsimp [lam]
    rw [Real.div_rpow hFpos.le (by positivity), third_power_sixth_root hNR.le]
    calc
      _ = (100 * C * F ^ (1 / 6 : ℝ)) * ((N : ℝ) / Real.sqrt N) := by ring
      _ = _ := by rw [Real.div_sqrt]

end Erdos587
