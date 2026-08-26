import ErdosProblems.Erdos421.ZetaBlocks

/-! # Zeta-factor estimates from small through polynomial frequencies -/

namespace Erdos421

theorem logarithmicSum_small_abs_frequency_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    {τ : ℝ} (hτ : τ ≠ 0) (hτM : |τ| ≤ M) :
    ‖logarithmicSum M N τ‖ ≤ 24 * M / |τ| := by
  have ht : 0 < |τ| := abs_pos.mpr hτ
  have hb := logarithmicSum_small_frequency_bound hM N ht hτM
  rw [logarithmicSum_norm_abs] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ ht.le
  have hn : (N : ℝ) ≤ M := by exact_mod_cast hN
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

theorem zetaBlock_small_frequency_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (s : ℂ) (hs : 0 ≤ s.re) (ht : s.im ≠ 0) (htM : |s.im| ≤ M) :
    ‖zetaBlock M N s‖ ≤ 24 * (M : ℝ) ^ (1 - s.re) / |s.im| := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have htp : 0 < |s.im| := abs_pos.mpr ht
  have hpref : ∀ n ≤ N, ‖logarithmicSum M n (-s.im)‖ ≤ 24 * M / |s.im| := by
    intro n hn
    simpa only [abs_neg] using logarithmicSum_small_abs_frequency_bound
      hM (hn.trans hN) (neg_ne_zero.mpr ht) (by simpa only [abs_neg] using htM)
  have hb := zetaBlock_norm_le_of_prefix_bounds hM N s hs (by positivity) hpref
  have he : (M : ℝ) ^ (-s.re) * M = (M : ℝ) ^ (1 - s.re) := by
    rw [sub_eq_add_neg, Real.rpow_add hMp, Real.rpow_one]
    ring
  calc
    _ ≤ (M : ℝ) ^ (-s.re) * (24 * M / |s.im|) := hb
    _ = 24 * ((M : ℝ) ^ (-s.re) * M) / |s.im| := by ring
    _ = _ := by rw [he]

/-- There is no lower polynomial restriction on the frequency in this
combined bound. The small-frequency contribution is recorded explicitly. -/
theorem zetaBlock_all_frequency_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) (s : ℂ) (hs : 0 ≤ s.re)
    (ht : s.im ≠ 0) (htM : |s.im| ≤ (M : ℝ) ^ (R + 1)) :
    ‖zetaBlock M N s‖ ≤ (M : ℝ) ^ (1 - s.re) *
      (24 / |s.im| + 4 * logarithmicPowerSaving M R K) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsaving := logarithmicPowerSaving_pos hM R K
  have hpower : 0 < (M : ℝ) ^ (1 - s.re) := Real.rpow_pos_of_pos hMp _
  by_cases hlo : (M : ℝ) ^ (2 / (K : ℝ)) ≤ |s.im|
  · have hb := zetaBlock_uniform_norm_bound hM hN R K hK s hs hlo htM
    have hquot : 0 ≤ 24 / |s.im| := by positivity
    nlinarith
  · have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have he : 2 / (K : ℝ) ≤ 1 := (div_le_one hKp).mpr (by exact_mod_cast (show 2 ≤ K by omega))
    have hsmall : |s.im| ≤ M := by
      apply (lt_of_not_ge hlo).le.trans
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM1 he
    have hb := zetaBlock_small_frequency_bound hM hN s hs ht hsmall
    have heq : 24 * (M : ℝ) ^ (1 - s.re) / |s.im| =
        (M : ℝ) ^ (1 - s.re) * (24 / |s.im|) := by ring
    rw [heq] at hb
    nlinarith

theorem zetaBlock_all_frequency_bound_of_one_le_re {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) (s : ℂ) (hs : 1 ≤ s.re)
    (ht : s.im ≠ 0) (htM : |s.im| ≤ (M : ℝ) ^ (R + 1)) :
    ‖zetaBlock M N s‖ ≤ 24 / |s.im| + 4 * logarithmicPowerSaving M R K := by
  have hb := zetaBlock_all_frequency_bound hM hN R K hK s (by linarith) ht htM
  have hp : (M : ℝ) ^ (1 - s.re) ≤ 1 := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hM1 (sub_nonpos.mpr hs)
  have hsave := logarithmicPowerSaving_pos hM R K
  exact hb.trans (by nlinarith [show 0 ≤ 24 / |s.im| by positivity])

end Erdos421
