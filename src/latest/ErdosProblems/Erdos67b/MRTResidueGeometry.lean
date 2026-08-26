import ErdosProblems.Erdos67b.MRTDividedIntervals
import ErdosProblems.Erdos67b.MRTCharacterResidues

/-! # Uniform geometry for every small residue modulus -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrScheduledBlocks_exp_lower_le_prime {p q : ℝ} (hp : 0 ≤ p) (hq : 1 ≤ q)
    {K : ℕ} {I : ℕ × ℕ} (hI : I ∈ mrScheduledBlocks p q K)
    {l : ℕ} (hl : l ∈ primesInBlock I) : Real.exp p ≤ (l : ℝ) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hI
  have hjpos := (Finset.mem_Icc.1 hj).1
  have hlow := (mem_primesInBlock.1 hl).2.1
  change ⌈Real.exp (mrLogScheduleLower p q j)⌉₊ ≤ l at hlow
  exact (Real.exp_le_exp.2 (mrLogScheduleLower_ge hp hq hjpos)).trans
    ((Nat.le_ceil _).trans (by exact_mod_cast hlow))

theorem mrtLogPower_scheduled_primes_large {L : ℝ}
    (hW : 2 ≤ mrtLogPowerWindow L) (hp : 0 ≤ mrtLogPowerLower L)
    (hq : 1 ≤ mrtLogPowerUpper L) {d : ℕ} (hd : d ≤ mrtLogPowerNatWindow L) (K : ℕ) :
    ∀ I ∈ mrScheduledBlocks (mrtLogPowerLower L) (mrtLogPowerUpper L) K,
      ∀ l ∈ primesInBlock I, d < l := by
  intro I hI l hl
  let W := mrtLogPowerWindow L
  have hWone : 1 ≤ W := by dsimp only [W]; linarith only [hW]
  have hWlt : W < W ^ 2 := by dsimp only [W]; nlinarith only [hW]
  have hpow : W ^ 2 ≤ W ^ 200 := pow_le_pow_right₀ hWone (by norm_num)
  have hdW : (d : ℝ) ≤ W :=
    (show (d : ℝ) ≤ (mrtLogPowerNatWindow L : ℝ) by exact_mod_cast hd).trans
      (mrtLogPowerNatWindow_bounds hW).2.2
  have hlower := mrScheduledBlocks_exp_lower_le_prime hp hq hI hl
  rw [mrtLogPower_exp_lower] at hlower
  exact_mod_cast hdW.trans_lt (hWlt.trans_le (hpow.trans hlower))

theorem mrtLogPower_window_cube_le_exp {L : ℝ} (hW : 1 ≤ mrtLogPowerWindow L)
    (hc : mrtLogPowerCutoff L ≤ 1) : mrtLogPowerWindow L ^ 3 ≤ Real.exp L := by
  rw [mrtLogPowerCutoff_eq] at hc
  have hten := (div_le_one (Real.exp_pos L)).1 hc
  exact (pow_le_pow_right₀ hW (by norm_num : 3 ≤ 10)).trans hten

theorem mrtDivided_shortLength_ge {a W : ℝ} (ha : 1 ≤ a) (hW : 0 < W)
    {h d : ℕ} (hd : 0 < d) (hdW : (d : ℝ) ≤ W) (hshort : 2 * a * W ≤ h) :
    a ≤ ((h / d : ℕ) : ℝ) := by
  have hnat : h < (h / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (h / d))
  have hround : (h : ℝ) < (((h / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast hnat
  have hprod := mul_le_mul_of_nonneg_left hdW
    (show 0 ≤ ((h / d : ℕ) : ℝ) + 1 by positivity)
  have hcancel : 2 * a < ((h / d : ℕ) : ℝ) + 1 := by
    apply (mul_lt_mul_iff_left₀ hW).1
    nlinarith only [hshort, hround, hprod]
  linarith only [ha, hcancel]

theorem mrtLogPower_divided_shortLength_bounds {H h d : ℕ} (hH : 0 < H)
    (hW : 2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)))
    (hc : mrtLogPowerCutoff (Real.log (H : ℝ)) ≤ 1) (hd : 0 < d)
    (hdW : d ≤ mrtLogPowerNatWindow (Real.log (H : ℝ)))
    (hshort : 2 * (H : ℝ) / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 2 ≤ h)
    (hhH : h ≤ H) :
    (H : ℝ) / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 ≤ (h / d : ℕ) ∧ h / d ≤ H := by
  let W := mrtLogPowerWindow (Real.log (H : ℝ))
  have hWpos : 0 < W := mrtLogPowerWindow_pos _
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcube : W ^ 3 ≤ (H : ℝ) := by
    have hh := mrtLogPower_window_cube_le_exp (by linarith only [hW]) hc
    simpa only [Real.exp_log hHR] using hh
  refine ⟨?_, (Nat.div_le_self h d).trans hhH⟩
  apply mrtDivided_shortLength_ge
    ((le_div_iff₀ (pow_pos hWpos 3)).2 (by simpa only [one_mul] using hcube)) hWpos hd
    ((show (d : ℝ) ≤ (mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℝ) by
      exact_mod_cast hdW).trans (mrtLogPowerNatWindow_bounds hW).2.2)
  calc
    _ = 2 * (H : ℝ) / W ^ 2 := by field_simp
    _ ≤ _ := hshort

theorem mrtDivided_ambient_threshold {Y₀ Y d w : ℕ} (hd : 0 < d)
    (hdw : d ≤ w) (hY : w * Y₀ ≤ Y) : Y₀ ≤ Y / d := by
  apply (Nat.le_div_iff_mul_le hd).2
  exact (Nat.mul_le_mul_left Y₀ hdw).trans (by simpa only [mul_comm] using hY)

theorem mrtDivided_scale_mono {d w : ℕ} (hd : 0 < d) (hdw : d ≤ w) (Y : ℕ) :
    Y / w ≤ Y / d := by
  apply (Nat.le_div_iff_mul_le hd).2
  exact (Nat.mul_le_mul_left (Y / w) hdw).trans (Nat.div_mul_le_self Y w)

theorem mrtDivided_cutoff {Z Y d : ℕ} (hd : 0 < d) (hZ : 2 * Y ≤ Z) :
    2 * (Y / d) ≤ Z / d := by
  apply (Nat.le_div_iff_mul_le hd).2
  calc
    _ = 2 * ((Y / d) * d) := by ring
    _ ≤ 2 * Y := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self Y d)
    _ ≤ _ := hZ

end

end Erdos67b
