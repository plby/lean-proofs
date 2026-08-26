import ErdosProblems.Erdos67b.MRTLogPowerParameters

/-! # The integer auxiliary window and actual rounded prime endpoints -/

namespace Erdos67b

noncomputable section

def mrtLogPowerNatWindow (L : ℝ) : ℕ := ⌊mrtLogPowerWindow L⌋₊

theorem mrtLogPowerNatWindow_bounds {L : ℝ} (hW : 2 ≤ mrtLogPowerWindow L) :
    2 ≤ mrtLogPowerNatWindow L ∧
      mrtLogPowerWindow L / 2 ≤ (mrtLogPowerNatWindow L : ℝ) ∧
      (mrtLogPowerNatWindow L : ℝ) ≤ mrtLogPowerWindow L := by
  have hfloor : mrtLogPowerWindow L < (mrtLogPowerNatWindow L : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨Nat.le_floor hW, ?_, Nat.floor_le (mrtLogPowerWindow_pos L).le⟩
  linarith

theorem mrtLogPower_prime_lower_le {L : ℝ} (hW : 2 ≤ mrtLogPowerWindow L) :
    mrtLogPowerNatWindow L ^ 200 ≤
      (mrLogPrimeInterval (mrtLogPowerLower L) (mrtLogPowerUpper L)).1 := by
  have hfloor := (mrtLogPowerNatWindow_bounds hW).2.2
  have hpow : ((mrtLogPowerNatWindow L ^ 200 : ℕ) : ℝ) ≤ Real.exp (mrtLogPowerLower L) := by
    rw [mrtLogPower_exp_lower, Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 200
  have hh := hpow.trans (Nat.le_ceil (Real.exp (mrtLogPowerLower L)))
  exact_mod_cast hh

theorem mrtLogPower_prime_upper_le {H : ℕ} (hH : 0 < H)
    (hW : 2 ≤ mrtLogPowerWindow (Real.log (H : ℝ))) :
    (mrLogPrimeInterval (mrtLogPowerLower (Real.log (H : ℝ)))
      (mrtLogPowerUpper (Real.log (H : ℝ)))).2 ≤
        H / mrtLogPowerNatWindow (Real.log (H : ℝ)) ^ 3 := by
  let L : ℝ := Real.log (H : ℝ)
  let w := mrtLogPowerNatWindow L
  have hbounds := mrtLogPowerNatWindow_bounds hW
  have hw : 0 < w := by dsimp only [w, L]; omega
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hHexp : Real.exp L = (H : ℝ) := Real.exp_log (by exact_mod_cast hH)
  have hupper : Real.exp (mrtLogPowerUpper L) ≤ (H : ℝ) / (w : ℝ) ^ 3 := by
    rw [mrtLogPower_exp_upper, hHexp]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg H) (pow_pos hwR 3)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbounds.2.2 3
  have hfloor := (Nat.floor_le (Real.exp_pos (mrtLogPowerUpper L)).le).trans hupper
  have hmul := (le_div_iff₀ (pow_pos hwR 3)).1 hfloor
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < w ^ 3)).2
  exact_mod_cast hmul

end

end Erdos67b
