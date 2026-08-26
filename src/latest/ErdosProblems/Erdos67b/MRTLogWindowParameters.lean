import ErdosProblems.Erdos67b.MRTLogWindowGeometry

/-! # Epsilon choices and the final logarithmic threshold -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrtLog_nat_one_le_of_four_le {H : ℕ} (hH : 4 ≤ H) : 1 ≤ Real.log H := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ H by exact_mod_cast hH)
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith [Real.log_two_gt_d9]

theorem mrtLogPowerNatWindow_pos_of_four_le {H : ℕ} (hH : 4 ≤ H) :
    0 < mrtLogPowerNatWindow (Real.log (H : ℝ)) := by
  change 1 ≤ ⌊mrtLogPowerWindow (Real.log (H : ℝ))⌋₊
  apply Nat.le_floor
  simpa only [Nat.cast_one] using
    mrtLogPowerWindow_one_le (mrtLog_nat_one_le_of_four_le hH)

theorem mrtLogWindow_small_coefficient {ε : ℝ} (hε : 0 < ε) :
    2 / max 1 (8 / ε) + 4 * (ε / 16) ≤ ε / 2 := by
  let R : ℝ := max 1 (8 / ε)
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hscale : 8 ≤ R * ε := (div_le_iff₀ hε).1 (le_max_right 1 (8 / ε))
  have hdiv : 2 / R ≤ ε / 4 := by
    apply (div_le_iff₀ hR).2
    nlinarith only [hscale]
  change 2 / R + 4 * (ε / 16) ≤ ε / 2
  linarith only [hdiv]

theorem mrtExists_logWindow_threshold (K N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℕ, max N 4 ≤ A₀ ∧ ∀ W : ℕ, A₀ ≤ W →
      1 ≤ Real.log W ∧ (K : ℝ) + 1 ≤ (ε / 2) * Real.log W := by
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually
      (eventually_ge_atTop (max 1 (2 * ((K : ℝ) + 1) / ε))))
  refine ⟨max (max N 4) A₁, le_max_left _ _, ?_⟩
  intro W hW
  have hh := hA₁ W ((le_max_right _ _).trans hW)
  have hlog : 1 ≤ Real.log W := (le_max_left _ _).trans hh
  have hbound := (div_le_iff₀ hε).1 ((le_max_right _ _).trans hh)
  exact ⟨hlog, by nlinarith only [hbound]⟩

end

end Erdos67b
