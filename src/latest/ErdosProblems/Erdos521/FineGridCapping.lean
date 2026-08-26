/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The probability of capping a central-window sign count is summably small across bins.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainWindowMoments
import ErdosProblems.Erdos521.DyadicWindowGeometry
import ErdosProblems.Erdos521.DyadicFineGrid
import ErdosProblems.Erdos521.WindowGridMoments

namespace Erdos521

open MeasureTheory Filter

theorem eventually_fineGrid_capping_probability :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      sequenceLaw.real {ε | (windowCapScale j : ℝ) ≤
        (windowGridSignChanges ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j))
          (dyadicFineGrid j k) (fineGridLength j) : ℝ)} ≤ B * (j : ℝ) ^ (-4 : ℝ) := by
  obtain ⟨B, hB, hmom⟩ := eventually_mainWindow_root_moments 32 (by norm_num)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hmom, eventually_mainBin_lower, eventually_ge_atTop 1] with j hj hl hj₁
  intro k hk
  have hj₀ : 0 < j := by omega
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj₀
  have hT : (0 : ℝ) < windowCapScale j := by
    exact_mod_cast (show 0 < windowCapScale j by dsimp [windowCapScale]; omega)
  have hLU : 2 ^ (k - windowWidthScale j) < 2 ^ (k + windowWidthScale j) + 1 := by
    have h := dyadic_window_low_le_high k (windowWidthScale j)
    omega
  have hdeg : 2 ^ (k + windowWidthScale j) + 1 - 2 ^ (k - windowWidthScale j) - 1 =
      dyadicWindowDegree k (windowWidthScale j) := by unfold dyadicWindowDegree; omega
  have h := window_grid_capping_probability hLU (dyadicFineGrid j k) (dyadicFineGrid_mono j k)
    (fun i ↦ dyadicFineGrid_pos j k (by linarith [hl k hk]) i) (fineGridLength j) 32 hT
  rw [← dyadicCoefficientWindow_eq_Ico (main_window_upper hk), hdeg,
    dyadicFineGrid_zero, dyadicFineGrid_end hj₀] at h
  apply h.trans
  have hpow : (j : ℝ) ^ 4 ≤ (windowCapScale j : ℝ) ^ 32 := by
    exact_mod_cast index_pow_four_le_windowCapScale_pow_thirtytwo j
  calc
    _ ≤ B / (windowCapScale j : ℝ) ^ 32 := div_le_div_of_nonneg_right (hj k hk) (by positivity)
    _ ≤ B / (j : ℝ) ^ 4 := div_le_div_of_nonneg_left hB.le (pow_pos hjpos 4) hpow
    _ = _ := by rw [Real.rpow_neg hjpos.le, Real.rpow_ofNat, div_eq_mul_inv]

end Erdos521
