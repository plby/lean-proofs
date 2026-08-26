/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform quantitative two-root bounds for the fine dyadic cells.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.FineGridSmallBall
import ErdosProblems.Erdos521.TwoRootLimits

namespace Erdos521

open MeasureTheory Filter

theorem eventually_fineGrid_two_roots :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ i < fineGridLength j,
      sequenceLaw.real {ε | 2 ≤ intervalRootCount ε (2 ^ j)
        (dyadicFineGrid j k i) (dyadicFineGrid j k (i + 1))} ≤
        (fineGridSmallBallConstant + 96) * fineGridThreshold j := by
  filter_upwards [eventually_mainBin_point_variance, eventually_mainBin_fine_error, eventually_ge_atTop 1]
    with j hj herr hj₁
  intro k hk i hi
  have hj₀ : 0 < j := by omega
  have hlo := hj k hk _ (dyadicFineGrid_mem hj₀ k (show i ≤ fineGridLength j by omega))
  have hup := hj k hk _ (dyadicFineGrid_mem hj₀ k (show i + 1 ≤ fineGridLength j by omega))
  have he := herr k hk _ (dyadicFineGrid_mem hj₀ k (show i + 1 ≤ fineGridLength j by omega))
  have h := two_interval_roots_normalized_error (2 ^ j)
    (by linarith [hlo.1] : 0 ≤ dyadicFineGrid j k i)
    (dyadicFineGrid_strictMono hj₀ k (Nat.lt_succ_self i))
    (by linarith [hup.1] : 1 / 2 ≤ dyadicFineGrid j k (i + 1)) hup.2.1
    (fineGridThreshold_pos hj₀) (fineGridRelativeWidth_pos hj₀).le
    (dyadicFineGrid_relative_width hj₀ k hi) hup.2.2.1
  rw [mul_div_assoc, fineGrid_energy_balance hj₀] at h
  unfold fineGridSmallBallConstant
  linarith

theorem eventually_mainBin_fine_zero_probability :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, ∀ x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)),
      sequenceLaw.real {ε | powerSum ε (2 ^ j + 1) x = 0} ≤ fineGridSmallBallConstant * fineGridThreshold j := by
  filter_upwards [eventually_mainBin_fine_smallBall, eventually_ge_atTop 1] with j hj hj₁
  intro k hk x hx
  apply le_trans _ (hj k hk x hx)
  apply measureReal_mono (h₂ := measure_ne_top sequenceLaw _)
  intro ε hε
  change powerSum ε (2 ^ j + 1) x = 0 at hε
  change |powerSum ε (2 ^ j + 1) x| ≤ _
  rw [hε, abs_zero]
  exact mul_nonneg (fineGridThreshold_pos (j := j) (by omega)).le (Real.sqrt_nonneg _)

end Erdos521
