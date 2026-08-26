/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform root moments for the shifted central-window polynomials.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainWindowGeometry
import ErdosProblems.Erdos521.WindowScaleGrowth

namespace Erdos521

open MeasureTheory Filter

theorem eventually_mainWindow_degree_large (M : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, M ≤ dyadicWindowDegree k (windowWidthScale j) := by
  have hpow : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ windowWidthScale j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp windowWidthScale_tendsto_atTop
  filter_upwards [hpow.eventually_ge_atTop M, eventually_ge_atTop 1] with j hj hj₁
  intro k hk
  exact hj.trans (main_window_degree_bounds hj₁ hk).1

theorem eventually_mainWindow_bulk {C : ℝ} (hC : 0 < C) :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      dyadicPoint (k + 1) ≤ endpointCenter C (dyadicWindowDegree k (windowWidthScale j)) := by
  filter_upwards [eventually_const_mul_rpow_le_window_scale (4 * C * Real.log 2) 1,
    eventually_ge_atTop 1] with j hj hj₁
  intro k hk
  have hD := main_window_degree_bounds hj₁ hk
  have hDpos : (0 : ℝ) < dyadicWindowDegree k (windowWidthScale j) := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℕ) < 2 ^ windowWidthScale j) hD.1)
  have hlog : Real.log (dyadicWindowDegree k (windowWidthScale j)) ≤ (j : ℝ) * Real.log 2 := by
    have h := Real.log_le_log hDpos (show (dyadicWindowDegree k (windowWidthScale j) : ℝ) ≤ (2 ^ j : ℕ) by
      exact_mod_cast hD.2)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
  have hgap := dyadicWindowDegree_endpoint_gap_lower k (windowWidthScale_pos hj₁)
  have hClog := mul_le_mul_of_nonneg_left hlog hC.le
  rw [Real.rpow_one] at hj
  have hscale : C * Real.log (dyadicWindowDegree k (windowWidthScale j)) ≤
      (dyadicWindowDegree k (windowWidthScale j) : ℝ) * (1 - dyadicPoint (k + 1)) := by nlinarith
  have hdiv : C * Real.log (dyadicWindowDegree k (windowWidthScale j)) /
      (dyadicWindowDegree k (windowWidthScale j) : ℝ) ≤ 1 - dyadicPoint (k + 1) := by
    apply (div_le_iff₀ hDpos).mpr
    simpa only [mul_comm] using hscale
  unfold endpointCenter
  linarith

theorem eventually_mainWindow_root_moments (p : ℕ) (hp : 1 ≤ p) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      (∫ ε, (intervalRootCount ε (dyadicWindowDegree k (windowWidthScale j))
        (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ^ p ∂sequenceLaw) ≤ B := by
  obtain ⟨B, hB, hmom⟩ := eventually_dyadic_interval_moments p hp
  obtain ⟨M, hM⟩ := eventually_atTop.mp hmom
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_mainWindow_degree_large M, eventually_mainBin_lower,
    eventually_mainWindow_bulk (localMomentBulkConstant_pos p)] with j hj hl hu
  intro k hk
  exact hM (dyadicWindowDegree k (windowWidthScale j)) (hj k hk) k (hl k hk) (hu k hk)

end Erdos521
