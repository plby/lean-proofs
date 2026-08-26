/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Passage from dyadic logarithmic statistics to all integer degrees.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.InteriorStability

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

def dyadicFloor (n : ℕ) : ℕ := 2 ^ Nat.log 2 n

theorem dyadicFloor_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 < dyadicFloor n ∧ dyadicFloor n ≤ n ∧ n ≤ 2 * dyadicFloor n := by
  have hlog : Nat.log 2 n ≠ 0 := (Nat.log_pos (by norm_num) hn).ne'
  refine ⟨one_lt_pow₀ (by norm_num) hlog, Nat.pow_log_le_self 2 (by omega), ?_⟩
  have h := (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n).le
  simpa only [dyadicFloor, pow_succ, mul_comm] using h

theorem log_dyadicFloor_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ Real.log n - Real.log (dyadicFloor n) ∧
      Real.log n - Real.log (dyadicFloor n) ≤ Real.log 2 := by
  obtain ⟨hN, hNn, hnN⟩ := dyadicFloor_bounds hn
  have hN₀ : (0 : ℝ) < dyadicFloor n := by exact_mod_cast (show 0 < dyadicFloor n by omega)
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlo := Real.log_le_log hN₀ (by exact_mod_cast hNn : (dyadicFloor n : ℝ) ≤ n)
  have hhi := Real.log_le_log hn₀ (by exact_mod_cast hnN : (n : ℝ) ≤ 2 * dyadicFloor n)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN₀.ne'] at hhi
  exact ⟨by linarith, by linarith⟩

theorem log_dyadicFloor_div_log_tendsto :
    Tendsto (fun n : ℕ ↦ Real.log (dyadicFloor n) / Real.log n) atTop (𝓝 1) := by
  have hdiff : Tendsto
      (fun n : ℕ ↦ (Real.log n - Real.log (dyadicFloor n)) / Real.log n) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := Real.log 2)
    · exact (eventually_ge_atTop 2).mono fun n hn ↦ (log_dyadicFloor_bounds hn).1
    · exact (eventually_ge_atTop 2).mono fun n hn ↦ (log_dyadicFloor_bounds hn).2
    · exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hdiff
  have heq : (fun n : ℕ ↦ 1 - (Real.log n - Real.log (dyadicFloor n)) / Real.log n) =ᶠ[atTop]
      (fun n : ℕ ↦ Real.log (dyadicFloor n) / Real.log n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    field_simp
    ring
  simpa only [sub_zero] using h.congr' heq

theorem dyadic_normalized_error_tendsto_zero (f : ℕ → ℝ)
    (h : ∀ k : ℕ, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, 2 ^ j ≤ m → m ≤ 2 * 2 ^ j →
        |f m - f (2 ^ j)| ≤ (1 / (k + 1 : ℝ)) * Real.log (2 ^ j : ℕ)) :
    Tendsto (fun n : ℕ ↦ (f n - f (dyadicFloor n)) / Real.log n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
  filter_upwards [nat_log_two_tendsto.eventually (h k), eventually_ge_atTop 2] with n hn hn₂
  obtain ⟨hN, hNn, hnN⟩ := dyadicFloor_bounds hn₂
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogN : Real.log (dyadicFloor n) ≤ Real.log n := by
    have hh := (log_dyadicFloor_bounds hn₂).1
    linarith
  have hbound : |f n - f (dyadicFloor n)| ≤ (1 / (k + 1 : ℝ)) * Real.log n := by
    exact (hn n hNn hnN).trans (mul_le_mul_of_nonneg_left hlogN (by positivity))
  simp only [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlog]
  exact ((div_le_iff₀ hlog).mpr hbound).trans_lt hk

/-- A general interpolation lemma, with no probabilistic assumptions. -/
theorem tendsto_of_dyadic_normalized_error (f : ℕ → ℝ) (L : ℝ)
    (herror : Tendsto (fun n : ℕ ↦ (f n - f (dyadicFloor n)) / Real.log n) atTop (𝓝 0))
    (hdyadic : Tendsto (fun j : ℕ ↦ f (2 ^ j) / Real.log (2 ^ j : ℕ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ f n / Real.log n) atTop (𝓝 L) := by
  have hbase := (hdyadic.comp nat_log_two_tendsto).mul log_dyadicFloor_div_log_tendsto
  have heq : (fun n : ℕ ↦ (f (2 ^ Nat.log 2 n) / Real.log (2 ^ Nat.log 2 n : ℕ)) *
      (Real.log (dyadicFloor n) / Real.log n)) =ᶠ[atTop]
      (fun n : ℕ ↦ f (dyadicFloor n) / Real.log n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hN := (dyadicFloor_bounds hn).1
    have hlog : 0 < Real.log (dyadicFloor n) := Real.log_pos (by exact_mod_cast hN)
    change (f (dyadicFloor n) / Real.log (dyadicFloor n)) *
      (Real.log (dyadicFloor n) / Real.log n) = _
    field_simp
  have hbase' : Tendsto (fun n : ℕ ↦ f (dyadicFloor n) / Real.log n) atTop (𝓝 L) := by
    simpa only [mul_one, Function.comp_apply] using hbase.congr' heq
  have hsum := herror.add hbase'
  convert hsum using 1
  · ext n
    ring
  · simp

theorem ae_interiorRootCount_dyadic_error :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun n : ℕ ↦
      ((interiorRootCount ε n : ℝ) - (interiorRootCount ε (dyadicFloor n) : ℝ)) / Real.log n)
        atTop (𝓝 0) := by
  have h : ∀ᵐ ε ∂sequenceLaw, ∀ k : ℕ, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, 2 ^ j ≤ m → m ≤ 2 * 2 ^ j →
        |(interiorRootCount ε m : ℝ) - (interiorRootCount ε (2 ^ j) : ℝ)| ≤
          (1 / (k + 1 : ℝ)) * Real.log (2 ^ j : ℕ) := by
    apply ae_all_iff.mpr
    intro k
    exact ae_interiorRootCount_dyadic_oscillation (by positivity)
  filter_upwards [h] with ε hε
  exact dyadic_normalized_error_tendsto_zero (fun n ↦ (interiorRootCount ε n : ℝ)) hε

end Erdos521
