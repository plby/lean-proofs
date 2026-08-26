import ErdosProblems.Erdos1148.LongCuspVisitPatterns
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The exponential rate of cusp visit patterns can be made arbitrarily small -/

namespace Erdos1148.DukeArithmetic

open Filter

theorem pow_nat_div_le_exp_rate {b ε : ℝ} (hb : 1 ≤ b) (hε : 0 ≤ ε)
    (m n : ℕ) (hrate : Real.log b ≤ ε * m) :
    b ^ (n / m + 1) ≤ b * Real.exp (ε * n) := by
  have hbpos : 0 < b := by linarith
  have hdiv : ((n / m : ℕ) : ℝ) * m ≤ (n : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self n m
  have hscaled := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg (n / m) : (0 : ℝ) ≤ _)
  have hdivscaled := mul_le_mul_of_nonneg_left hdiv hε
  calc
    _ = Real.exp (((n / m + 1 : ℕ) : ℝ) * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hbpos]
    _ ≤ Real.exp (Real.log b + ε * n) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith
    _ = b * Real.exp (ε * n) := by rw [Real.exp_add, Real.exp_log hbpos]

theorem exists_cusp_pattern_window_small_rate {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ Real.log ((m : ℝ) ^ 2 + 1) ≤ ε * m := by
  have hevent := Real.isLittleO_log_id_atTop.bound (div_pos hε (by norm_num : (0 : ℝ) < 4))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hevent
  obtain ⟨m, hm⟩ := exists_nat_gt (max R (max 1 (4 * Real.log 2 / ε)))
  have hmR : R ≤ (m : ℝ) := (le_max_left _ _).trans hm.le
  have hm1 : 1 < (m : ℝ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hmlarge : 4 * Real.log 2 / ε < (m : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hm
  have hlogm : Real.log (m : ℝ) ≤ (ε / 4) * m := by
    have h := hR (m : ℝ) hmR
    simp only [Real.norm_eq_abs, id_eq, abs_of_pos hmpos] at h
    exact (le_abs_self _).trans h
  refine ⟨m, by exact_mod_cast hmpos, ?_⟩
  calc
    _ ≤ Real.log ((2 * (m : ℝ)) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = 2 * (Real.log 2 + Real.log (m : ℝ)) := by
      rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmpos.ne']
      norm_num
    _ ≤ ε * m := by nlinarith [(div_lt_iff₀ hε).mp hmlarge]

theorem exists_cusp_visit_pattern_small_rate {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ C : ℝ, 0 < H₀ ∧ 0 < C ∧ ∀ H : ℝ, H₀ ≤ H → ∀ n : ℕ,
      ∃ P : Finset (Finset (Fin n)), (P.card : ℝ) ≤ C * Real.exp (ε * n) ∧
        ∀ x : ModularOrbitSpace, modularCuspVisitPattern H n x ∈ P := by
  obtain ⟨m, hm, hrate⟩ := exists_cusp_pattern_window_small_rate hε
  refine ⟨Real.exp (m : ℝ), (m : ℝ) ^ 2 + 1, Real.exp_pos _, by positivity, ?_⟩
  intro H hH n
  have hH1 : 1 ≤ H := (Real.one_le_exp_iff.mpr (Nat.cast_nonneg m)).trans hH
  have hHpos : 0 < H := by linarith
  have hwindow : Real.exp (m : ℝ) ≤ H ^ 4 := by
    apply hH.trans
    nlinarith [sq_nonneg (H ^ 2 - 1)]
  obtain ⟨P, hP, hcover⟩ := exists_long_cusp_visit_patterns hHpos m hm hwindow n
  refine ⟨P, ?_, hcover⟩
  have hcast : (P.card : ℝ) ≤ ((m : ℝ) ^ 2 + 1) ^ (n / m + 1) := by exact_mod_cast hP
  exact hcast.trans (pow_nat_div_le_exp_rate (by nlinarith [sq_nonneg (m : ℝ)]) hε.le m n hrate)

end Erdos1148.DukeArithmetic
