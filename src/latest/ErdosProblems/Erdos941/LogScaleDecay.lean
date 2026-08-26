import ErdosProblems.Erdos941.EntropyComparison

/-! # Geometric decay at the logarithmic sphere scale -/

namespace Erdos941.Analytic

open Filter

theorem log_scale_power_bound {Q n : ℕ} (hQ : 1 < Q) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ((n : ℝ) ^ δ) ^ 3 ≤ ((Q : ℝ) ^ (6 * δ)) ^ (Nat.log (Q ^ 2) n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ2 : 1 < Q ^ 2 := Nat.one_lt_pow (by decide) hQ
  have hnupper : (n : ℝ) ≤ (Q : ℝ) ^ (2 * (Nat.log (Q ^ 2) n + 1)) := by
    have h := (Nat.lt_pow_succ_log_self hQ2 n).le
    rw [← pow_mul] at h
    exact_mod_cast h
  calc
    ((n : ℝ) ^ δ) ^ 3 = (n : ℝ) ^ (3 * δ) := by
      rw [← Real.rpow_mul_natCast hnR.le]
      congr 1
      ring
    _ ≤ ((Q : ℝ) ^ (2 * (Nat.log (Q ^ 2) n + 1))) ^ (3 * δ) :=
      Real.rpow_le_rpow hnR.le hnupper (by positivity)
    _ = ((Q : ℝ) ^ (6 * δ)) ^ (Nat.log (Q ^ 2) n + 1) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg Q),
        ← Real.rpow_mul_natCast (Nat.cast_nonneg Q)]
      congr 1
      push_cast
      ring

theorem exists_log_scale_decay {Q : ℕ} (hQ : 1 < Q) {P δ : ℝ}
    (hP : 0 ≤ P) (hδ : 0 < δ) (hgap : P * (Q : ℝ) ^ (6 * δ) < Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (P ^ Nat.log (Q ^ 2) n / (Q : ℝ) ^ Nat.log (Q ^ 2) n) * ((n : ℝ) ^ δ) ^ 3 < ε := by
  let T := (Q : ℝ) ^ (6 * δ)
  let r := P / Q * T
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (zero_lt_one.trans hQ)
  have hT : 0 < T := Real.rpow_pos_of_pos hQr _
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_one hQr]
    exact hgap
  have hlim : Tendsto (fun j : ℕ => T * r ^ j) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul T
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨(Q ^ 2) ^ J, pow_pos (pow_pos (zero_lt_one.trans hQ) _) _, ?_⟩
  intro n hn
  have hn0 : 0 < n := (pow_pos (pow_pos (zero_lt_one.trans hQ) _) _).trans_le hn
  have hj : J ≤ Nat.log (Q ^ 2) n := Nat.le_log_of_pow_le (Nat.one_lt_pow (by decide) hQ) hn
  calc
    _ ≤ (P / Q) ^ Nat.log (Q ^ 2) n * T ^ (Nat.log (Q ^ 2) n + 1) := by
      rw [div_pow]
      exact mul_le_mul_of_nonneg_left (log_scale_power_bound hQ hn0 hδ.le) (by positivity)
    _ = T * r ^ Nat.log (Q ^ 2) n := by
      dsimp [r]
      rw [mul_pow, pow_succ]
      ring
    _ < ε := hJ _ hj

end Erdos941.Analytic
