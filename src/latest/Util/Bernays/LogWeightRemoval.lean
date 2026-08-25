import Util.Bernays.DirichletTauberian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Removing logarithmic weights

For coefficients between zero and one, replacing `log n` by `log N` in a
partial sum costs at most `4*N`. This elementary estimate follows from a
telescoping square-root bound and is negligible on the Bernays weighted scale.
-/

open Filter Topology Real

namespace Bernays

noncomputable def ordinarySum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n

noncomputable def logarithmicSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * log (n : ℝ)

theorem inv_sqrt_step (n : ℕ) :
    1 / sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (sqrt ((n + 1 : ℕ) : ℝ) - sqrt (n : ℝ)) := by
  have hpos : 0 < sqrt ((n + 1 : ℕ) : ℝ) := sqrt_pos.mpr (by positivity)
  have h₁ : sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 :=
    (sq_sqrt (Nat.cast_nonneg (n + 1))).trans (by norm_num)
  have h₀ := sq_sqrt (Nat.cast_nonneg n)
  apply (div_le_iff₀ hpos).mpr
  nlinarith [sq_nonneg (sqrt ((n + 1 : ℕ) : ℝ) - sqrt (n : ℝ))]

theorem sum_inv_sqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / sqrt (n : ℝ)) ≤ 2 * sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      linarith [inv_sqrt_step N]

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ 2 * sqrt x := by
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr hx)
  rw [log_sqrt hx.le] at h
  linarith

theorem log_weight_error_bounds {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ log (N : ℝ) * ordinarySum a N - logarithmicSum a N ∧
      log (N : ℝ) * ordinarySum a N - logarithmicSum a N ≤ 4 * N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have heq : log (N : ℝ) * ordinarySum a N - logarithmicSum a N =
      ∑ n ∈ Finset.Icc 1 N, a n * (log (N : ℝ) - log (n : ℝ)) := by
    simp only [ordinarySum, logarithmicSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hnpos (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
  have hlog (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : 0 ≤ log (N : ℝ) - log (n : ℝ) :=
    sub_nonneg.mpr (log_le_log (hnpos n hn) (by exact_mod_cast (Finset.mem_Icc.mp hn).2))
  rw [heq]
  constructor
  · exact Finset.sum_nonneg fun n hn => mul_nonneg (ha n) (hlog n hn)
  · calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (log (N : ℝ) - log (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact (mul_le_mul_of_nonneg_right (ha₁ n) (hlog n hn)).trans_eq (one_mul _)
      _ ≤ ∑ n ∈ Finset.Icc 1 N, 2 * sqrt (N : ℝ) * (1 / sqrt (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [← log_div hNpos.ne' (hnpos n hn).ne']
        have h := log_le_two_sqrt (div_pos hNpos (hnpos n hn))
        rw [sqrt_div hNpos.le] at h
        simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h
      _ = 2 * sqrt (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, 1 / sqrt (n : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * sqrt (N : ℝ) * (2 * sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by positivity)
      _ = 4 * N := by nlinarith [sq_sqrt hNpos.le]

theorem ordinarySum_asymptotic_of_logarithmicSum {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {C : ℝ}
    (hlog : Tendsto (fun N : ℕ => logarithmicSum a N /
      ((N : ℝ) * sqrt (log (N : ℝ)))) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ => ordinarySum a N / ((N : ℝ) / sqrt (log (N : ℝ))))
      atTop (𝓝 C) := by
  let E : ℕ → ℝ := fun N =>
    (log (N : ℝ) * ordinarySum a N - logarithmicSum a N) /
      ((N : ℝ) * sqrt (log (N : ℝ)))
  have hden : Tendsto (fun N : ℕ => sqrt (log (N : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbound : Tendsto (fun N : ℕ => 4 / sqrt (log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ← div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (4 : ℝ)
  have hE : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [eventually_ge_atTop 2] with N hN
      exact div_nonneg (log_weight_error_bounds ha ha₁ (by omega)).1 (by positivity)
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hLp : 0 < sqrt (log (N : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast hN))
      calc
        E N ≤ (4 * N) / ((N : ℝ) * sqrt (log (N : ℝ))) :=
          div_le_div_of_nonneg_right (log_weight_error_bounds ha ha₁ (by omega)).2 (by positivity)
        _ = 4 / sqrt (log (N : ℝ)) := by field_simp
  have hsum := hlog.add hE
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hsqrt : sqrt (log (N : ℝ)) ≠ 0 := (sqrt_pos.mpr hLp).ne'
  change logarithmicSum a N / ((N : ℝ) * sqrt (log (N : ℝ))) + E N = _
  dsimp only [E]
  field_simp
  rw [sq_sqrt hLp.le]
  ring

end Bernays
