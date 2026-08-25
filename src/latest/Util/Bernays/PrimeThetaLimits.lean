import Util.Bernays.CharacterPrimeDistribution
import Util.Bernays.LogWeightRemoval

/-!
# Natural-endpoint limits for prime logarithmic sums
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem ordinarySum_eq_cumsum_succ {a : ℕ → ℝ} (ha₀ : a 0 = 0) (N : ℕ) :
    ordinarySum a N = cumsum a (N + 1) := by
  rw [cumsum, Nat.range_succ_eq_Icc_zero, Finset.Icc_eq_cons_Ioc (Nat.zero_le N),
    Finset.sum_cons, ha₀, zero_add]
  simp only [ordinarySum, ← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add]

theorem nat_succ_div_self_tendsto :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_add 1
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  dsimp only [Function.comp_def]
  push_cast
  field_simp

theorem ordinarySum_div_tendsto_of_cumsum {a : ℕ → ℝ} (ha₀ : a 0 = 0) {c : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum a N / (N : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => ordinarySum a N / (N : ℝ)) atTop (𝓝 c) := by
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  have hm := hshift.mul nat_succ_div_self_tendsto
  rw [mul_one] at hm
  apply hm.congr'
  apply Filter.Eventually.of_forall
  intro N
  change (cumsum a (N + 1) / ((N + 1 : ℕ) : ℝ)) * (((N + 1 : ℕ) : ℝ) / N) =
    ordinarySum a N / N
  rw [ordinarySum_eq_cumsum_succ ha₀]
  have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact div_mul_div_cancel₀ hne

theorem psi_eq_ordinarySum (N : ℕ) :
    Chebyshev.psi (N : ℝ) = ordinarySum ArithmeticFunction.vonMangoldt N := by
  simp only [Chebyshev.psi, Nat.floor_natCast, ordinarySum,
    ← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add]

theorem psi_div_tendsto_one :
    Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  simpa only [psi_eq_ordinarySum] using
    ordinarySum_div_tendsto_of_cumsum (by simp : ArithmeticFunction.vonMangoldt 0 = 0) WeakPNT

theorem primePowerError_div_tendsto_zero :
    Tendsto (fun N : ℕ => (Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)) / (N : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ) / sqrt (N : ℝ)) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbound : Tendsto (fun N : ℕ => 2 * sqrt (N : ℝ) * log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
    have h := hlog.const_mul 2
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hsp : sqrt (N : ℝ) ≠ 0 := (sqrt_pos.mpr hNp).ne'
    change 2 * (log (N : ℝ) / sqrt (N : ℝ)) = _
    field_simp
    rw [sq_sqrt hNp.le]
  apply squeeze_zero' _ _ hbound
  · exact Filter.Eventually.of_forall fun N => div_nonneg
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_le_div_of_nonneg_right
      ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hN)))
      (Nat.cast_nonneg N)

theorem theta_div_tendsto_one :
    Tendsto (fun N : ℕ => Chebyshev.theta (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have h := psi_div_tendsto_one.sub primePowerError_div_tendsto_zero
  rw [sub_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun _ => by dsimp only; ring

noncomputable def realCharacterTheta {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow, (χ p).re * log p

theorem characterTheta_error_le {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    |ordinarySum (fun n => (χ n).re * ArithmeticFunction.vonMangoldt n) N - realCharacterTheta χ N| ≤
      Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
  have heq : ordinarySum (fun n => (χ n).re * ArithmeticFunction.vonMangoldt n) N -
      realCharacterTheta χ N = ∑ n ∈ Finset.Icc 1 N,
        if n.Prime then 0 else (χ n).re * ArithmeticFunction.vonMangoldt n := by
    rw [realCharacterTheta, ← Nat.primesLE, Nat.primesLE_eq_filter_Icc_one,
      ordinarySum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n.Prime
    · simp [hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
    · simp [hn]
  rw [heq, Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast, ← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add, Finset.sum_filter]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : n.Prime
  · simp [hn]
  · simp only [hn, if_false, not_false_eq_true, if_true, abs_mul,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_mul_of_nonneg_right
      ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))
      ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)

theorem realCharacterTheta_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => realCharacterTheta χ N / (N : ℝ)) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n => (χ n).re * ArithmeticFunction.vonMangoldt n
  have hψ : Tendsto (fun N : ℕ => ordinarySum a N / (N : ℝ)) atTop (𝓝 0) :=
    ordinarySum_div_tendsto_of_cumsum (by simp [a]) (realTwistedMangoldt_div_tendsto_zero χ hχ)
  have he : Tendsto (fun N : ℕ => (ordinarySum a N - realCharacterTheta χ N) / (N : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ primePowerError_div_tendsto_zero
    intro N
    rw [Real.norm_eq_abs, abs_div]
    rw [show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
    exact div_le_div_of_nonneg_right (characterTheta_error_le χ N) (Nat.cast_nonneg N)
  have h := hψ.sub he
  rw [sub_self] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun _ => by dsimp only; ring

end Bernays
