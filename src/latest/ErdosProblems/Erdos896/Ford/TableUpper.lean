/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.TableBridge
import ErdosProblems.Erdos896.Ford.ReductionCollapse

/-!
# Analytic preparation for the multiplication-table upper bound

This module supplies the elementary truncation and geometric-series estimates
used to sum the dyadic cover from `TableBridge.lean`.  We truncate after

`halfLog N = Nat.log 2 N / 2`.

Thus `2 ^ halfLog N` has square-root size.  The terminal interval is absorbed
by the Ford scale, all divisor windows before the truncation tend uniformly to
infinity, and the admissibility inequality gives the required comparison of
the square of a divisor-window endpoint with the product-shell endpoint.
-/

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators

/-- Half of the integral base-two logarithm, used as the terminal dyadic
shell index. -/
def halfLog (N : ℕ) : ℕ := Nat.log 2 N / 2

lemma two_pow_halfLog_le (N : ℕ) (hN : 0 < N) :
    2 ^ halfLog N ≤ N := by
  exact (Nat.pow_le_pow_right (by omega) (Nat.div_le_self (Nat.log 2 N) 2)).trans
    (Nat.pow_log_le_self 2 hN.ne')

lemma two_pow_two_mul_halfLog_le (N : ℕ) (hN : 0 < N) :
    2 ^ (2 * halfLog N) ≤ N := by
  apply (Nat.pow_le_pow_right (by omega) ?_).trans (Nat.pow_log_le_self 2 hN.ne')
  unfold halfLog
  omega

/-- The complementary upper estimate: `N` is below four times the square of
the truncation denominator. -/
lemma lt_two_pow_two_mul_halfLog_add_two (N : ℕ) :
    N < 2 ^ (2 * halfLog N + 2) := by
  apply (Nat.lt_pow_succ_log_self (b := 2) (by omega) N).trans_le
  apply Nat.pow_le_pow_right (by omega)
  unfold halfLog
  omega

lemma halfLog_ge_of_two_pow_two_mul_le {M N : ℕ}
    (h : 2 ^ (2 * M) ≤ N) : M ≤ halfLog N := by
  have hN : N ≠ 0 := by
    intro hzero
    subst N
    simp at h
  have hlog : 2 * M ≤ Nat.log 2 N :=
    (Nat.le_log_iff_pow_le (by omega) hN).2 h
  unfold halfLog
  omega

/-- The lower endpoints `N / 2^(j+1)` tend to infinity uniformly over all
windows `j < halfLog N`. -/
theorem eventually_uniform_window_large (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ j < halfLog N,
      M ≤ N / 2 ^ (j + 1) := by
  filter_upwards [eventually_ge_atTop (2 ^ (2 * M))] with N hN j hj
  have hK : M ≤ halfLog N := halfLog_ge_of_two_pow_two_mul_le hN
  have hMpow : M ≤ 2 ^ halfLog N :=
    M.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by omega) hK)
  have hjK : j + 1 ≤ halfLog N := by omega
  have hdpow : 2 ^ (j + 1) ≤ 2 ^ halfLog N :=
    Nat.pow_le_pow_right (by omega) hjK
  apply (Nat.le_div_iff_mul_le (by positivity)).2
  calc
    M * 2 ^ (j + 1) ≤ 2 ^ halfLog N * 2 ^ (j + 1) :=
      Nat.mul_le_mul_right _ hMpow
    _ ≤ 2 ^ halfLog N * 2 ^ halfLog N :=
      Nat.mul_le_mul_left _ hdpow
    _ = 2 ^ (2 * halfLog N) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ N := two_pow_two_mul_halfLog_le N (by
      exact lt_of_lt_of_le (by positivity : 0 < 2 ^ (2 * M)) hN)

/-- If the product-shell and divisor-window indices are admissible, the
square of the integral lower window lies below the shell endpoint. -/
lemma window_sq_le_div_pow {N j k : ℕ} (hk : k ≤ 2 * j + 2) :
    (N / 2 ^ (j + 1)) ^ 2 ≤ N ^ 2 / 2 ^ k := by
  apply (Nat.le_div_iff_mul_le (by positivity)).2
  have hdiv : (N / 2 ^ (j + 1)) * 2 ^ (j + 1) ≤ N :=
    Nat.div_mul_le_self _ _
  have hsq := Nat.mul_self_le_mul_self hdiv
  have hpow : 2 ^ k ≤ 2 ^ (2 * j + 2) :=
    Nat.pow_le_pow_right (by omega) hk
  calc
    (N / 2 ^ (j + 1)) ^ 2 * 2 ^ k ≤
        (N / 2 ^ (j + 1)) ^ 2 * 2 ^ (2 * j + 2) :=
      Nat.mul_le_mul_left _ hpow
    _ = ((N / 2 ^ (j + 1)) * 2 ^ (j + 1)) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ N ^ 2 := by simpa [pow_two] using hsq

/-- Every retained dyadic window is at least the truncation power. -/
lemma two_pow_halfLog_le_window {N j : ℕ} (hN : 0 < N)
    (hj : j < halfLog N) :
    2 ^ halfLog N ≤ N / 2 ^ (j + 1) := by
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ (j + 1))]
  have hjK : j + 1 ≤ halfLog N := by omega
  have hpow : 2 ^ (j + 1) ≤ 2 ^ halfLog N :=
    Nat.pow_le_pow_right (by omega) hjK
  calc
    2 ^ halfLog N * 2 ^ (j + 1) ≤
        2 ^ halfLog N * 2 ^ halfLog N :=
      Nat.mul_le_mul_left _ hpow
    _ = 2 ^ (2 * halfLog N) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ N := two_pow_two_mul_halfLog_le N hN

/-- Before the half-logarithmic truncation, the slowly varying denominator
at a window base differs from its value at `N` by only an absolute factor. -/
lemma logDenom896_le_dyadic_halfLog
    {N j : ℕ} (hN : 128 ≤ N) (hj : j < halfLog N) :
    Erdos896.logDenom896 N ≤
      64 * Erdos896.logDenom896 (N / 2 ^ (j + 1)) := by
  let L : ℕ := Nat.log 2 N
  let k : ℕ := 2 ^ (j + 1)
  let T : ℕ := N / k
  have hN0 : N ≠ 0 := by omega
  have hk : 0 < k := by positivity
  have hjL : j < L / 2 := by simpa [L, halfLog] using hj
  have hexp : 2 * (j + 1) ≤ L := by omega
  have hkpow : k * k = 2 ^ (2 * (j + 1)) := by
    dsimp [k]
    rw [← pow_add]
    congr 1
    omega
  have hpow_le_log : 2 ^ (2 * (j + 1)) ≤ 2 ^ L :=
    Nat.pow_le_pow_right (by omega) hexp
  have hpow_log_le_N : 2 ^ L ≤ N := by
    simpa [L] using Nat.pow_log_le_self 2 hN0
  have hkkN : k * k ≤ N := by
    rw [hkpow]
    exact hpow_le_log.trans hpow_log_le_N
  have hkT : k ≤ T := by
    change k ≤ N / k
    rw [Nat.le_div_iff_mul_le hk]
    exact hkkN
  have hTpos : 0 < T := hk.trans_le hkT
  have hNlt : N < k * (T + 1) := by
    simpa [T] using Nat.lt_mul_div_succ N hk
  have hNlt2 : N < 2 * T ^ 2 := by
    rw [Nat.pow_two]
    nlinarith
  have hT9 : 9 ≤ T := by
    by_contra h
    have hT8 : T ≤ 8 := by omega
    rw [Nat.pow_two] at hNlt2
    nlinarith
  have hN3 : 3 ≤ N := by omega
  have h2T9 : 9 ≤ 2 * T := by omega
  have h2T3 : 3 ≤ 2 * T := by omega
  have hN_sq : N ≤ (2 * T) ^ 2 := by
    rw [Nat.pow_two] at hNlt2 ⊢
    nlinarith
  have h2T_Tsq : 2 * T ≤ T ^ 2 := by
    rw [Nat.pow_two]
    nlinarith
  change Erdos896.logDenom896 N ≤ 64 * Erdos896.logDenom896 T
  calc
    Erdos896.logDenom896 N ≤ Erdos896.logDenom896 ((2 * T) ^ 2) :=
      Erdos896.logDenom896_mono hN3 hN_sq
    _ ≤ 8 * Erdos896.logDenom896 (2 * T) :=
      Erdos896.logDenom896_sq_le (2 * T) h2T9
    _ ≤ 8 * Erdos896.logDenom896 (T ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (Erdos896.logDenom896_mono h2T3 h2T_Tsq) (by norm_num)
    _ ≤ 64 * Erdos896.logDenom896 T := by
      nlinarith [Erdos896.logDenom896_sq_le T hT9]

private theorem dyadic_real_window_nat_bounds
    (N j d : ℕ)
    (hlower : (N : ℝ) / (2 : ℝ) ^ (j + 1) < (d : ℝ))
    (hupper : (d : ℝ) ≤ (N : ℝ) / (2 : ℝ) ^ j) :
    N / 2 ^ (j + 1) < d ∧ d ≤ 2 * (N / 2 ^ (j + 1)) + 1 := by
  let t : ℕ := 2 ^ j
  have ht : 0 < t := pow_pos (by decide) _
  have htwo_t : 0 < 2 * t := Nat.mul_pos (by decide) ht
  have hpowNat : 2 ^ (j + 1) = 2 * t := by
    simp [t, pow_succ, mul_comm]
  have hpowReal : (2 : ℝ) ^ (j + 1) = 2 * (t : ℝ) := by
    simp [t, pow_succ, mul_comm]
  have hfloorMul : (N / (2 * t)) * (2 * t) ≤ N := Nat.div_mul_le_self _ _
  have hfloorReal : ((N / (2 * t) : ℕ) : ℝ) ≤
      (N : ℝ) / (2 * (t : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (t : ℝ))).2
    exact_mod_cast hfloorMul
  have hlowerNat : N / (2 * t) < d := by
    have hcast : ((N / (2 * t) : ℕ) : ℝ) < (d : ℝ) :=
      hfloorReal.trans_lt (by simpa [hpowReal] using hlower)
    exact_mod_cast hcast
  have hupperMulR : (d : ℝ) * (t : ℝ) ≤ (N : ℝ) := by
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ))).mp
      (by simpa [t] using hupper)
  have hupperMul : d * t ≤ N := by exact_mod_cast hupperMulR
  have hNlt : N < (2 * t) * (N / (2 * t) + 1) :=
    Nat.lt_mul_div_succ N htwo_t
  have hmulLt : d * t < (2 * (N / (2 * t)) + 2) * t := by
    calc
      d * t ≤ N := hupperMul
      _ < (2 * t) * (N / (2 * t) + 1) := hNlt
      _ = (2 * (N / (2 * t)) + 2) * t := by ring
  have hdlt : d < 2 * (N / (2 * t)) + 2 :=
    Nat.lt_of_mul_lt_mul_right hmulLt
  constructor
  · simpa [hpowNat] using hlowerNat
  · rw [hpowNat]
    omega

private theorem dyadic_HSetR_subset_nat_endpoint (x N j : ℕ) :
    HSetR x ((N : ℝ) / (2 : ℝ) ^ (j + 1))
        ((N : ℝ) / (2 : ℝ) ^ j) ⊆
      HSet x (N / 2 ^ (j + 1)) (2 * (N / 2 ^ (j + 1))) ∪
        multiplesUpTo x (2 * (N / 2 ^ (j + 1)) + 1) := by
  intro n hn
  obtain ⟨hnPos, hnx, d, hdn, hdLower, hdUpper⟩ := mem_HSetR.mp hn
  obtain ⟨hdLowerNat, hdUpperNat⟩ :=
    dyadic_real_window_nat_bounds N j d hdLower hdUpper
  by_cases hdMid : d ≤ 2 * (N / 2 ^ (j + 1))
  · exact Finset.mem_union_left _
      (mem_HSet.mpr ⟨hnPos, hnx, d, hdn, hdLowerNat, hdMid⟩)
  · apply Finset.mem_union_right
    have hdEq : d = 2 * (N / 2 ^ (j + 1)) + 1 := by omega
    subst d
    have hendpointPos : 0 < 2 * (N / 2 ^ (j + 1)) + 1 := by omega
    have hquotPos : 0 < n / (2 * (N / 2 ^ (j + 1)) + 1) :=
      Nat.div_pos (Nat.le_of_dvd hnPos hdn) hendpointPos
    have hquotLe : n / (2 * (N / 2 ^ (j + 1)) + 1) ≤
        x / (2 * (N / 2 ^ (j + 1)) + 1) := Nat.div_le_div_right hnx
    apply Finset.mem_image.mpr
    refine ⟨n / (2 * (N / 2 ^ (j + 1)) + 1),
      Finset.mem_Icc.mpr ⟨hquotPos, hquotLe⟩, ?_⟩
    exact Nat.div_mul_cancel hdn

/-- Rounding a real dyadic window loses only the single possible upper
endpoint, whose multiples have the displayed exact cardinality bound. -/
theorem HR_dyadic_window_le_H_add_endpoint (x N j : ℕ) :
    HR x ((N : ℝ) / (2 : ℝ) ^ (j + 1))
        ((N : ℝ) / (2 : ℝ) ^ j) ≤
      H x (N / 2 ^ (j + 1)) (2 * (N / 2 ^ (j + 1))) +
        x / (2 * (N / 2 ^ (j + 1)) + 1) := by
  calc
    HR x ((N : ℝ) / (2 : ℝ) ^ (j + 1))
        ((N : ℝ) / (2 : ℝ) ^ j) ≤
        (HSet x (N / 2 ^ (j + 1)) (2 * (N / 2 ^ (j + 1))) ∪
          multiplesUpTo x (2 * (N / 2 ^ (j + 1)) + 1)).card :=
      Finset.card_le_card (dyadic_HSetR_subset_nat_endpoint x N j)
    _ ≤ (HSet x (N / 2 ^ (j + 1)) (2 * (N / 2 ^ (j + 1)))).card +
        (multiplesUpTo x (2 * (N / 2 ^ (j + 1)) + 1)).card :=
      Finset.card_union_le _ _
    _ ≤ H x (N / 2 ^ (j + 1)) (2 * (N / 2 ^ (j + 1))) +
        (Finset.Icc 1 (x / (2 * (N / 2 ^ (j + 1)) + 1))).card := by
      exact Nat.add_le_add_left Finset.card_image_le _
    _ = H x (N / 2 ^ (j + 1)) (2 * (N / 2 ^ (j + 1))) +
        x / (2 * (N / 2 ^ (j + 1)) + 1) := by simp [H]

lemma self_le_four_mul_two_pow_halfLog_sq (N : ℕ) :
    N ≤ 4 * (2 ^ halfLog N) ^ 2 := by
  have h := (lt_two_pow_two_mul_halfLog_add_two N).le
  calc
    N ≤ 2 ^ (2 * halfLog N + 2) := h
    _ = 4 * (2 ^ halfLog N) ^ 2 := by
      rw [pow_add, show 2 * halfLog N = halfLog N * 2 by omega, pow_mul]
      norm_num
      ring

/-- A deliberately coarse eighth-power estimate.  It is sufficient to
compare the slowly varying logarithmic denominator with `2 ^ halfLog N`. -/
lemma self_le_two_pow_halfLog_eight (N : ℕ) (hN : 4 ≤ N) :
    N ≤ (2 ^ halfLog N) ^ 8 := by
  have hlog : 2 ≤ Nat.log 2 N :=
    (Nat.le_log_iff_pow_le (by omega) (by omega : N ≠ 0)).2 (by
      norm_num
      exact hN)
  have hK : 1 ≤ halfLog N := by
    unfold halfLog
    omega
  have hd : 2 ≤ 2 ^ halfLog N := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hK
  have hfour : 4 ≤ (2 ^ halfLog N) ^ 6 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ halfLog N) ^ 2 := Nat.pow_le_pow_left hd 2
      _ ≤ (2 ^ halfLog N) ^ 6 :=
        Nat.pow_le_pow_right (by positivity) (by omega)
  calc
    N ≤ 4 * (2 ^ halfLog N) ^ 2 := self_le_four_mul_two_pow_halfLog_sq N
    _ ≤ (2 ^ halfLog N) ^ 6 * (2 ^ halfLog N) ^ 2 :=
      Nat.mul_le_mul_right _ hfour
    _ = (2 ^ halfLog N) ^ 8 := by rw [← pow_add]

theorem eventually_logDenom896_le_two_pow_halfLog :
    ∀ᶠ N : ℕ in atTop,
      Erdos896.logDenom896 N ≤ ((2 ^ halfLog N : ℕ) : ℝ) := by
  filter_upwards [eventually_logDenom896_le_eighth_rpow,
    eventually_ge_atTop 4] with N hslow hN
  have hnat : N ≤ (2 ^ halfLog N) ^ 8 :=
    self_le_two_pow_halfLog_eight N hN
  have hreal : (N : ℝ) ≤ (((2 ^ halfLog N : ℕ) : ℝ) ^ (8 : ℕ)) := by
    exact_mod_cast hnat
  have hrpow := Real.rpow_le_rpow (Nat.cast_nonneg N) hreal
    (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hcollapse :
      ((((2 ^ halfLog N : ℕ) : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8)) =
        ((2 ^ halfLog N : ℕ) : ℝ) := by
    simpa [one_div] using Real.pow_rpow_inv_natCast
      (show 0 ≤ ((2 ^ halfLog N : ℕ) : ℝ) by positivity)
      (by norm_num : (8 : ℕ) ≠ 0)
  exact hslow.trans (hrpow.trans_eq hcollapse)

/-- The terminal real interval has size bounded by the Erdős--Ford scale. -/
theorem terminal_isBigO_scale896 :
    (fun N : ℕ ↦ (N : ℝ) ^ (2 : ℕ) /
      ((2 ^ halfLog N : ℕ) : ℝ)) =O[atTop] Erdos896.scale896 := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_logDenom896_le_two_pow_halfLog,
    eventually_ge_atTop 3] with N hden hN
  have hnum : 0 ≤ (N : ℝ) ^ (2 : ℕ) := by positivity
  have hdenPos : 0 < Erdos896.logDenom896 N :=
    Erdos896.logDenom896_pos hN
  have hpowPos : 0 < ((2 ^ halfLog N : ℕ) : ℝ) := by positivity
  rw [one_mul, Real.norm_of_nonneg
      (div_nonneg hnum hpowPos.le),
    Real.norm_of_nonneg (Erdos896.scale896_pos hN).le]
  rw [Erdos896.scale896]
  exact div_le_div_of_nonneg_left hnum hdenPos hden

/-- The exact natural-cardinality version of the terminal interval is also
bounded by the Erdős--Ford scale. -/
theorem terminalNat_isBigO_scale896 :
    (fun N : ℕ ↦ ((N ^ 2 / 2 ^ halfLog N : ℕ) : ℝ)) =O[atTop]
      Erdos896.scale896 := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_logDenom896_le_two_pow_halfLog,
    eventually_ge_atTop 3] with N hden hN
  have hnum : 0 ≤ (N : ℝ) ^ (2 : ℕ) := by positivity
  have hdenPos : 0 < Erdos896.logDenom896 N :=
    Erdos896.logDenom896_pos hN
  have hpowPos : 0 < ((2 ^ halfLog N : ℕ) : ℝ) := by positivity
  rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Erdos896.scale896_pos hN).le,
    Erdos896.scale896]
  calc
    ((N ^ 2 / 2 ^ halfLog N : ℕ) : ℝ) ≤
        ((N ^ 2 : ℕ) : ℝ) / ((2 ^ halfLog N : ℕ) : ℝ) :=
      Nat.cast_div_le
    _ = (N : ℝ) ^ (2 : ℕ) / ((2 ^ halfLog N : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
    _ ≤ (N : ℝ) ^ (2 : ℕ) / Erdos896.logDenom896 N :=
      div_le_div_of_nonneg_left hnum hdenPos hden

/-- The finite first moment of the binary geometric series.  This is the
constant-cost summation used after reversing the admissible `j,k` sums. -/
theorem sum_succ_mul_inv_two_pow_le_four (K : ℕ) :
    (∑ k ∈ Finset.range K,
      ((k + 1 : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)⁻¹) ≤ 4 := by
  have hmul : HasSum
      (fun k : ℕ ↦ (k : ℝ) * ((1 : ℝ) / 2) ^ k) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 : ℝ) / 2‖ < 1 by norm_num)
    norm_num at h
    exact h
  have hsum : HasSum
      (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ k) 4 := by
    convert hmul.add hasSum_geometric_two using 1
    · ext k
      push_cast
      ring
    · norm_num
  have hterm (k : ℕ) :
      ((k + 1 : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)⁻¹ =
        ((k + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ k := by
    congr 1
    norm_num [Nat.cast_pow, inv_pow, div_pow]
  simp_rw [hterm]
  exact (hsum.summable.sum_le_tsum (Finset.range K) fun _ _ ↦ by positivity).trans_eq
    hsum.tsum_eq

/-! ## Pointwise majorization of one table window -/

/-- The real scale of the terminal interval. -/
noncomputable def tableTerminalScale896 (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 : ℕ) / ((2 ^ halfLog N : ℕ) : ℝ)

lemma tableTerminalScale896_nonneg (N : ℕ) :
    0 ≤ tableTerminalScale896 N := by
  unfold tableTerminalScale896
  positivity

/-- A single real dyadic window is controlled by a geometric shell factor.
The first summand is Ford's `H` estimate; the second absorbs the one endpoint
created when the real window is rounded to natural endpoints. -/
lemma tableHR_window_le_shell_majorant
    {C : ℝ} {Y₀ N k j : ℕ}
    (hC : 0 ≤ C)
    (hH : ∀ x y : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
      (H x y (2 * y) : ℝ) ≤
        C * (x : ℝ) / Erdos896.logDenom896 y)
    (hN : 128 ≤ N) (hk : k < halfLog N)
    (hj : j ∈ admissibleWindows k)
    (hyY₀ : Y₀ ≤ N / 2 ^ (j + 1))
    (hy9 : 9 ≤ N / 2 ^ (j + 1)) :
    (HR (N ^ 2 / 2 ^ k)
        ((N : ℝ) / (2 : ℝ) ^ (j + 1))
        ((N : ℝ) / (2 : ℝ) ^ j) : ℝ) ≤
      (64 * C * Erdos896.scale896 N + tableTerminalScale896 N) *
        ((2 ^ k : ℕ) : ℝ)⁻¹ := by
  let X : ℕ := N ^ 2 / 2 ^ k
  let y : ℕ := N / 2 ^ (j + 1)
  let K : ℕ := halfLog N
  have hjData := mem_admissibleWindows.mp hj
  have hjK : j < K := hjData.1.trans_lt hk
  have hNpos : 0 < N := by omega
  have hy9' : 9 ≤ y := by simpa [y] using hy9
  have hy3 : 3 ≤ y := by omega
  have hLN : 0 < Erdos896.logDenom896 N :=
    Erdos896.logDenom896_pos (by omega)
  have hLy : 0 < Erdos896.logDenom896 y :=
    Erdos896.logDenom896_pos hy3
  have hdenComp : Erdos896.logDenom896 N ≤
      64 * Erdos896.logDenom896 y := by
    simpa [K, y] using logDenom896_le_dyadic_halfLog hN hjK
  have hinvDen : (Erdos896.logDenom896 y)⁻¹ ≤
      64 * (Erdos896.logDenom896 N)⁻¹ := by
    have hdiv : 1 / Erdos896.logDenom896 y ≤
        64 / Erdos896.logDenom896 N := by
      rw [div_le_div_iff₀ hLy hLN]
      simpa using hdenComp
    simpa [one_div, div_eq_mul_inv] using hdiv
  have hXcast : (X : ℝ) ≤
      (N : ℝ) ^ (2 : ℕ) * ((2 ^ k : ℕ) : ℝ)⁻¹ := by
    calc
      (X : ℝ) = ((N ^ 2 / 2 ^ k : ℕ) : ℝ) := by rfl
      _ ≤ ((N ^ 2 : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) := Nat.cast_div_le
      _ = (N : ℝ) ^ (2 : ℕ) * ((2 ^ k : ℕ) : ℝ)⁻¹ := by
        rw [Nat.cast_pow]
        ring
  have hHmajor : (H X y (2 * y) : ℝ) ≤
      (64 * C * Erdos896.scale896 N) *
        ((2 ^ k : ℕ) : ℝ)⁻¹ := by
    have hbase := hH X y (by simpa [y] using hyY₀)
      (by simpa [X, y] using window_sq_le_div_pow hjData.2)
    calc
      (H X y (2 * y) : ℝ) ≤
          C * (X : ℝ) / Erdos896.logDenom896 y := hbase
      _ ≤ C * ((N : ℝ) ^ (2 : ℕ) *
          ((2 ^ k : ℕ) : ℝ)⁻¹) /
            Erdos896.logDenom896 y := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXcast hC) hLy.le
      _ ≤ C * ((N : ℝ) ^ (2 : ℕ) *
          ((2 ^ k : ℕ) : ℝ)⁻¹) *
            (64 * (Erdos896.logDenom896 N)⁻¹) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinvDen
          (mul_nonneg hC (mul_nonneg (by positivity) (by positivity)))
      _ = (64 * C * Erdos896.scale896 N) *
          ((2 ^ k : ℕ) : ℝ)⁻¹ := by
        unfold Erdos896.scale896
        ring
  have hpowWindow : 2 ^ K ≤ y := by
    simpa [K, y] using two_pow_halfLog_le_window hNpos hjK
  have hendpointDen : (2 ^ K : ℕ) ≤ 2 * y + 1 := by omega
  have hEndpoint :
      ((X / (2 * y + 1) : ℕ) : ℝ) ≤
        tableTerminalScale896 N * ((2 ^ k : ℕ) : ℝ)⁻¹ := by
    have hInv : (((2 * y + 1 : ℕ) : ℝ))⁻¹ ≤
        (((2 ^ K : ℕ) : ℝ))⁻¹ := by
      exact (inv_le_inv₀ (by positivity) (by positivity)).2
        (by exact_mod_cast hendpointDen)
    calc
      ((X / (2 * y + 1) : ℕ) : ℝ) ≤
          (X : ℝ) / ((2 * y + 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (X : ℝ) * (((2 * y + 1 : ℕ) : ℝ))⁻¹ := by ring
      _ ≤ ((N : ℝ) ^ (2 : ℕ) * ((2 ^ k : ℕ) : ℝ)⁻¹) *
          (((2 ^ K : ℕ) : ℝ))⁻¹ :=
        mul_le_mul hXcast hInv (by positivity) (by positivity)
      _ = tableTerminalScale896 N * ((2 ^ k : ℕ) : ℝ)⁻¹ := by
        unfold tableTerminalScale896
        simp only [K]
        ring
  have hbridge :
      (HR X ((N : ℝ) / (2 : ℝ) ^ (j + 1))
          ((N : ℝ) / (2 : ℝ) ^ j) : ℝ) ≤
        (H X y (2 * y) : ℝ) + ((X / (2 * y + 1) : ℕ) : ℝ) := by
    exact_mod_cast HR_dyadic_window_le_H_add_endpoint X N j
  calc
    (HR (N ^ 2 / 2 ^ k)
        ((N : ℝ) / (2 : ℝ) ^ (j + 1))
        ((N : ℝ) / (2 : ℝ) ^ j) : ℝ) =
        (HR X ((N : ℝ) / (2 : ℝ) ^ (j + 1))
          ((N : ℝ) / (2 : ℝ) ^ j) : ℝ) := by rfl
    _ ≤ (H X y (2 * y) : ℝ) + ((X / (2 * y + 1) : ℕ) : ℝ) := hbridge
    _ ≤ (64 * C * Erdos896.scale896 N) *
          ((2 ^ k : ℕ) : ℝ)⁻¹ +
        tableTerminalScale896 N * ((2 ^ k : ℕ) : ℝ)⁻¹ :=
      add_le_add hHmajor hEndpoint
    _ = (64 * C * Erdos896.scale896 N + tableTerminalScale896 N) *
        ((2 ^ k : ℕ) : ℝ)⁻¹ := by ring

lemma admissibleWindows_card_le (k : ℕ) :
    (admissibleWindows k).card ≤ k + 1 := by
  unfold admissibleWindows
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Summing the pointwise shell majorant costs only the first moment of the
binary geometric series. -/
theorem tableHSum_le_of_H_bound
    {C : ℝ} {Y₀ N : ℕ}
    (hC : 0 ≤ C)
    (hH : ∀ x y : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
      (H x y (2 * y) : ℝ) ≤
        C * (x : ℝ) / Erdos896.logDenom896 y)
    (hN : 128 ≤ N)
    (hlarge : ∀ j < halfLog N,
      max Y₀ 9 ≤ N / 2 ^ (j + 1)) :
    (tableHSum N (halfLog N) : ℝ) ≤
      4 * (64 * C * Erdos896.scale896 N + tableTerminalScale896 N) := by
  let A : ℝ :=
    64 * C * Erdos896.scale896 N + tableTerminalScale896 N
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC)
        (Erdos896.scale896_pos (by omega)).le)
      (tableTerminalScale896_nonneg N)
  rw [tableHSum]
  push_cast
  calc
    (∑ k ∈ Finset.range (halfLog N),
        ∑ j ∈ admissibleWindows k,
          (HR (N ^ 2 / 2 ^ k)
            ((N : ℝ) / (2 : ℝ) ^ (j + 1))
            ((N : ℝ) / (2 : ℝ) ^ j) : ℝ)) ≤
      ∑ k ∈ Finset.range (halfLog N),
        ((k + 1 : ℕ) : ℝ) *
          (A * ((2 ^ k : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK : k < halfLog N := Finset.mem_range.mp hk
      calc
        (∑ j ∈ admissibleWindows k,
            (HR (N ^ 2 / 2 ^ k)
              ((N : ℝ) / (2 : ℝ) ^ (j + 1))
              ((N : ℝ) / (2 : ℝ) ^ j) : ℝ)) ≤
          ∑ j ∈ admissibleWindows k,
            A * ((2 ^ k : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro j hj
          have hjK : j < halfLog N :=
            (mem_admissibleWindows.mp hj).1.trans_lt hkK
          have hjLarge := hlarge j hjK
          simpa [A] using tableHR_window_le_shell_majorant hC hH hN hkK hj
            ((le_max_left Y₀ 9).trans hjLarge)
            ((le_max_right Y₀ 9).trans hjLarge)
        _ = ((admissibleWindows k).card : ℝ) *
            (A * ((2 ^ k : ℕ) : ℝ)⁻¹) := by simp
        _ ≤ ((k + 1 : ℕ) : ℝ) *
            (A * ((2 ^ k : ℕ) : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast admissibleWindows_card_le k)
            (mul_nonneg hA (by positivity))
    _ = A * (∑ k ∈ Finset.range (halfLog N),
        ((k + 1 : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ A * 4 := mul_le_mul_of_nonneg_left
      (sum_succ_mul_inv_two_pow_le_four (halfLog N)) hA
    _ = 4 * (64 * C * Erdos896.scale896 N +
        tableTerminalScale896 N) := by simp [A]; ring

/-! ## Multiplication-table upper bound -/

/-- The dyadic `H`-sum is bounded by the Erdős--Ford scale whenever Ford's
uniform local `H` estimate is available. -/
theorem tableHSum_isBigO_scale896_of_H_bound
    (hbound : ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ,
      ∀ x y : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
        (H x y (2 * y) : ℝ) ≤
          C * (x : ℝ) / Erdos896.logDenom896 y) :
    (fun N : ℕ ↦ (tableHSum N (halfLog N) : ℝ)) =O[atTop]
      Erdos896.scale896 := by
  obtain ⟨C, hC, Y₀, hH⟩ := hbound
  apply IsBigO.of_bound (256 * C + 4)
  filter_upwards [eventually_uniform_window_large (max Y₀ 9),
    eventually_logDenom896_le_two_pow_halfLog,
    eventually_ge_atTop 128] with N hlarge hden hN
  have hscale : 0 < Erdos896.scale896 N :=
    Erdos896.scale896_pos (by omega)
  have hterminal : tableTerminalScale896 N ≤ Erdos896.scale896 N := by
    have hnum : 0 ≤ (N : ℝ) ^ (2 : ℕ) := by positivity
    have hdenPos : 0 < Erdos896.logDenom896 N :=
      Erdos896.logDenom896_pos (by omega)
    unfold tableTerminalScale896 Erdos896.scale896
    exact div_le_div_of_nonneg_left hnum hdenPos hden
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg hscale.le]
  calc
    (tableHSum N (halfLog N) : ℝ) ≤
        4 * (64 * C * Erdos896.scale896 N +
          tableTerminalScale896 N) :=
      tableHSum_le_of_H_bound hC.le hH hN hlarge
    _ ≤ 4 * (64 * C * Erdos896.scale896 N +
          Erdos896.scale896 N) := by
      gcongr
    _ = (256 * C + 4) * Erdos896.scale896 N := by ring

/-- The exact upper-bound API consumed by `UpperBridge.lean`: the concrete
multiplication table is `O` of the Ford scale. -/
theorem multiplicationTable_isBigO_scale896_of_H_bound
    (hbound : ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ,
      ∀ x y : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
        (H x y (2 * y) : ℝ) ≤
          C * (x : ℝ) / Erdos896.logDenom896 y) :
    (fun N : ℕ ↦ ((Erdos896.multiplicationTable N).card : ℝ)) =O[atTop]
      Erdos896.scale896 :=
  multiplicationTable_isBigO_of_terminal_isBigO_of_tableHSum_isBigO
    halfLog Erdos896.scale896 terminalNat_isBigO_scale896
      (tableHSum_isBigO_scale896_of_H_bound hbound)

/-- Complete conditional upper estimate from the sharp weight-sum scale. -/
theorem multiplicationTable_isBigO_scale896_of_weight_estimate
    (hweight : ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ T : ℕ,
      ∀ t : ℕ, T ≤ t → fordWeightSum t ≤ Cweight * fordWeightScale t) :
    (fun N : ℕ ↦ ((Erdos896.multiplicationTable N).card : ℝ)) =O[atTop]
      Erdos896.scale896 :=
  multiplicationTable_isBigO_scale896_of_H_bound
    (exists_H_le_inv_logDenom_of_weight_estimate hweight)

/-- The unconditional multiplication-table upper bound at Ford's sharp
Erdős--Tenenbaum--Ford scale.  This is the upper API consumed by the final
`IsTheta` assembly. -/
theorem multiplicationTable_isBigO_scale896 :
    (fun N : ℕ ↦ ((Erdos896.multiplicationTable N).card : ℝ)) =O[atTop]
      Erdos896.scale896 :=
  multiplicationTable_isBigO_scale896_of_H_bound
    exists_H_le_inv_logDenom

end Erdos896.Ford
