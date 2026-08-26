import ErdosProblems.Erdos796.BaselineAsymptotic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit separated polylogarithmic pruning scales

To keep the structural reduction independent of prime-density estimates, we
use more widely separated powers than the manuscript.  Put

* `L(n) = floor(log_2 n) + 1`,
* `W = L^20`, `Z = L^96`, `Y = L^112`,
* `R = L^448 = Y^4`.

The extra separation lets the complete-box and overlap estimates absorb all
dyadic logarithmic factors using only ambient integer interval sizes.
-/

namespace Erdos796

open Filter Topology

namespace PruningScales

/-- A positive integral proxy for `log n`. -/
def logScale (n : ℕ) : ℕ := Nat.log 2 n + 1

def W (n : ℕ) : ℕ := logScale n ^ 20
def Z (n : ℕ) : ℕ := logScale n ^ 96
def Y (n : ℕ) : ℕ := logScale n ^ 112
def R (n : ℕ) : ℕ := logScale n ^ 448

theorem R_eq_Y_pow_four (n : ℕ) : R n = Y n ^ 4 := by
  simp [R, Y, ← pow_mul]

/-- The integral logarithmic scale tends to infinity. -/
theorem tendsto_logScale_atTop : Tendsto logScale atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (2 ^ b)] with n hn
  have hlog : b ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hn
  exact hlog.trans (Nat.le_succ _)

/-- The fixed comparison constant between integral base-two logarithm and
the natural logarithm. -/
noncomputable def logComparisonConstant : ℝ := (Real.log 2)⁻¹ + 1

theorem logComparisonConstant_nonneg : 0 ≤ logComparisonConstant := by
  unfold logComparisonConstant
  positivity

/-- The natural logarithm of the natural variable is eventually at least
one. -/
theorem eventually_one_le_log_natCast :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hlog.eventually (eventually_ge_atTop 1)

/-- Eventual comparison of the integral logarithmic scale with `log n`. -/
theorem eventually_logScale_cast_le :
    ∀ᶠ n : ℕ in atTop,
      (logScale n : ℝ) ≤
        logComparisonConstant * Real.log (n : ℝ) := by
  filter_upwards [eventually_one_le_log_natCast] with n hlog
  have hnatlog : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n :=
    Real.natLog_le_logb n 2
  rw [logScale, Nat.cast_add, Nat.cast_one]
  calc
    (Nat.log 2 n : ℝ) + 1 ≤ Real.logb 2 n + 1 :=
      by linarith
    _ = Real.log (n : ℝ) * (Real.log 2)⁻¹ + 1 := by
      rw [Real.logb, div_eq_mul_inv]
    _ ≤ Real.log (n : ℝ) * (Real.log 2)⁻¹ +
        Real.log (n : ℝ) := by linarith
    _ = logComparisonConstant * Real.log (n : ℝ) := by
      unfold logComparisonConstant
      ring

/-- Every fixed power of `L(n)` is negligible compared with `n`. -/
theorem logScale_pow_div_nat_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => (logScale n : ℝ) ^ k / (n : ℝ))
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ k / (n : ℝ))
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa using! h
  have hupper : Tendsto
      (fun n : ℕ => logComparisonConstant ^ k *
        (Real.log (n : ℝ) ^ k / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using! hbase.const_mul (logComparisonConstant ^ k)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    positivity
  · filter_upwards [eventually_ge_atTop 1, eventually_one_le_log_natCast,
      eventually_logScale_cast_le] with n hn hlogOne hLlog
    have hL : (0 : ℝ) ≤ (logScale n : ℝ) := by positivity
    have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    have hp : (logScale n : ℝ) ^ k ≤
        (logComparisonConstant * Real.log (n : ℝ)) ^ k := by
      exact pow_le_pow_left₀ hL hLlog k
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    calc
      (logScale n : ℝ) ^ k / (n : ℝ) ≤
          (logComparisonConstant * Real.log (n : ℝ)) ^ k /
            (n : ℝ) :=
        (div_le_div_iff_of_pos_right hnpos).mpr hp
      _ = logComparisonConstant ^ k *
          (Real.log (n : ℝ) ^ k / (n : ℝ)) := by
        rw [mul_pow]
        ring
  · exact hupper

/-- Every fixed power of `L(n)` is negligible on the second-order scale
`n/log n`. -/
theorem logScale_pow_div_secondOrder_tendsto_zero (k : ℕ) :
    Tendsto
      (fun n : ℕ => (logScale n : ℝ) ^ k / secondOrderScale n)
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ (k + 1) / (n : ℝ))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 (k + 1) one_ne_zero).comp
        tendsto_natCast_atTop_atTop
    simpa using! h
  have hupper : Tendsto
      (fun n : ℕ => logComparisonConstant ^ k *
        (Real.log (n : ℝ) ^ (k + 1) / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using! hbase.const_mul (logComparisonConstant ^ k)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1,
      eventually_one_le_log_natCast] with n hn hlogOne
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : (0 : ℝ) < Real.log (n : ℝ) := by linarith
    simp only [secondOrderScale]
    positivity
  · filter_upwards [eventually_ge_atTop 1, eventually_one_le_log_natCast,
      eventually_logScale_cast_le] with n hn hlogOne hLlog
    have hL : (0 : ℝ) ≤ (logScale n : ℝ) := by positivity
    have hlog : (0 : ℝ) < Real.log (n : ℝ) := by linarith
    have hp : (logScale n : ℝ) ^ k ≤
        (logComparisonConstant * Real.log (n : ℝ)) ^ k := by
      exact pow_le_pow_left₀ hL hLlog k
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    unfold secondOrderScale
    calc
      (logScale n : ℝ) ^ k / ((n : ℝ) / Real.log (n : ℝ)) =
          (logScale n : ℝ) ^ k * Real.log (n : ℝ) /
            (n : ℝ) := by field_simp
      _ ≤ (logComparisonConstant * Real.log (n : ℝ)) ^ k *
          Real.log (n : ℝ) / (n : ℝ) := by
        exact (div_le_div_iff_of_pos_right hnpos).mpr
          (mul_le_mul_of_nonneg_right hp hlog.le)
      _ = logComparisonConstant ^ k *
          (Real.log (n : ℝ) ^ (k + 1) / (n : ℝ)) := by
        rw [mul_pow, pow_succ]
        ring
  · exact hupper

/-- A fixed polylogarithmic factor times `sqrt n` is still negligible on
the second-order scale. -/
theorem logScale_pow_mul_sqrt_div_secondOrder_tendsto_zero (k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((logScale n : ℝ) ^ k * (n.sqrt : ℝ)) / secondOrderScale n)
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun n : ℕ =>
        Real.log (n.sqrt : ℝ) ^ (k + 1) / (n.sqrt : ℝ))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 (k + 1) one_ne_zero).comp
        tendsto_natSqrtCast_atTop
    simpa using! h
  let C : ℝ := logComparisonConstant ^ k * 3 ^ (k + 1)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (pow_nonneg logComparisonConstant_nonneg k)
      (pow_nonneg (by norm_num) (k + 1))
  have hupper : Tendsto
      (fun n : ℕ => C *
        (Real.log (n.sqrt : ℝ) ^ (k + 1) / (n.sqrt : ℝ)))
      atTop (nhds 0) := by
    simpa using! hbase.const_mul C
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 9] with n hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by norm_num; omega)
    simp only [secondOrderScale]
    positivity
  · filter_upwards [eventually_ge_atTop 9,
      eventually_logScale_cast_le,
      eventually_log_le_three_log_sqrt] with n hn hLlog hlogsqrt
    let x : ℝ := n.sqrt
    let ell : ℝ := Real.log (n : ℝ)
    let ellS : ℝ := Real.log (n.sqrt : ℝ)
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hellpos : 0 < ell := by
      dsimp [ell]
      exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hellSpos : 0 < ellS := by
      dsimp [ellS]
      exact Real.log_pos (by
        exact_mod_cast (show 1 < n.sqrt by
          have hsqrt : 3 ≤ n.sqrt := by
            rw [Nat.le_sqrt]
            omega
          omega))
    have hxsq : x * x ≤ (n : ℝ) := by
      dsimp [x]
      exact_mod_cast Nat.sqrt_le n
    have hxdiv : x / (n : ℝ) ≤ 1 / x := by
      rw [div_le_div_iff₀ hnpos hxpos]
      nlinarith
    have hLpow : (logScale n : ℝ) ^ k ≤
        (logComparisonConstant * ell) ^ k := by
      exact pow_le_pow_left₀ (by positivity) (by simpa [ell] using! hLlog) k
    have hellpow : ell ^ (k + 1) ≤ (3 * ellS) ^ (k + 1) := by
      exact pow_le_pow_left₀ hellpos.le
        (by simpa [ell, ellS] using! hlogsqrt) (k + 1)
    unfold secondOrderScale
    change ((logScale n : ℝ) ^ k * x) / ((n : ℝ) / ell) ≤
      C * (ellS ^ (k + 1) / x)
    calc
      ((logScale n : ℝ) ^ k * x) / ((n : ℝ) / ell) =
          ((logScale n : ℝ) ^ k * ell) * (x / (n : ℝ)) := by
        field_simp
      _ ≤ ((logScale n : ℝ) ^ k * ell) * (1 / x) := by
        exact mul_le_mul_of_nonneg_left hxdiv
          (mul_nonneg (by positivity) hellpos.le)
      _ ≤ ((logComparisonConstant * ell) ^ k * ell) * (1 / x) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLpow hellpos.le) (by positivity)
      _ = (logComparisonConstant ^ k * ell ^ (k + 1)) / x := by
        rw [mul_pow, pow_succ]
        field_simp
      _ ≤ (logComparisonConstant ^ k * (3 * ellS) ^ (k + 1)) / x := by
        apply (div_le_div_iff_of_pos_right hxpos).mpr
        exact mul_le_mul_of_nonneg_left hellpow
          (pow_nonneg logComparisonConstant_nonneg k)
      _ = C * (ellS ^ (k + 1) / x) := by
        dsimp [C]
        rw [mul_pow]
        ring
  · exact hupper

/-- The natural logarithm is bounded above by the integral scale `L(n)` for
positive natural inputs. -/
theorem log_natCast_le_logScale {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ (logScale n : ℝ) := by
  have hnlt : n < 2 ^ logScale n := by
    simpa [logScale] using!
      (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n)
  have hcast : (n : ℝ) < ((2 ^ logScale n : ℕ) : ℝ) := by
    exact_mod_cast hnlt
  have hloglt := Real.log_lt_log (by positivity) hcast
  have hlogpow : Real.log (((2 ^ logScale n : ℕ) : ℝ)) =
      (logScale n : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogpow] at hloglt
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  calc
    Real.log (n : ℝ) ≤ (logScale n : ℝ) * Real.log 2 := hloglt.le
    _ ≤ (logScale n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlogTwo (Nat.cast_nonneg _)
    _ = (logScale n : ℝ) := by ring

/-- The quotient `log n / L(n)^7` tends to zero. -/
theorem log_div_logScale_pow_seven_tendsto_zero :
    Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (logScale n : ℝ) ^ 7)
      atTop (nhds 0) := by
  have hLtop : Tendsto (fun n : ℕ => (logScale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_logScale_atTop
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (logScale n : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hLtop
  have hupper : Tendsto
      (fun n : ℕ => (1 : ℝ) / (logScale n : ℝ) ^ 6)
      atTop (nhds 0) := by
    have hpow := hinv.pow 6
    have heq :
        (fun n : ℕ => ((1 : ℝ) / (logScale n : ℝ)) ^ 6) =ᶠ[atTop]
          (fun n : ℕ => (1 : ℝ) / (logScale n : ℝ) ^ 6) := by
      apply Eventually.of_forall
      intro n
      change ((1 : ℝ) / (logScale n : ℝ)) ^ 6 =
        (1 : ℝ) / (logScale n : ℝ) ^ 6
      rw [div_pow]
      norm_num
    have ht := hpow.congr' heq
    simpa using! ht
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hLpos : (0 : ℝ) < (logScale n : ℝ) := by
      exact_mod_cast (show 0 < logScale n by simp [logScale])
    have hlogL : Real.log (n : ℝ) ≤ (logScale n : ℝ) :=
      log_natCast_le_logScale (by omega)
    apply (div_le_iff₀ (pow_pos hLpos 7)).mpr
    calc
      Real.log (n : ℝ) ≤ (logScale n : ℝ) := hlogL
      _ = ((1 : ℝ) / (logScale n : ℝ) ^ 6) *
          (logScale n : ℝ) ^ 7 := by
        field_simp

/-- With the chosen even exponent, the square root of `Z` is exact. -/
theorem sqrt_Z (n : ℕ) :
    Real.sqrt (Z n : ℝ) = (logScale n : ℝ) ^ 48 := by
  have hnonneg : 0 ≤ (logScale n : ℝ) ^ 48 := by positivity
  have hpow : ((Z n : ℕ) : ℝ) = ((logScale n : ℝ) ^ 48) ^ 2 := by
    rw [Z, Nat.cast_pow, ← pow_mul]
  rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

/-- The four scales have their required strict ordering eventually. -/
theorem eventually_scale_order :
    ∀ᶠ n : ℕ in atTop,
      1 < W n ∧ W n < Z n ∧ Z n < Y n ∧ Y n < R n := by
  filter_upwards [tendsto_logScale_atTop.eventually
      (eventually_ge_atTop 2)] with n hn
  have hbase : 1 < logScale n := hn
  have h20_96 : 20 < 96 := by omega
  have h96_112 : 96 < 112 := by omega
  have hY : 1 < Y n := by
    exact one_lt_pow₀ hbase (by norm_num)
  constructor
  · exact one_lt_pow₀ hbase (by norm_num)
  constructor
  · exact Nat.pow_lt_pow_right hbase h20_96
  constructor
  · exact Nat.pow_lt_pow_right hbase h96_112
  · rw [R_eq_Y_pow_four]
    simpa only [pow_one] using!
      Nat.pow_lt_pow_right hY (by norm_num : 1 < 4)

/-- The largest cofactor cutoff is eventually below `sqrt n`. -/
theorem eventually_R_le_sqrt :
    ∀ᶠ n : ℕ in atTop, R n ≤ n.sqrt := by
  have hratio := logScale_pow_div_nat_tendsto_zero 896
  have hlt : ∀ᶠ n : ℕ in atTop,
      (logScale n : ℝ) ^ 896 / (n : ℝ) < 1 :=
    hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1, hlt] with n hn hratioOne
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hpowReal : (logScale n : ℝ) ^ 896 < (n : ℝ) := by
    exact (div_lt_one hnpos).mp hratioOne
  have hpowNat : logScale n ^ 896 ≤ n := by
    exact_mod_cast hpowReal.le
  rw [Nat.le_sqrt]
  have hRR : R n * R n = logScale n ^ 896 := by
    rw [R, ← pow_add]
  rwa [hRR]

/-- All elementary scale hypotheses used by pruning hold eventually. -/
theorem eventually_pruning_scale_hypotheses :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ Z n ∧ Z n ≤ Y n ∧ R n = Y n ^ 4 ∧
        R n ≤ n.sqrt ∧ W n ≤ Z n := by
  filter_upwards [eventually_scale_order, eventually_R_le_sqrt] with n hord hR
  exact ⟨by omega, hord.2.2.1.le, R_eq_Y_pow_four n, hR, hord.2.1.le⟩

end PruningScales

end Erdos796
