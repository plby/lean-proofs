import ErdosProblems.Erdos117.GlobalCoverBound
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A common logarithmic scale

The integer ceiling logarithm of `n+2` controls all polynomial and
conjugacy-index terms in the constructed cover. The estimates in this file
are purely numerical and do not assume a bound on a derived subgroup.
-/

namespace Erdos117

open Filter Asymptotics
open scoped Topology

def logScale (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

theorem logScale_pos (n : ℕ) : 0 < logScale n := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (n + 2)
  by_contra hn
  have hz : logScale n = 0 := by omega
  change n + 2 ≤ 2 ^ logScale n at h
  rw [hz, pow_zero] at h
  omega

theorem le_two_pow_logScale (n : ℕ) : n + 2 ≤ 2 ^ logScale n :=
  Nat.le_pow_clog (by decide) _

theorem conjugacy_clog_le_logScale (n : ℕ) :
    Nat.clog 2 ((2 * n) ^ 2) ≤ 4 * logScale n := by
  have hn : 2 * n ≤ (n + 2) ^ 2 := by nlinarith
  apply Nat.clog_le_of_le_pow
  calc
    (2 * n) ^ 2 ≤ ((n + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left hn 2
    _ = (n + 2) ^ 4 := by ring
    _ ≤ (2 ^ logScale n) ^ 4 := Nat.pow_le_pow_left (le_two_pow_logScale n) 4
    _ = 2 ^ (4 * logScale n) := by rw [← pow_mul, Nat.mul_comm]

theorem floor_log_le_logScale (n : ℕ) : Nat.log 2 n ≤ logScale n :=
  (Nat.log_le_clog 2 n).trans (Nat.clog_mono_right 2 (by omega))

theorem coverExtensionPolynomial_le_pow (n : ℕ) :
    coverExtensionPolynomial n ≤ (n + 2) ^ 11 := by
  have hbase : 2 ≤ n + 2 := by omega
  have htwo : 2 * n ≤ (n + 2) ^ 2 := by nlinarith
  have hsquare : (2 * n) ^ 2 ≤ (n + 2) ^ 4 := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left htwo 2
  have hterm : (2 * n) ^ 2 * n ≤ (n + 2) ^ 5 := by
    calc
      _ ≤ (n + 2) ^ 4 * (n + 2) := Nat.mul_le_mul hsquare (by omega)
      _ = _ := by ring
  have hone : 1 ≤ (n + 2) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hterm' : (2 * n) ^ 2 * n + 1 ≤ (n + 2) ^ 6 := by
    calc
      _ ≤ 2 * (n + 2) ^ 5 := by omega
      _ ≤ (n + 2) * (n + 2) ^ 5 := Nat.mul_le_mul_right _ hbase
      _ = _ := by ring
  calc
    _ ≤ (n + 2) * (n + 2) ^ 4 * (n + 2) ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul hbase hsquare) hterm'
    _ = _ := by ring

theorem log_coverExtensionPolynomial_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (coverExtensionPolynomial n) ≤ 11 * logScale n := by
  have hC : 0 < coverExtensionPolynomial n := by unfold coverExtensionPolynomial; positivity
  have hpow : coverExtensionPolynomial n ≤ 2 ^ (11 * logScale n) := by
    calc
      _ ≤ (n + 2) ^ 11 := coverExtensionPolynomial_le_pow n
      _ ≤ (2 ^ logScale n) ^ 11 := Nat.pow_le_pow_left (le_two_pow_logScale n) 11
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hreal : (coverExtensionPolynomial n : ℝ) ≤ 2 ^ (11 * logScale n) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by exact_mod_cast hC) hreal
  rw [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  exact hlog.trans (by
    have h := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 11 * (logScale n : ℝ) by positivity)
    simpa only [mul_one] using h)

theorem logScale_le_log (n : ℕ) :
    (logScale n : ℝ) ≤ (2 / Real.log 2) * Real.log ((n : ℝ) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hratio : 1 ≤ Real.log ((n : ℝ) + 2) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa using hbase)
  have hceil : (logScale n : ℝ) ≤ Real.log ((n : ℝ) + 2) / Real.log 2 + 1 := by
    have hnonneg : 0 ≤ Real.logb (2 : ℝ) ((n + 2 : ℕ) : ℝ) := by
      simp only [Real.logb, Nat.cast_add, Nat.cast_ofNat]
      positivity
    have h := (Nat.ceil_lt_add_one hnonneg).le
    have heq : ⌈Real.logb (2 : ℝ) ((n + 2 : ℕ) : ℝ)⌉₊ = logScale n := by
      simpa only [Nat.cast_ofNat, logScale] using Real.natCeil_logb_natCast 2 (n + 2)
    rw [heq] at h
    simpa only [Real.logb, Nat.cast_add, Nat.cast_ofNat, logScale] using h
  calc
    _ ≤ Real.log ((n : ℝ) + 2) / Real.log 2 + 1 := hceil
    _ ≤ 2 * (Real.log ((n : ℝ) + 2) / Real.log 2) := by linarith
    _ = _ := by ring

theorem logScale_isBigO_log :
    (fun n : ℕ => (logScale n : ℝ)) =O[atTop] (fun n : ℕ => Real.log ((n : ℝ) + 2)) := by
  apply IsBigO.of_bound (2 / Real.log 2)
  apply Filter.Eventually.of_forall
  intro n
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hlog] using
    logScale_le_log n

theorem sqrt_add_two_isBigO_sqrt :
    (fun n : ℕ => Real.sqrt ((n : ℝ) + 2)) =O[atTop] (fun n : ℕ => Real.sqrt n) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith only [Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n), hn']

theorem log_cube_isLittleO_sqrt :
    (fun n : ℕ => (Real.log ((n : ℝ) + 2)) ^ 3) =o[atTop] (fun n : ℕ => Real.sqrt n) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hshift
  change (fun n : ℕ => (Real.log ((n : ℝ) + 2)) ^ (3 : ℝ)) =o[atTop]
    (fun n : ℕ => ((n : ℝ) + 2) ^ (1 / 2 : ℝ)) at h
  have h' : (fun n : ℕ => (Real.log ((n : ℝ) + 2)) ^ 3) =o[atTop]
      (fun n : ℕ => Real.sqrt ((n : ℝ) + 2)) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_ofNat] using h
  exact h'.trans_isBigO sqrt_add_two_isBigO_sqrt

theorem logScale_cube_isLittleO_sqrt :
    (fun n : ℕ => (logScale n : ℝ) ^ 3) =o[atTop] (fun n : ℕ => Real.sqrt n) :=
  (logScale_isBigO_log.pow 3).trans_isLittleO log_cube_isLittleO_sqrt

theorem eventually_logScale_cube_le_sqrt :
    ∀ᶠ n : ℕ in atTop, (logScale n : ℝ) ^ 3 ≤ Real.sqrt n := by
  have h := logScale_cube_isLittleO_sqrt.def (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h] with n hn
  simpa only [Real.norm_of_nonneg (show 0 ≤ (logScale n : ℝ) ^ 3 by positivity),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), one_mul] using hn

end Erdos117
