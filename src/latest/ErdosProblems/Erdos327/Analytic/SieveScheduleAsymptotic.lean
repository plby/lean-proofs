import ErdosProblems.Erdos327.Analytic.SieveSchedule
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Eventual validity of the finite-sieve schedule

The elementary schedule is useful only after the dyadic index dominates
the square of its binary logarithm.  This file derives that fact from the
standard `log² x = o(x)` theorem in Mathlib.
-/

namespace Erdos327.Analytic

open Filter Real Asymptotics

noncomputable section

/-- The real coefficient used to absorb the square of the binary
logarithm in the schedule. -/
def sieveDominanceCoefficient : ℝ :=
  32768 / log 2 ^ 2

theorem sieveDominanceCoefficient_pos :
    0 < sieveDominanceCoefficient := by
  unfold sieveDominanceCoefficient
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The binary height is at most twice the real base-two logarithm once
the argument is at least two. -/
theorem sieveHeight_cast_le_two_mul_logb
    {j : ℕ} (hj : 1 ≤ j) :
    (sieveHeight j : ℝ) ≤
      2 * (log (j + 1 : ℕ) / log 2) := by
  have hn : 2 ≤ j + 1 := by omega
  have hnatlog :
      (Nat.log 2 (j + 1) : ℝ) ≤
        log (j + 1 : ℕ) / log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb (j + 1) 2
  have hlog2 : 0 < log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogmono :
      log (2 : ℝ) ≤ log (j + 1 : ℕ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
      (by
        simpa only [Set.mem_Ioi]
          using (show (0 : ℝ) < (j + 1 : ℕ) by positivity))
      (by exact_mod_cast hn)
  have hone :
      (1 : ℝ) ≤ log (j + 1 : ℕ) / log 2 := by
    exact (le_div_iff₀ hlog2).2 (by simpa using hlogmono)
  unfold sieveHeight
  push_cast
  norm_num [Nat.cast_add] at hnatlog hone ⊢
  linarith

/-- Quantitative real square bound for the binary height. -/
theorem sieveHeight_cast_sq_le
    {j : ℕ} (hj : 1 ≤ j) :
    (sieveHeight j : ℝ) ^ 2 ≤
      4 * log (j + 1 : ℕ) ^ 2 / log 2 ^ 2 := by
  have hheight := sieveHeight_cast_le_two_mul_logb hj
  have hheight0 : 0 ≤ (sieveHeight j : ℝ) := by positivity
  have hlog2 : 0 < log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog0 : 0 ≤ log (j + 1 : ℕ) :=
    Real.log_natCast_nonneg _
  have hratio0 :
      0 ≤ log (j + 1 : ℕ) / log 2 := by positivity
  have hsquare :=
    (sq_le_sq₀ hheight0
      (mul_nonneg (by norm_num) hratio0)).2 hheight
  calc
    (sieveHeight j : ℝ) ^ 2
        ≤ (2 * (log (j + 1 : ℕ) / log 2)) ^ 2 := hsquare
    _ = 4 * log (j + 1 : ℕ) ^ 2 / log 2 ^ 2 := by ring

/-- The schedule dominance hypothesis `32R ≤ j` holds for all sufficiently
large dyadic indices. -/
theorem eventually_sieveSchedule_dominates :
    ∀ᶠ j : ℕ in atTop, 32 * sieveRadius j ≤ j := by
  have hlo :
      (fun x : ℝ ↦ sieveDominanceCoefficient * log x ^ 2)
          =o[atTop] (fun x : ℝ ↦ x) :=
    Real.isLittleO_pow_log_id_atTop.const_mul_left
      sieveDominanceCoefficient
  have hsmall :
      ∀ᶠ x : ℝ in atTop,
        ‖sieveDominanceCoefficient * log x ^ 2‖ ≤ ‖x‖ :=
    hlo.eventuallyLE
  have hcast :
      Tendsto (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmallNat :
      ∀ᶠ j : ℕ in atTop,
        ‖sieveDominanceCoefficient *
            log ((j + 1 : ℕ) : ℝ) ^ 2‖ ≤
          ‖((j + 1 : ℕ) : ℝ)‖ :=
    hsmall.filter_mono hcast
  filter_upwards [hsmallNat, eventually_ge_atTop 1] with j hsmallj hj
  have hlogpos :
      0 < log ((j + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < j + 1 by omega))
  have hcoeffpos := sieveDominanceCoefficient_pos
  have hsmallj' :
      sieveDominanceCoefficient *
          log ((j + 1 : ℕ) : ℝ) ^ 2 ≤
        ((j + 1 : ℕ) : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hcoeffpos, abs_of_pos hlogpos,
      abs_of_pos (show (0 : ℝ) < (j + 1 : ℕ) by positivity)]
      using hsmallj
  have hheight := sieveHeight_cast_sq_le hj
  have hstrict :
      (32 * sieveRadius j : ℕ) < j + 1 := by
    have hhalf :
        (4096 : ℝ) * (sieveHeight j : ℝ) ^ 2 <
          sieveDominanceCoefficient *
            log ((j + 1 : ℕ) : ℝ) ^ 2 := by
      unfold sieveDominanceCoefficient
      have hlog2sq :
          0 < log (2 : ℝ) ^ 2 := sq_pos_of_pos
            (Real.log_pos (by norm_num))
      calc
        (4096 : ℝ) * (sieveHeight j : ℝ) ^ 2
            ≤ 4096 *
                (4 * log ((j + 1 : ℕ) : ℝ) ^ 2 /
                  log 2 ^ 2) :=
              mul_le_mul_of_nonneg_left hheight (by norm_num)
        _ = 16384 * log ((j + 1 : ℕ) : ℝ) ^ 2 /
                log 2 ^ 2 := by ring
        _ < 32768 / log 2 ^ 2 *
              log ((j + 1 : ℕ) : ℝ) ^ 2 := by
              field_simp
              nlinarith [sq_pos_of_pos hlogpos]
    have hcastlt :
        ((32 * sieveRadius j : ℕ) : ℝ) <
          ((j + 1 : ℕ) : ℝ) := by
      have hbound := hhalf.trans_le hsmallj'
      norm_num [sieveRadius, Nat.cast_add] at hbound ⊢
      nlinarith
    exact_mod_cast hcastlt
  omega

end

end Erdos327.Analytic
