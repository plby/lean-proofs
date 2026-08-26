import ErdosProblems.Erdos520.CaichLambda2Assembly
import ErdosProblems.Erdos520.ShortIntervalPrimes

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos
namespace Problem520

/-!
# Reciprocal-prime fourth moments for Caich's auxiliary lambda terms

`CaichLambda2Assembly` proves the exact largest-prime reduction and the
Doob--hypercontractive estimate.  This file keeps the short prime interval
instead of discarding it.  The resulting fourth-moment budget is the one
used for both `lambda^(2)` and `lambda^(3)` in Caich's argument.
-/

/-- The classical effective prime number theorem, packaged by
`EffectivePrimeCountingStatement`, is sufficient for every fixed
polylogarithmic smoothing exponent.  This wrapper makes that proposition the
only external analytic input in the short-prime-interval step. -/
theorem eventually_freshReciprocalSum_le_two_div_X_log_of_effectiveStatement
    (hPNT : EffectivePrimeCountingStatement) (A : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ {X a b : ℕ},
      2 ≤ a → a ≤ b → 1 ≤ X → y ≤ a →
      (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
      ((b : ℝ) - (a : ℝ)) ≤ (a : ℝ) / (X : ℝ) →
      freshReciprocalSum a b ≤
        2 / ((X : ℝ) * Real.log (y : ℝ)) := by
  obtain ⟨C, hC, c, hc, N, hN, herror⟩ := hPNT
  have heventually :=
    eventually_freshReciprocalSum_le_two_div_X_log_of_effectivePNT_polylog
      hC.le hc herror A
  filter_upwards [heventually, eventually_ge_atTop N] with
    y hy hNy X a b ha hab hX hya hXpoly hwidth
  exact hy (hNy.trans hya) ha hab hX hya hXpoly hwidth

/-- The elementary divisor estimate at `z / p`, with the logarithm enlarged
to the ambient endpoint `z`.  This version remains valid when `z / p` is
zero, which is useful when summing over an unrestricted prime interval. -/
theorem sum_Ioc_orderedDivisorCount_three_div_le
    (z p : ℕ) (hz : 3 ≤ z) :
    (∑ k ∈ Finset.Ioc 0 (z / p),
        (orderedDivisorCount 3 k : ℝ)) ≤
      ((z / p : ℕ) : ℝ) * (2 * Real.log (z : ℝ)) ^ 2 := by
  by_cases hq : z / p = 0
  · simp [hq]
  have hqpos : 1 ≤ z / p := Nat.one_le_iff_ne_zero.mpr hq
  have hqz : z / p ≤ z := Nat.div_le_self z p
  have hzpos : (0 : ℝ) < (z : ℝ) := by positivity
  have hlogz : 1 ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) :=
      Real.exp_one_lt_three.le.trans (by exact_mod_cast hz)
    exact (Real.le_log_iff_exp_le hzpos).mpr hexp
  have hqRpos : (0 : ℝ) < ((z / p : ℕ) : ℝ) := by positivity
  have hlogmono : Real.log ((z / p : ℕ) : ℝ) ≤
      Real.log (z : ℝ) :=
    Real.log_le_log hqRpos (by exact_mod_cast hqz)
  have hbase : 0 ≤ 1 + Real.log ((z / p : ℕ) : ℝ) := by
    have : 0 ≤ Real.log ((z / p : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqpos)
    linarith
  have hbase_le : 1 + Real.log ((z / p : ℕ) : ℝ) ≤
      2 * Real.log (z : ℝ) := by linarith
  have hdiv := orderedDivisorSummatory_le_one_add_log 3 (z / p)
    (by norm_num) hqpos
  have hcast :
      (∑ k ∈ Finset.Ioc 0 (z / p),
          (orderedDivisorCount 3 k : ℝ)) =
        (orderedDivisorSummatory 3 (z / p) : ℝ) := by
    simp only [orderedDivisorSummatory]
    norm_cast
  rw [hcast]
  exact hdiv.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hbase hbase_le 2) (by positivity))

/-- Summing the exact `n = p*k` reduction and the divisor estimate retains
the reciprocal mass of the short prime interval. -/
theorem sum_squarefree_band_orderedDivisorCount_three_le_reciprocal
    (z a b : ℕ) (hz : 3 ≤ z) :
    (∑ n ∈ (caichLargestPrimeBand z a b).filter Squarefree,
        (orderedDivisorCount 3 n : ℝ)) ≤
      3 * (z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2 *
        freshReciprocalSum a b := by
  have hreduce := sum_squarefree_band_orderedDivisorCount_three_le z a b
  have hreduceR :
      (∑ n ∈ (caichLargestPrimeBand z a b).filter Squarefree,
          (orderedDivisorCount 3 n : ℝ)) ≤
        ∑ p ∈ freshPrimes a b, ∑ k ∈ Finset.Ioc 0 (z / p),
          (3 * orderedDivisorCount 3 k : ℕ) := by
    exact_mod_cast hreduce
  refine hreduceR.trans ?_
  calc
    (∑ p ∈ freshPrimes a b, ∑ k ∈ Finset.Ioc 0 (z / p),
        (3 * orderedDivisorCount 3 k : ℕ)) =
        ∑ p ∈ freshPrimes a b,
          3 * (∑ k ∈ Finset.Ioc 0 (z / p),
            (orderedDivisorCount 3 k : ℝ)) := by
      push_cast
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ freshPrimes a b,
        3 * (((z : ℝ) / (p : ℝ)) *
          (2 * Real.log (z : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := (mem_freshPrimes.mp hp).1
      have hdiv := sum_Ioc_orderedDivisorCount_three_div_le z p hz
      have hcastDiv : ((z / p : ℕ) : ℝ) ≤ (z : ℝ) / (p : ℝ) :=
        Nat.cast_div_le
      have hfactor : 0 ≤ (2 * Real.log (z : ℝ)) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_left
        (hdiv.trans (mul_le_mul_of_nonneg_right hcastDiv hfactor))
        (by norm_num)
    _ = 3 * (z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2 *
          freshReciprocalSum a b := by
      rw [freshReciprocalSum]
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- The squarefree restriction does not change a finite Rademacher sum. -/
theorem sum_caichLargestPrimeBand_eq_sum_squarefree
    (omega : Omega) (z a b : ℕ) :
    (∑ n ∈ caichLargestPrimeBand z a b, f omega n) =
      ∑ n ∈ (caichLargestPrimeBand z a b).filter Squarefree,
        f omega n := by
  rw [← caichFiniteRMFSum_one]
  rw [caichFiniteRMFSum_eq_sum_squarefree]
  simp

/-- Hypercontractivity followed by the exact largest-prime reduction.  This
is the square-root fourth-moment estimate quoted in Caich's proof. -/
theorem caichLambda2Terminal_fourthMoment_sqrt_le_reciprocal
    (z : ℕ) {a b : ℕ} (hz : 3 ≤ z) (hab : a ≤ b) :
    (∫ omega, |caichLambda2Terminal z a b omega| ^ 4 ∂μ) ^ (1 / (2 : ℝ)) ≤
      3 * (z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2 *
        freshReciprocalSum a b := by
  let s := (caichLargestPrimeBand z a b).filter Squarefree
  have hs : s ⊆ Finset.Ioc 0 z := by
    intro n hn
    exact caichLargestPrimeBand_subset_Ioc z a b (Finset.mem_filter.mp hn).1
  have hhyper := caichFiniteRMFSum_hypercontractive
    2 (by norm_num) z s (fun _ => 1) hs
  simp only [caichFiniteRMFSum_one, one_pow, mul_one,
    show 2 * 2 = 4 by norm_num, show 2 * 2 - 1 = 3 by norm_num] at hhyper
  have hterminal : ∀ omega,
      caichLambda2Terminal z a b omega = ∑ n ∈ s, f omega n := by
    intro omega
    rw [caichLambda2Terminal,
      Psi_sub_Psi_eq_sum_caichLargestPrimeBand omega z hab,
      sum_caichLargestPrimeBand_eq_sum_squarefree]
  simp_rw [hterminal]
  exact hhyper.trans
    (sum_squarefree_band_orderedDivisorCount_three_le_reciprocal z a b hz)

/-- Raw fourth-moment form used under the outer `z` integral. -/
theorem integral_abs_caichLambda2Terminal_four_le_reciprocal
    (z : ℕ) {a b : ℕ} (hz : 3 ≤ z) (hab : a ≤ b) :
    (∫ omega, |caichLambda2Terminal z a b omega| ^ 4 ∂μ) ≤
      (3 * (z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2 *
        freshReciprocalSum a b) ^ 2 := by
  let I : ℝ := ∫ omega, |caichLambda2Terminal z a b omega| ^ 4 ∂μ
  let B : ℝ := 3 * (z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2 *
    freshReciprocalSum a b
  have hI : 0 ≤ I := integral_nonneg fun omega => by positivity
  have hroot : I ^ (1 / (2 : ℝ)) ≤ B := by
    simpa only [I, B] using!
      caichLambda2Terminal_fourthMoment_sqrt_le_reciprocal z hz hab
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot 2
  change I ≤ B ^ 2
  calc
    I = (I ^ (1 / (2 : ℝ))) ^ 2 := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hI]
    _ ≤ B ^ 2 := hpow

/-- Doob's inequality retains the reciprocal-prime saving as well. -/
theorem integral_caichLambda2Concrete_max_four_le_reciprocal
    (z : ℕ) {a b : ℕ} (hz : 3 ≤ z) (hab : a ≤ b) :
    ∫ omega, finiteRunningMax
        (fun k omega => |caichLambda2ConcretePath z a b k omega| ^ 2)
        b omega ^ 2 ∂μ ≤
      4 * (3 * (z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2 *
        freshReciprocalSum a b) ^ 2 := by
  have hdoob := integral_caichLambda2Doob_max_four_le z hab
  have hmax := finiteRunningMax_caichLambda2Doob_ae_eq_concrete z a b
  have hintEq :
      (∫ omega, finiteRunningMax
          (fun k omega => |caichLambda2Doob z a b k omega| ^ 2)
          b omega ^ 2 ∂μ) =
        ∫ omega, finiteRunningMax
          (fun k omega => |caichLambda2ConcretePath z a b k omega| ^ 2)
          b omega ^ 2 ∂μ := by
    apply integral_congr_ae
    exact hmax.fun_comp (fun x : ℝ => x ^ 2)
  rw [hintEq] at hdoob
  exact hdoob.trans (mul_le_mul_of_nonneg_left
    (integral_abs_caichLambda2Terminal_four_le_reciprocal z hz hab)
    (by norm_num))

end Problem520
end Erdos
