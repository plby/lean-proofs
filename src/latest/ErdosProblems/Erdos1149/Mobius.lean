/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Möbius identities for Erdős Problem 1149

The analytic constant and the finite coprimality indicator are proved here
without importing the much larger existing Erdős 1102 development.
-/

namespace Erdos1149

open scoped ArithmeticFunction.Moebius LSeries.notation
open ArithmeticFunction
open Filter

/-- The absolutely convergent Möbius Dirichlet series at two has value
`6 / π²`. -/
theorem mobius_div_sq_hasSum :
    HasSum (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2)
      (6 / Real.pi ^ 2) := by
  have hs : (1 : ℝ) < ((2 : ℂ).re) := by norm_num
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at hmul
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hL : L ↗ArithmeticFunction.moebius (2 : ℂ) =
      ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    apply (mul_left_cancel₀
      (div_ne_zero (pow_ne_zero 2 hpi) (by norm_num : (6 : ℂ) ≠ 0)))
    rw [hmul]
    push_cast
    field_simp
  have hsum :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  rw [hL] at hsum
  apply Complex.hasSum_ofReal.mp
  exact HasSum.congr_fun hsum (fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, ArithmeticFunction.moebius]
    · simp [LSeries.term, hn])

/-- Möbius inversion for the indicator of coprimality, in integer form. -/
theorem coprime_indicator_mobius (n m : ℕ) :
    (if n.Coprime m then 1 else 0 : ℤ) =
      ∑ d ∈ (Nat.gcd n m).divisors, ArithmeticFunction.moebius d := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- Möbius inversion for the indicator of coprimality, cast to `ℝ`. -/
theorem coprime_indicator_mobius_real (n m : ℕ) :
    (if n.Coprime m then 1 else 0 : ℝ) =
      ∑ d ∈ (Nat.gcd n m).divisors, (ArithmeticFunction.moebius d : ℝ) := by
  exact_mod_cast coprime_indicator_mobius n m

/-- Divisors of a positive gcd, written as the simultaneous divisors in a
bounded range. -/
theorem gcd_divisors_eq_filter_range {n m : ℕ} (hn : 0 < n) :
    (Nat.gcd n m).divisors =
      (Finset.range (n + 1)).filter (fun d ↦ d ∣ n ∧ d ∣ m) := by
  ext d
  have hg : Nat.gcd n m ≠ 0 := (Nat.gcd_pos_of_pos_left m hn).ne'
  simp only [Nat.mem_divisors, hg, and_true, Finset.mem_filter,
    Finset.mem_range, Nat.dvd_gcd_iff]
  exact ⟨fun h ↦ ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn h.1.1), h.1⟩,
    fun h ↦ ⟨h.2, hg⟩⟩

/-- Divisors of `gcd g Q`, expressed inside the fixed divisor set of `Q`. -/
theorem gcd_divisors_eq_divisors_filter {g Q : ℕ} (hQ : Q ≠ 0) :
    (Nat.gcd g Q).divisors = Q.divisors.filter (fun d ↦ d ∣ g) := by
  ext d
  have hg : Nat.gcd g Q ≠ 0 :=
    (Nat.gcd_pos_of_pos_right g (Nat.pos_of_ne_zero hQ)).ne'
  simp only [Nat.mem_divisors, hg, hQ, and_true, Finset.mem_filter,
    Nat.dvd_gcd_iff]
  aesop

/-- Finite Möbius expansion of avoidance of all prime factors of `Q`. -/
theorem finite_sieve_indicator_mobius {g Q : ℕ} (hQ : Q ≠ 0) :
    (if g.Coprime Q then 1 else 0 : ℝ) =
      ∑ d ∈ Q.divisors.filter (fun d ↦ d ∣ g),
        (ArithmeticFunction.moebius d : ℝ) := by
  rw [coprime_indicator_mobius_real, gcd_divisors_eq_divisors_filter hQ]

/-- Absolute summability of the Möbius Dirichlet series at two. -/
theorem mobius_abs_div_sq_summable :
    Summable
      (fun n : ℕ ↦ |(ArithmeticFunction.moebius n : ℝ)| / (n : ℝ) ^ 2) := by
  simpa [Real.norm_eq_abs, abs_div] using
    (summable_norm_iff.mpr mobius_div_sq_hasSum.summable)

/-- Ordinary initial sums of the Möbius series converge to `6 / π²`. -/
theorem mobius_div_sq_partial_sums_tendsto :
    Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop (nhds (6 / Real.pi ^ 2)) :=
  mobius_div_sq_hasSum.tendsto_sum_nat

/-- The divisor sets of `D!` exhaust every positive integer.  Since the
zero term of the Möbius series vanishes, their partial sums converge to the
same value as the full unconditional sum. -/
theorem mobius_div_sq_factorial_divisor_sums_tendsto :
    Tendsto
      (fun D : ℕ ↦ ∑ d ∈ D.factorial.divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)
      atTop (nhds (6 / Real.pi ^ 2)) := by
  let F : ℕ → Finset ℕ := fun D ↦ insert 0 D.factorial.divisors
  have hF : Tendsto F atTop atTop := by
    rw [tendsto_atTop]
    intro s
    filter_upwards [eventually_ge_atTop (∑ n ∈ s, n)] with D hD
    intro n hn
    by_cases hn0 : n = 0
    · simp [F, hn0]
    have hnle : n ≤ ∑ k ∈ s, k := by
      simpa using (Finset.single_le_sum (s := s) (f := fun k : ℕ ↦ k)
        (fun k _ ↦ Nat.zero_le k) hn)
    have hndvd : n ∣ D.factorial :=
      Nat.dvd_factorial (Nat.pos_of_ne_zero hn0) (hnle.trans hD)
    simp [F, hn0, Nat.mem_divisors, hndvd, Nat.factorial_ne_zero]
  have hs := mobius_div_sq_hasSum
  rw [HasSum] at hs
  have hcomp := hs.comp hF
  convert hcomp using 1
  funext D
  simp [F, ArithmeticFunction.moebius]

end Erdos1149
