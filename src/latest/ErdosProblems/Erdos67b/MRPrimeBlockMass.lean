import ErdosProblems.Erdos67b.MRNarrowPrimePartition
import ErdosProblems.Erdos67b.MRTDensity

/-!
# Reciprocal mass of rounded logarithmic prime blocks

The already proved Mertens bound is applied with both integer endpoints
tracked, including the subtraction of one at the lower endpoint.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrLogPrimeInterval_endpoint_bounds {p q : ℝ} (hp : 2 ≤ p) (hpq : 2 * p ≤ q) :
    3 ≤ (mrLogPrimeInterval p q).1 ∧
      (mrLogPrimeInterval p q).1 ≤ (mrLogPrimeInterval p q).2 ∧
      Real.log (((mrLogPrimeInterval p q).1 - 1 : ℕ) : ℝ) ≤ p ∧
      q / 2 ≤ Real.log ((mrLogPrimeInterval p q).2 : ℝ) := by
  let L : ℕ := ⌈Real.exp p⌉₊
  let U : ℕ := ⌊Real.exp q⌋₊
  have hLp : (3 : ℝ) ≤ L := by
    have hh := Real.add_one_le_exp p
    have hc := Nat.le_ceil (Real.exp p)
    dsimp only [L]
    linarith
  have hL : 3 ≤ L := by exact_mod_cast hLp
  have hLlt : (L : ℝ) < Real.exp p + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hep : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr (by linarith)
  have hshift : Real.exp p + 1 ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith
  have hLeq : (L : ℝ) ≤ Real.exp q :=
    hLlt.le.trans (hshift.trans (Real.exp_le_exp.mpr (by linarith)))
  have hLU : L ≤ U := Nat.le_floor hLeq
  have hLm : (0 : ℝ) < ((L - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < L - 1)
  have hLmexp : (((L - 1 : ℕ) : ℝ)) ≤ Real.exp p := by
    have hc : (((L - 1 : ℕ) : ℝ)) + 1 = L := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ L)
    linarith
  have hlogLm : Real.log (((L - 1 : ℕ) : ℝ)) ≤ p := by
    have hh := Real.log_le_log hLm hLmexp
    simpa only [Real.log_exp] using hh
  have hU0 : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have heq : Real.exp q = Real.exp (q - 1) * Real.exp 1 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heqm : 1 ≤ Real.exp (q - 1) := Real.one_le_exp_iff.mpr (by linarith)
  have hfloor : Real.exp q - 1 ≤ (U : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp q)
    dsimp only [U]
    linarith
  have hUm : Real.exp (q - 1) ≤ (U : ℝ) := by nlinarith
  have hlogU : q / 2 ≤ Real.log (U : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hUm
    rw [Real.log_exp] at hh
    linarith
  exact ⟨hL, hLU, hlogLm, hlogU⟩

theorem mrPrimeBlock_reciprocalMass_eq {L U : ℕ} (hL : 0 < L) :
    (∑ p ∈ primesInBlock (L, U), 1 / (p : ℝ)) =
      PrimeEstimates.reciprocalPrimeInterval (L - 1) U := by
  have hsets : primesInBlock (L, U) = PrimeEstimates.primesInInterval (L - 1) U := by
    ext p
    simp only [mem_primesInBlock, PrimeEstimates.mem_primesInInterval]
    constructor
    · rintro ⟨hp, hLp, hpU⟩
      exact ⟨by omega, hpU, hp⟩
    · rintro ⟨hLmp, hpU, hp⟩
      exact ⟨hp, by omega, hpU⟩
  simp only [PrimeEstimates.reciprocalPrimeInterval, hsets, one_div]

theorem mrLogPrimeInterval_reciprocalMass_lower {p q : ℝ} (hp : 2 ≤ p) (hpq : 2 * p ≤ q) :
    Real.log q - Real.log p - Real.log 2 - 2 * PrimeEstimates.mertensBound ≤
      ∑ l ∈ primesInBlock (mrLogPrimeInterval p q), 1 / (l : ℝ) := by
  obtain ⟨hL, hLU, hlogL, hlogU⟩ := mrLogPrimeInterval_endpoint_bounds hp hpq
  have hmain := reciprocalPrimeInterval_log_log_lower hL hLU
  have hLm : (1 : ℝ) < (((mrLogPrimeInterval p q).1 - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < (mrLogPrimeInterval p q).1 - 1)
  have hloglogL : Real.log (Real.log (((mrLogPrimeInterval p q).1 - 1 : ℕ) : ℝ)) ≤ Real.log p :=
    Real.log_le_log (Real.log_pos hLm) hlogL
  have hloglogU : Real.log q - Real.log 2 ≤ Real.log (Real.log ((mrLogPrimeInterval p q).2 : ℝ)) := by
    have hh := Real.log_le_log (by linarith : 0 < q / 2) hlogU
    simpa only [Real.log_div (by linarith : q ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] using hh
  rw [mrPrimeBlock_reciprocalMass_eq (by omega : 0 < (mrLogPrimeInterval p q).1)]
  linarith

theorem mrLogSchedule_log_ratio {p₁ q₁ : ℝ} (hp : 0 < p₁) (hq : 1 ≤ q₁)
    {j : ℕ} (hj : 1 ≤ j) :
    Real.log (mrLogScheduleUpper q₁ j) - Real.log (mrLogScheduleLower p₁ q₁ j) =
      2 * Real.log (j : ℝ) + Real.log q₁ - Real.log p₁ := by
  have hw : 0 < mrLogScheduleWeight q₁ j := lt_of_lt_of_le (by norm_num) (mrLogScheduleWeight_one_le hq hj)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hq0 : 0 < q₁ := by linarith
  have hQ : mrLogScheduleUpper q₁ j = mrLogScheduleWeight q₁ j * (j : ℝ) ^ 2 * q₁ := by
    unfold mrLogScheduleUpper mrLogScheduleWeight
    rw [pow_add, show q₁ ^ j = q₁ ^ (j - 1) * q₁ by rw [← pow_succ, Nat.sub_add_cancel hj]]
    ring
  rw [hQ, mrLogScheduleLower, Real.log_mul (by positivity) hq0.ne',
    Real.log_mul hw.ne' (by positivity), Real.log_mul hw.ne' hp.ne', Real.log_pow]
  norm_num
  ring

theorem mrScheduledPrimeInterval_reciprocalMass_lower
    {p₁ q₁ : ℝ} (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁)
    {j : ℕ} (hj : 1 ≤ j) :
    2 * Real.log (j : ℝ) + Real.log q₁ - Real.log p₁ - Real.log 2 -
        2 * PrimeEstimates.mertensBound ≤
      ∑ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j), 1 / (p : ℝ) := by
  have hpj : 2 ≤ mrLogScheduleLower p₁ q₁ j :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq hj)
  have hscale : 2 * mrLogScheduleLower p₁ q₁ j ≤ mrLogScheduleUpper q₁ j := by
    have hh := mrLogScheduleLower_le_upper hq hpq hj
    unfold mrLogScheduleLower at hh ⊢
    nlinarith
  have hh := mrLogPrimeInterval_reciprocalMass_lower hpj hscale
  rw [show Real.log (mrLogScheduleUpper q₁ j) - Real.log (mrLogScheduleLower p₁ q₁ j) =
    2 * Real.log (j : ℝ) + Real.log q₁ - Real.log p₁ from mrLogSchedule_log_ratio (by linarith) hq hj] at hh
  exact hh

theorem mrScheduledPrimeInterval_reciprocalMass_ge_two_log
    {p₁ q₁ : ℝ} (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    {j : ℕ} (hj : 1 ≤ j) :
    2 * Real.log (j : ℝ) ≤
      ∑ p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j), 1 / (p : ℝ) := by
  have hh := mrScheduledPrimeInterval_reciprocalMass_lower hp hq hpq hj
  linarith

end

end Erdos67b
