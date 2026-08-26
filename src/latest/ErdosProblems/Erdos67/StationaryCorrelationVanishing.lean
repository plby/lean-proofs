import ErdosProblems.Erdos67.StationaryPairBlocks
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Every nonzero correlation vanishes

If a correlation were nonzero, prime cancellation would force a positive
mean square error. Abel comparison transfers this lower bound to reciprocal
prime weights, contradicting the proved finite entropy budget.
-/

open scoped BigOperators Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem sum_prime_indicator_eq_primeBelow (g : ℕ → ℝ) (X : ℕ) :
    (∑ p ∈ range X, if p.Prime then g p else 0) = ∑ p : PrimeBelow X, g p.val.val := by
  classical
  let S := (univ : Finset (Fin X)).filter (fun p ↦ p.val.Prime)
  have hs := sum_subtype (p := fun p : Fin X ↦ p.val.Prime) (F := inferInstance)
    S (fun p ↦ by simp only [S, mem_filter, mem_univ, true_and]) (fun p ↦ g p.val)
  calc
    _ = ∑ p : Fin X, if p.val.Prime then g p.val else 0 :=
      (Fin.sum_univ_eq_sum_range _ X).symm
    _ = ∑ p ∈ S, g p.val := (sum_filter _ _).symm
    _ = _ := hs

noncomputable def primeError (Q : ProbabilityMeasure Configuration) (d : ℕ+) (p : ℕ) : ℝ :=
  if p.Prime then (correlation Q (d.val : ℤ) - correlation Q ((d.val * p : ℕ) : ℤ)) ^ 2 else 0

theorem primeError_nonneg (Q : ProbabilityMeasure Configuration) (d : ℕ+) (p : ℕ) :
    0 ≤ primeError Q d p := by unfold primeError; split_ifs <;> positivity

theorem summable_primeError_harmonic (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (d : ℕ+) : Summable (fun p ↦ primeError Q d p / (p : ℝ)) := by
  apply summable_of_sum_range_le (fun p ↦ div_nonneg (primeError_nonneg Q d p) (Nat.cast_nonneg _))
    (c := 18 * ((2 * d.val + 1 : ℕ) : ℝ) * Real.log 2)
  intro X
  have he (p : ℕ) : primeError Q d p / (p : ℝ) =
      if p.Prime then (correlation Q (d.val : ℤ) -
        correlation Q ((p : ℤ) * (d.val : ℤ))) ^ 2 / p else 0 := by
    unfold primeError
    split_ifs <;> simp only [zero_div, Nat.cast_mul, mul_comm]
  simp_rw [he]
  rw [sum_prime_indicator_eq_primeBelow]
  exact harmonic_prime_correlation_budget Q hQ hCD d.val X

theorem correlation_eq_zero_of_pos (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+) :
    correlation Q (d.val : ℤ) = 0 := by
  classical
  by_contra hr
  let c : ℝ := correlation Q (d.val : ℤ) ^ 2 / 2
  have hc : 0 < c := div_pos (sq_pos_of_ne_zero hr) (by norm_num)
  let a : ℕ → ℝ := fun p ↦ if p.Prime then c else 0
  let b : ℕ → ℝ := primeError Q d
  have ha : ∀ n, 0 ≤ a n := by intro n; dsimp [a]; split_ifs <;> positivity
  have hb : ∀ n, 0 ≤ b n := primeError_nonneg Q d
  have ha0 : a 0 = 0 := by simp only [a, Nat.not_prime_zero, if_false]
  have hb0 : b 0 = 0 := by simp only [b, primeError, Nat.not_prime_zero, if_false]
  have hpa (N : ℕ) : (∑ n ∈ range N, pairBlock a n) =
      c * ((Nat.primesLE (2 * N)).card : ℝ) := by
    rw [pairBlock_prefix a ha0, ← sum_filter]
    simp only [Nat.primesLE_eq_filter_range, sum_const, nsmul_eq_mul]
    ring
  have hpb (N : ℕ) : (∑ n ∈ range N, pairBlock b n) =
      ∑ p ∈ Nat.primesLE (2 * N),
        (correlation Q (d.val : ℤ) - correlation Q ((d.val * p : ℕ) : ℤ)) ^ 2 := by
    rw [pairBlock_prefix b hb0]
    simp only [b, primeError, Nat.primesLE_eq_filter_range, sum_filter]
  have hprefix : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, pairBlock a n) ≤ ∑ n ∈ range N, pairBlock b n := by
    filter_upwards [eventually_prime_error_lower Q hQ σ hσ d hr] with N hN
    rw [hpa, hpb]
    exact hN
  have hbs : Summable (fun n ↦ pairBlock b n / (n + 1 : ℕ)) :=
    summable_pairBlock_harmonic b hb (summable_primeError_harmonic Q hQ hCD d)
  have has := summable_harmonic_of_pairBlock a ha
    (summable_harmonic_of_eventual_prefix_le (pairBlock a) (pairBlock b)
      (pairBlock_nonneg a ha) (pairBlock_nonneg b hb) hprefix hbs)
  apply not_summable_one_div_on_primes
  have ht := has.mul_left (1 / c)
  have he : (fun p : ℕ ↦ (1 / c) * (a p / (p : ℝ))) =
      Set.indicator {p : ℕ | p.Prime} (fun p : ℕ ↦ (1 : ℝ) / p) := by
    funext p
    by_cases hp : p.Prime
    · simp only [a, Set.indicator, Set.mem_ofPred_eq, if_pos hp, one_div]
      field_simp [hc.ne']
    · simp only [a, Set.indicator, Set.mem_ofPred_eq, if_neg hp, zero_div, mul_zero]
  rwa [he] at ht

end Erdos67.StationaryModel
