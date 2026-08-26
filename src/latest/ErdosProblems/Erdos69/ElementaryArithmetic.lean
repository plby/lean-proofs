import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Arithmetic foundations of the elementary proof of Erdős problem 69

The distinct-prime-divisor count, convergence of the exact binary series,
and the overlap correction for composite dilations.
-/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable section

/-- The number of distinct prime divisors. -/
def omegaCount (n : ℕ) : ℕ := n.primeFactors.card

@[simp] theorem omegaCount_zero : omegaCount 0 = 0 := by
  simp [omegaCount]

@[simp] theorem omegaCount_one : omegaCount 1 = 0 := by
  simp [omegaCount]

theorem omegaCount_eq_cardDistinctFactors (n : ℕ) :
    omegaCount n = ArithmeticFunction.cardDistinctFactors n := by
  simp [omegaCount, ArithmeticFunction.cardDistinctFactors_apply,
    ← Nat.toFinset_factors, List.card_toFinset]

theorem omegaCount_le_add_one (n : ℕ) : omegaCount n ≤ n + 1 := by
  unfold omegaCount
  calc
    n.primeFactors.card ≤ (Finset.range (n + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hprime, hdvd, hn⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd))
    _ = n + 1 := Finset.card_range _

/-- The exact real number in Erdős problem 69; the terms at zero and one vanish. -/
def binaryOmegaSum : ℝ := ∑' n : ℕ, (omegaCount n : ℝ) / 2 ^ n

theorem summable_omegaCount_div_two_pow :
    Summable (fun n : ℕ ↦ (omegaCount n : ℝ) / 2 ^ n) := by
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hweighted : Summable (fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one
      (R := ℝ) 1 (r := (1 / 2 : ℝ)) (by norm_num)
  have hmajor : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) / 2 ^ n) := by
    simpa [div_eq_mul_inv, add_mul, one_div, inv_pow] using hweighted.add hgeo
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity) _ hmajor
  intro n
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast omegaCount_le_add_one n) (by positivity)

/-- Inclusion-exclusion for distinct prime factors, with no coprimality assumption. -/
theorem omegaCount_gcd_add_mul (a m : ℕ) :
    omegaCount (a.gcd m) + omegaCount (a * m) = omegaCount a + omegaCount m := by
  simpa [omegaCount] using
    Nat.sum_primeFactors_gcd_add_sum_primeFactors_mul a m (fun _ ↦ (1 : ℕ))

theorem omegaCount_mul_real (a m : ℕ) :
    (omegaCount (a * m) : ℝ) =
      omegaCount a + omegaCount m - omegaCount (a.gcd m) := by
  have h : (omegaCount (a.gcd m) : ℝ) + omegaCount (a * m) =
      omegaCount a + omegaCount m := by
    exact_mod_cast omegaCount_gcd_add_mul a m
  linarith

theorem primeFactors_gcd_eq_filter {a m : ℕ} (ha : a ≠ 0) (hm : m ≠ 0) :
    (a.gcd m).primeFactors = a.primeFactors.filter (fun p ↦ p ∣ m) := by
  rw [Nat.primeFactors_gcd ha hm]
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, (Nat.mem_primeFactors.mp h.2).2.1⟩
  · intro h
    exact ⟨h.1, Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp h.1).1, h.2, hm⟩⟩

theorem omegaCount_gcd_real {a m : ℕ} (ha : a ≠ 0) (hm : m ≠ 0) :
    (omegaCount (a.gcd m) : ℝ) =
      ∑ p ∈ a.primeFactors, if p ∣ m then (1 : ℝ) else 0 := by
  rw [omegaCount, primeFactors_gcd_eq_filter ha hm]
  simp [Finset.sum_filter]

theorem omegaCount_mul_indicator {a m : ℕ} (ha : a ≠ 0) (hm : m ≠ 0) :
    (omegaCount (a * m) : ℝ) = omegaCount a + omegaCount m -
      ∑ p ∈ a.primeFactors, if p ∣ m then (1 : ℝ) else 0 := by
  rw [omegaCount_mul_real, omegaCount_gcd_real ha hm]

end

end Erdos69.Elementary
