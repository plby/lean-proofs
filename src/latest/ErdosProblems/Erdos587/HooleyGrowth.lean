import ErdosProblems.Erdos587.HooleyDelta
import ErdosProblems.Erdos1148.DivisorBounds

/-!
# Growth bounds for the short-progression transfer

Delta has both an exponential prime-multiplicity majorant and a uniform
subpower majorant. Large least prime factors therefore give a constant
cost when the argument is bounded by a fixed power of the prime cutoff.
-/

open scoped BigOperators

namespace Erdos587

def deltaPrimeMultiplicity (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p

lemma card_divisors_le_two_pow_multiplicity (n : ℕ) :
    n.divisors.card ≤ 2 ^ deltaPrimeMultiplicity n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Nat.card_divisors hn, deltaPrimeMultiplicity, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod'
    intro p hp
    exact_mod_cast Erdos1148.DukeArithmetic.nat_add_one_le_two_pow (n.factorization p)

lemma pow_deltaPrimeMultiplicity_le {P n : ℕ} (hn : n ≠ 0)
    (hmin : ∀ p ∈ n.primeFactors, P ≤ p) : P ^ deltaPrimeMultiplicity n ≤ n := by
  rw [deltaPrimeMultiplicity, ← Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact Nat.pow_le_pow_left (hmin p hp) _
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

lemma card_divisors_rough_le {P X n r K : ℕ} (hP : 2 ≤ P) (hn : n ≠ 0)
    (hmin : ∀ p ∈ n.primeFactors, P ≤ p) (hX : X ≤ P ^ K) (hnX : n ≤ X ^ r) :
    n.divisors.card ≤ 2 ^ (K * r) := by
  have hpow : P ^ deltaPrimeMultiplicity n ≤ P ^ (K * r) := by
    calc
      _ ≤ n := pow_deltaPrimeMultiplicity_le hn hmin
      _ ≤ X ^ r := hnX
      _ ≤ (P ^ K) ^ r := Nat.pow_le_pow_left hX r
      _ = _ := (pow_mul _ _ _).symm
  have homega : deltaPrimeMultiplicity n ≤ K * r :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < P)).mp hpow
  exact (card_divisors_le_two_pow_multiplicity n).trans
    (Nat.pow_le_pow_right (by norm_num) homega)

/-- A real-exponential version retains the dependence on the least
prime-factor cutoff, as needed when summing logarithmic ranges. -/
lemma card_divisors_rough_exp_le {P N n : ℕ} (hP : 2 ≤ P) (hn : n ≠ 0)
    (hmin : ∀ p ∈ n.primeFactors, P ≤ p) (hnN : n ≤ N) :
    (n.divisors.card : ℝ) ≤
      Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log (P : ℝ)) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hpow := pow_deltaPrimeMultiplicity_le hn hmin
  have hlog := Real.log_le_log (pow_pos hP0 (deltaPrimeMultiplicity n))
    (show (P : ℝ) ^ deltaPrimeMultiplicity n ≤ n by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hlogN := Real.log_le_log hn0 (show (n : ℝ) ≤ N by exact_mod_cast hnN)
  have homega : (deltaPrimeMultiplicity n : ℝ) ≤ Real.log (N : ℝ) / Real.log (P : ℝ) :=
    (le_div_iff₀ hlogP).mpr (hlog.trans hlogN)
  calc
    _ ≤ (2 : ℝ) ^ deltaPrimeMultiplicity n := by
      exact_mod_cast card_divisors_le_two_pow_multiplicity n
    _ = Real.exp ((deltaPrimeMultiplicity n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_right homega (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
      calc
        _ ≤ (Real.log (N : ℝ) / Real.log (P : ℝ)) * Real.log 2 := h
        _ = _ := by ring)

/-- The precise growth condition used in the one-variable
Nair--Tenenbaum class, proved here even without coprimality of the factors. -/
theorem exists_hooleyDelta_growth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℕ, a ≠ 0 →
      (hooleyDelta (a * b) : ℝ) ≤
        min ((2 : ℝ) ^ deltaPrimeMultiplicity a) (C * (a : ℝ) ^ ε) * hooleyDelta b := by
  obtain ⟨C, hC, hdiv⟩ := Erdos1148.DukeArithmetic.exists_card_divisors_le_rpow hε
  refine ⟨C + 1, by linarith, ?_⟩
  intro a b ha
  have htwo : (a.divisors.card : ℝ) ≤ (2 : ℝ) ^ deltaPrimeMultiplicity a := by
    exact_mod_cast card_divisors_le_two_pow_multiplicity a
  have hpower : (a.divisors.card : ℝ) ≤ (C + 1) * (a : ℝ) ^ ε := by
    have h := hdiv a ha
    have hpos : 0 ≤ (a : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith only [h, hpos]
  calc
    _ ≤ (a.divisors.card : ℝ) * hooleyDelta b := by exact_mod_cast hooleyDelta_mul_le a b
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_min htwo hpower) (by positivity)

end Erdos587
