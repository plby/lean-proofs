import ErdosProblems.Erdos1141.Definitions
import ErdosProblems.Erdos1141.SparseEulerProduct

/-!
# Connecting the sparse Euler product to the exact residue-prime set

Every exceptional prime is either a divisor of the modulus or a prime at
which the character is `1`.  The latter are counted by the unchanged
`residuePrimesUpTo` definition.
-/

namespace Pollack17

open scoped BigOperators

theorem mem_residuePrimesUpTo_iff {m p : ℕ} {ε : ℝ}
    {χ : DirichletCharacter ℂ m} :
    p ∈ residuePrimesUpTo m χ ε ↔ p.Prime ∧
      (p : ℝ) ≤ residuePrimeUpperBound m ε ∧ χ (p : ZMod m) = 1 := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, h⟩
    apply Nat.lt_succ_of_le
    exact_mod_cast h.2.1.trans (Nat.le_ceil (residuePrimeUpperBound m ε))

theorem exceptionalPrimes_subset {m X : ℕ} {ε : ℝ}
    (hm : m ≠ 0) (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (hX : (X : ℝ) ≤ residuePrimeUpperBound m ε) :
    exceptionalPrimes χ X ⊆ m.primeFactors ∪ residuePrimesUpTo m χ ε := by
  classical
  intro p hp
  obtain ⟨hpS, hpne⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpX, hprime⟩ := Nat.mem_primesBelow.mp hpS
  rcases hχ (p : ZMod m) with hzero | hone | hneg
  · apply Finset.mem_union_left
    have hnonunit := MulChar.apply_eq_zero_iff.mp hzero
    have hdiv : p ∣ m := by
      simpa only [ZMod.isUnit_iff_coprime, hprime.coprime_iff_not_dvd, not_not] using hnonunit
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hm⟩
  · apply Finset.mem_union_right
    exact mem_residuePrimesUpTo_iff.mpr ⟨hprime,
      (show (p : ℝ) ≤ X by exact_mod_cast Nat.lt_succ_iff.mp hpX).trans hX, hone⟩
  · exact (hpne hneg).elim

theorem exceptionalPrimes_card_le {m X : ℕ} {ε : ℝ}
    (hm : m ≠ 0) (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (hX : (X : ℝ) ≤ residuePrimeUpperBound m ε) :
    (exceptionalPrimes χ X).card ≤ m.primeFactors.card + (residuePrimesUpTo m χ ε).card :=
  (Finset.card_le_card (exceptionalPrimes_subset hm χ hχ hX)).trans
    (Finset.card_union_le _ _)

theorem primeFactors_card_le_log {m : ℕ} (hm : 0 < m) :
    (m.primeFactors.card : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
  have hpow : 2 ^ m.primeFactors.card ≤ m := by
    calc
      2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ m.primeFactors, p := by
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hcast : (2 : ℝ) ^ m.primeFactors.card ≤ (m : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos (by norm_num) _) hcast
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

end Pollack17
