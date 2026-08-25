import ErdosProblems.Erdos1141.DivisorSumLowerBound
import ErdosProblems.Erdos1141.SparseResiduePrimes

/-!
# Pollack's uniform lower bound for prime quadratic residues

Pollack, *Bounds for the First Several Prime Character Nonresidues* (2017),
Theorem 1.3. The two bounds on the same nonnegative divisor sum contradict
one another if there are fewer than the prescribed power of the logarithm
residue primes. Both bounds are uniform over all quadratic characters.
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem residue_prime_count (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m0 : ℕ, ∀ m : ℕ, m > m0 →
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        Real.rpow (Real.log (m : ℝ)) A ≤ ((residuePrimesUpTo m χ ε).card : ℝ) := by
  obtain ⟨ρ, hρ, hupper⟩ := eventually_few_residue_primes_divisor_sum ε A hε hA
  have hlower := eventually_divisor_sum_lower_bound
    (c := (1 / 4 : ℝ) + ε) (δ := ρ / 2) (by linarith) (half_pos hρ)
  have hresult : ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        Real.rpow (Real.log (m : ℝ)) A ≤ ((residuePrimesUpTo m χ ε).card : ℝ) := by
    filter_upwards [hupper, hlower, eventually_ge_atTop 2] with m hu hl hm
    intro χ hχ
    by_contra hnot
    have hcount : ((residuePrimesUpTo m χ ε).card : ℝ) ≤ (Real.log (m : ℝ)) ^ A :=
      (lt_of_not_ge hnot).le
    have hX : (⌊(m : ℝ) ^ ((1 / 4 : ℝ) + ε)⌋₊ : ℝ) ≤ residuePrimeUpperBound m ε :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsum := (hl χ hχ).trans (hu χ hχ hcount _ hX)
    have hstrict : (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ) <
        (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < m by omega)) (by linarith)
    exact (not_le_of_gt hstrict) hsum
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp hresult
  exact ⟨m0, fun m hm => hm0 m hm.le⟩

end Pollack17
