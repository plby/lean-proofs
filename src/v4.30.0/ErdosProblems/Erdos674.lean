/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 674.
https://www.erdosproblems.com/forum/thread/674

Formal authors:
- Bhavik Mehta

URLs:
- https://www.erdosproblems.com/forum/thread/674#post-2118
-/
import Mathlib

namespace Erdos674

open Nat

def solutionSet : Set (ℕ × ℕ × ℕ) :=
    { (x, y, z) | 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z }

theorem erdos_674 : solutionSet.Nonempty := by
  rw [solutionSet]
  exact ⟨⟨2 ^ 12 * 3 ^ 6, 2 ^ 8 * 3 ^ 8, 2 ^ 11 * 3 ^ 7⟩, by decide +kernel⟩

theorem erdos_674_infinite : solutionSet.Infinite := by
  let i (n : ℕ) : ℕ := 2 ^ n
  let b (n : ℕ) : ℕ := i n - 1
  let K (n : ℕ) : ℕ := 2 ^ (2 * i n * (b n - n)) * (b n ^ b n) ^ 2
  let x (n : ℕ) : ℕ := K n * i n ^ 2
  let y (n : ℕ) : ℕ := K n * b n ^ 2
  let z (n : ℕ) : ℕ := K n * (b n * (2 * i n))
  have hb (n : ℕ) (hn : 2 ≤ n) : n < b n := by induction n, hn using le_induction with grind
  have hb' (n : ℕ) (hn : 2 ≤ n) : b n + 1 = i n := by grind
  have hb₀ (n : ℕ) (hn : 2 ≤ n) : 0 < b n := by grind
  have h (n : ℕ) (hn : 2 ≤ n) : x n ^ x n * y n ^ y n = z n ^ z n := by
    have aux : K n * (i n ^ 2) ^ i n ^ 2 * ((b n ^ 2) ^ b n ^ 2) = 
        (2 * b n * i n) ^ (2 * b n * i n) := by calc
      _ = 2 ^ (2 * (n * i n ^ 2 + i n * (b n - n))) * b n ^ (2 * b n * (b n + 1)) := by ring
      _ = 2 ^ (2 * i n * (n * b n + n + (b n - n))) * b n ^ (2 * b n * i n) := by congr! 2 <;> grind
      _ = 2 ^ (2 * i n * ((n + 1) * b n)) * b n ^ (2 * b n * i n) := by congr! 3; grind
      _ = _ := by ring
    calc
      _ = (K n ^ (i n ^ 2 + b n ^ 2) * (i n ^ 2) ^ i n ^ 2 * ((b n ^ 2) ^ b n ^ 2)) ^ K n := by 
        simp only [x, y]; ring
      _ = (K n ^ (2 * b n * i n + 1) * (i n ^ 2) ^ i n ^ 2 * ((b n ^ 2) ^ b n ^ 2)) ^ K n := by 
        congr! 4; grind
      _ =
          (K n ^ (2 * b n * i n) *
            (K n * (i n ^ 2) ^ i n ^ 2 * ((b n ^ 2) ^ b n ^ 2))) ^ K n := by
        ring
      _ = (K n ^ (2 * b n * i n) * (2 * b n * i n) ^ (2 * b n * i n)) ^ K n := by grind
      _ = z n ^ z n := by simp only [z]; ring
  have hb'' (n : ℕ) (hn : 2 ≤ n) : (b n).factorization 2 = 0 := by 
    grind [factorization_eq_zero_of_not_dvd, two_pow_sub_one_mod_two, one_mod_two_pow_eq_one]
  have hK (n : ℕ) (hn : 2 ≤ n) : (K n).factorization 2 = 2 * i n * (b n - n) := by
    simp [K, prime_two, hb'' n hn]
  have hK' (n : ℕ) (hn : 2 ≤ n) : 0 < (K n).factorization 2 := by simp [hK n hn, hb n hn, i]
  have aux : ∀ n < 2, n.factorization 2 = 0 := by
    intro n hn
    interval_cases n <;> simp
  have hK₁ (n : ℕ) (hn : 2 ≤ n) : 1 < K n := by grind
  have hx (n : ℕ) (hn : 2 ≤ n) : (x n).factorization 2 = (K n).factorization 2 + 2 * n := by
    rw [Nat.factorization_mul (by simp [K]) (by simp [i])]
    simp [i, prime_two]
  have hy (n : ℕ) (hn : 2 ≤ n) : (y n).factorization 2 = (K n).factorization 2 := by
    rw [Nat.factorization_mul (by simp [K]) (by
      exact pow_ne_zero 2 (hb₀ n hn).ne')]
    simp [hb'' n hn]
  have hz (n : ℕ) (hn : 2 ≤ n) : (z n).factorization 2 = (K n).factorization 2 + (n + 1) := by
    rw [Nat.factorization_mul (by simp [K]) (by
      exact Nat.mul_ne_zero (hb₀ n hn).ne' (by simp [i])), Finsupp.add_apply,
      Nat.factorization_mul (hb₀ n hn).ne' (by simp [i])]
    simp [hb'' n hn, i, Nat.prime_two, add_comm]
  apply Set.infinite_of_injOn_mapsTo (f := fun n ↦ (x n, y n, z n)) _ _ (Set.Ici_infinite 2)
  · grind [Set.InjOn]
  · simp +contextual only [Set.MapsTo, Set.mem_Ici, solutionSet, Set.mem_setOf_eq, h, and_true]
    intro n hn
    exact ⟨by grind, by grind, by grind⟩

end Erdos674

#print axioms Erdos674.erdos_674_infinite
-- 'Erdos674.erdos_674_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
