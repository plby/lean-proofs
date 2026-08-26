import ErdosProblems.Erdos1188.PrimeConstruction
import ErdosProblems.Erdos1188.BinomialBounds

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An explicit elementary double-exponential lower bound
-/

namespace Erdos1188

open scoped BigOperators

noncomputable section

/-- A coarse bound on the indexed primes, tailored to multiplying them. -/
theorem nthPrime_le_two_pow_succ (i : ℕ) : nthPrime i ≤ 2 ^ (i + 1) := by
  have hcap := nthPrime_sub_one_le_two_pow i
  have hp1 : 1 ≤ nthPrime i := (nthPrime_prime i).one_le
  calc
    nthPrime i = (nthPrime i - 1) + 1 := (Nat.sub_add_cancel hp1).symm
    _ ≤ 2 ^ i + 1 := Nat.add_le_add_right hcap 1
    _ ≤ 2 ^ i + 2 ^ i :=
      Nat.add_le_add_left (Nat.one_le_pow i 2 (by decide)) (2 ^ i)
    _ = 2 ^ (i + 1) := by rw [pow_succ]; omega

/-- The product of the first `m` primes is at most `2^(m^2)`. -/
theorem basePrimeProduct_le_two_pow_sq (m : ℕ) :
    (∏ i : Fin m, nthPrime i.val) ≤ 2 ^ (m * m) := by
  calc
    (∏ i : Fin m, nthPrime i.val) ≤ ∏ _i : Fin m, 2 ^ m := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      exact le_trans (nthPrime_le_two_pow_succ i.val)
        (Nat.pow_le_pow_right (by decide) (by omega))
    _ = (2 ^ m) ^ m := by simp
    _ = 2 ^ (m * m) := by rw [pow_mul]

/-- Adding a final prime no larger than `2^(m-1)` keeps the full period below
`2^(m(m+1))`. -/
theorem extendedPrimeProduct_le (m P : ℕ) (hP : P ≤ 2 ^ (m - 1)) :
    P * (∏ i : Fin m, nthPrime i.val) ≤ 2 ^ (m * (m + 1)) := by
  have hPm : P ≤ 2 ^ m := le_trans hP
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le m 1))
  calc
    P * (∏ i : Fin m, nthPrime i.val) ≤ 2 ^ m * 2 ^ (m * m) :=
      Nat.mul_le_mul hPm (basePrimeProduct_le_two_pow_sq m)
    _ = 2 ^ (m * (m + 1)) := by
      rw [← pow_add]
      congr 1
      ring

/-- Fully explicit lower bound: at cutoff `2^(m(m+1))`, there are at least
`2^(2^(m-2))` minimal distinct covering systems. -/
theorem explicit_double_exponential_lower (m : ℕ) (hm : 6 ≤ m) :
    2 ^ (2 ^ (m - 2)) ≤ coveringCount (2 ^ (m * (m + 1))) := by
  obtain ⟨P, hPprime, hPlo, hPhi, hcount⟩ := exists_large_prime_frame_count m hm
  let k := P - 1
  let t := 2 ^ (m - 2)
  have ht_le_k : t ≤ k := by simp only [t, k]; omega
  have ht4 : 4 ≤ t := by
    have hexp : 2 ≤ m - 2 := by omega
    simpa [t] using (Nat.pow_le_pow_right (n := 2) (by decide) hexp)
  have hk4 : 4 ≤ k := le_trans ht4 ht_le_k
  have hpowm : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (m - 1) := Nat.mul_comm _ _
  have h2k : 2 * k ≤ 2 ^ m - 1 := by
    simp only [k]
    rw [hpowm]
    omega
  have hbin : 2 ^ k ≤ (2 ^ m - 1).choose k :=
    two_pow_le_choose_of_two_mul_le (2 ^ m - 1) k hk4 h2k
  have htk : 2 ^ t ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) ht_le_k
  have hperiod := extendedPrimeProduct_le m P hPhi
  exact le_trans htk <| le_trans hbin <| le_trans hcount
    (coveringCount_mono hperiod)

end

end Erdos1188
