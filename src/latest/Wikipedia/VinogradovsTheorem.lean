/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Wikipedia.VinogradovsTheorem.Arithmetic

/-!
# Vinogradov's three-primes theorem

Every sufficiently large odd natural number is the sum of three pairwise
distinct primes.
-/

namespace VinogradovsTheorem

/-- Every sufficiently large odd natural number is the sum of three pairwise
 distinct primes. -/
theorem vinogradovs_theorem :
    ∃ N : ℕ, ∀ n : ℕ, N < n → Odd n →
      ∃ p q r : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
          p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p + q + r := by
  obtain ⟨N, hN⟩ :=
    distinctTernaryGoldbachEventually_of_count_large
      (ternaryPrimeCountEventuallyLarge_of_weightedLowerBound
        (weightedTernaryPrimeLowerBound_of_vonMangoldt
          vonMangoldtTernaryLowerBound))
  refine ⟨N, ?_⟩
  intro n hn hodd
  obtain ⟨p, q, r, hp, hq, hr, ⟨hpq, hpr, hqr⟩, hsum⟩ :=
    hN n hn hodd
  exact ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, hsum⟩

end VinogradovsTheorem
