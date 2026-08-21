/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos88.QuadraticCancellation

/-!
# Erdős Problem 88: rich tuple families for quadratic cancellation

This file connects KSSS Lemma 4.4 to the exact finite greedy packing engine
for the diverse-neighborhood tuples in Lemma 8.2.
-/

namespace Erdos88
namespace QuadraticCancellation

open Classical

/-- The source-shaped rich-core/greedy-packing interface behind KSSS
Lemma 8.2. The remaining side conditions are exactly the two numerical
inequalities checked by the logarithmic parameter choice in the paper. -/
def KSSSLemma82RichCore : Prop :=
  ∀ (C α : ℝ), 0 < C → 0 < α →
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℝ,
        Real.sqrt n ≤ m → m ≤ ρ * n →
          ∀ G : SimpleGraph (Fin n), RamseyFree C G →
            ∃ U : Finset (Fin n),
              m ≤ U.card ∧
              Rich (G.induce (U : Set (Fin n))) ((m / n) ^ ρ) ρ α ∧
              ∀ (q ℓ : ℕ),
                (∀ k ≤ q,
                  (m / n) ^ ρ * U.card ≤ ρ ^ k * U.card) →
                ((U.card : ℝ) ^ α + ℓ * q < U.card) →
                ∃ allUsed, Nonempty
                  (DiverseNeighborhoodFamily
                    (G.induce (U : Set (Fin n))) ρ Finset.univ
                    q ℓ allUsed)

theorem ksssLemma82RichCore : KSSSLemma82RichCore := by
  intro C α hC hα
  obtain ⟨ρ, hρ, hρone, N, hcore⟩ := ksssLemma44 C α hC hα
  refine ⟨ρ, hρ, hρone, N, ?_⟩
  intro n hn m hsqrt hm G hG
  obtain ⟨U, hmU, hrich⟩ := hcore n hn m hsqrt hm G hG
  refine ⟨U, hmU, hrich, ?_⟩
  intro q ℓ hresidual hsupply
  apply exists_diverseNeighborhoodFamily hrich Finset.univ q ℓ hρ.le
  · intro k hk
    simpa using hresidual k hk
  · simpa using hsupply

end QuadraticCancellation
end Erdos88
