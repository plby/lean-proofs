/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The largest reciprocal sum is of logarithmic order at every large cardinality.
Informal source: Section 7 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.QuantitativeConstruction
import ErdosProblems.Erdos1189.PrimeSeedSum
import ErdosProblems.Erdos1189.PrimeReciprocals
import ErdosProblems.Erdos1189.ReciprocalUpper
import ErdosProblems.Erdos1189.Statements

namespace Erdos1189

open Filter

lemma log_card_le_three_log_prime {P k : ℕ} (hP : P.Prime) (hPk : P ≤ k)
    (hkP : k ≤ P ^ 2 + 2 * P) : Real.log k ≤ 3 * Real.log P := by
  have hP2 : 2 * P ≤ P ^ 2 := by nlinarith [hP.two_le]
  have hP3 : 2 * P ^ 2 ≤ P ^ 3 := by
    nlinarith [Nat.mul_le_mul_right (P ^ 2) hP.two_le]
  have hcube : k ≤ P ^ 3 := by omega
  have hlog := Real.log_le_log
    (show (0 : ℝ) < k by exact_mod_cast hP.pos.trans_le hPk)
    (show (k : ℝ) ≤ (P : ℝ) ^ 3 by exact_mod_cast hcube)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

theorem eventually_large_reciprocalSum :
    ∀ᶠ k : ℕ in atTop,
      ∃ S ∈ irreducibleSetsOfSize k,
        (1 / 48 : ℝ) * Real.log k ≤ (reciprocalSum S : ℝ) := by
  obtain ⟨_, _, hconstruction⟩ := eventually_bounded_construction
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp eventually_primeLog_reciprocal_lower
  filter_upwards [hconstruction, eventually_ge_atTop (P₀ ^ 2 + 2 * P₀ + 1)]
    with k hk hlarge
  obtain ⟨P, S, hP, hPk, hkP, hS, hcard, _, hproducts⟩ := hk
  have hPlarge : P₀ ≤ P := by
    by_contra h
    have hPP₀ : P ≤ P₀ := by omega
    have hsq := Nat.pow_le_pow_left hPP₀ 2
    omega
  have hprime := hP₀ P hPlarge
  have hseed := reciprocalSum_lower_of_squarefree_products hproducts
  have hlog := log_card_le_three_log_prime hP hPk hkP
  refine ⟨S, ⟨hS, hcard⟩, ?_⟩
  linarith

/-- Part (iv), with bounds at all sufficiently large cardinalities. -/
theorem maximumReciprocalSum : MaximumReciprocalSumClaim := by
  refine ⟨1 / 48, 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [eventually_reciprocalSum_le_two_log, eventually_large_reciprocalSum]
    with k hupper hlower
  refine ⟨?_, hlower⟩
  intro D hD
  exact hupper D hD.1.1.1 hD.2

end Erdos1189
