/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the positive resolution of Erdős Problem 546.
https://www.erdosproblems.com/forum/thread/546

Informal authors:
- Benny Sudakov

Formal authors:
- OpenAI Codex
-/

import ErdosProblems.Erdos546.Amplification
import ErdosProblems.Erdos546.CliqueBound
import ErdosProblems.Erdos546.Iteration

/-!
# Erdős Problem 546

If a finite graph `G` has no isolated vertices and has `m` edges, then its
diagonal two-colour Ramsey number is at most `2^(O(√m))`.

We first prove the fully discrete bound

`graphRamseyNumber G ≤ 2 ^ (32768 * (Nat.sqrt m + 1))`.

For positive `m`, `Nat.sqrt m + 1 ≤ 2√m`; hence the universal real-exponent
form follows with the explicit constant `65536`.  Containment throughout is
ordinary, not necessarily induced, graph containment.

Reference: B. Sudakov, *A conjecture of Erdős on graph Ramsey numbers*,
Advances in Mathematics 227 (2011), 601–609.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open SimpleGraph

/-- The exact natural-number bound underlying the asymptotic statement of
Erdős Problem 546. -/
theorem erdos_546_discrete {v : ℕ} (G : SimpleGraph (Fin v))
    [DecidableRel G.Adj] (hG : ∀ x, ¬ G.IsIsolated x) :
    graphRamseyNumber G ≤
      2 ^ (32768 * sqrtScale G.edgeFinset.card) := by
  let m := G.edgeFinset.card
  change graphRamseyNumber G ≤ 2 ^ (32768 * sqrtScale m)
  by_cases hmzero : m = 0
  · calc
      graphRamseyNumber G = 0 :=
        graphRamseyNumber_eq_zero_of_noIsolated_of_edgeFinset_card_eq_zero
          G hG (by simpa [m] using hmzero)
      _ ≤ 2 ^ (32768 * sqrtScale m) := Nat.zero_le _
  · apply graphRamseyNumber_le_of_property
    by_cases hsmall : sqrtScale m < 32
    · exact smallScale_graphRamseyProperty G hG (by simp [m]) hsmall
    · have hs : 32 ≤ sqrtScale m := by omega
      have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
      intro R
      obtain ⟨X, Y, hpair, hX, hY⟩ :=
        exists_initial_iteration_pair R rfl hs
      have hvertex : v ≤ 2 * sqrtScale m ^ 2 := by
        calc
          v ≤ 2 * G.edgeFinset.card := noIsolated_card_le_twice_edges G hG
          _ = 2 * m := by simp [m]
          _ ≤ 2 * sqrtScale m ^ 2 :=
            Nat.mul_le_mul_left 2 (le_sqrtScale_sq m)
      apply iterate_amplification G R hvertex
        (fun q X Y hq hlegal hpair hX hY ↦
          amplification_step G R (by simp [m]) hmpos hG
            hq hlegal hpair hX hY)
        (q := 5) (X := X) (Y := Y)
      · norm_num
      · simpa using hs
      · exact hpair
      · exact hX
      · exact hY

/-- Uniform real-exponent form of Erdős Problem 546.  The absolute constant
is quantified before the graph, so this is a genuinely uniform assertion. -/
theorem erdos_546 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : ℕ) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj],
        (∀ x, ¬ G.IsIsolated x) →
          (graphRamseyNumber G : ℝ) ≤
            Real.rpow 2 (C * Real.sqrt (G.edgeFinset.card : ℝ)) := by
  refine ⟨65536, by norm_num, ?_⟩
  intro v G _ hG
  by_cases hmzero : G.edgeFinset.card = 0
  · rw [graphRamseyNumber_eq_zero_of_noIsolated_of_edgeFinset_card_eq_zero
      G hG hmzero]
    simp [hmzero]
  · have hmpos : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero hmzero
    have hdiscrete := erdos_546_discrete G hG
    have hexponent :
        ((32768 * sqrtScale G.edgeFinset.card : ℕ) : ℝ) ≤
          65536 * Real.sqrt (G.edgeFinset.card : ℝ) := by
      calc
        ((32768 * sqrtScale G.edgeFinset.card : ℕ) : ℝ) =
            32768 * (sqrtScale G.edgeFinset.card : ℝ) := by norm_num
        _ ≤ 32768 * (2 * Real.sqrt (G.edgeFinset.card : ℝ)) :=
          mul_le_mul_of_nonneg_left (sqrtScale_cast_le_two_sqrt hmpos) (by norm_num)
        _ = 65536 * Real.sqrt (G.edgeFinset.card : ℝ) := by ring
    calc
      (graphRamseyNumber G : ℝ) ≤
          ((2 ^ (32768 * sqrtScale G.edgeFinset.card) : ℕ) : ℝ) := by
        exact_mod_cast hdiscrete
      _ = Real.rpow 2
          ((32768 * sqrtScale G.edgeFinset.card : ℕ) : ℝ) := by
        change
          (((2 : ℕ) ^ (32768 * sqrtScale G.edgeFinset.card) : ℕ) : ℝ) =
            (2 : ℝ) ^
              ((32768 * sqrtScale G.edgeFinset.card : ℕ) : ℝ)
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact (Real.rpow_natCast 2
          (32768 * sqrtScale G.edgeFinset.card)).symm
      _ ≤ Real.rpow 2
          (65536 * Real.sqrt (G.edgeFinset.card : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

#print axioms Erdos546.erdos_546

end Erdos546
