/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 493.
https://www.erdosproblems.com/forum/thread/493

Formal authors:
- Seed-Prover 1.5
- Aristotle
- ChatGPT
- Zheng Yuan

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos493.md
-/
import Mathlib

namespace Erdos493

/--
There exists a `k` such that every sufficiently large integer `n`
can be written as `∏ aᵢ - ∑ aᵢ` with all `aᵢ ≥ 2`.
-/
theorem erdos_493_aristotle :
  ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∃ a : Fin k → ℤ,
      (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
      (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  use 2;
  use 0;
  -- For any non-negative integer $n$, we can choose $a_0 = n + 2$ and $a_1 = 2$.
  intro n hn
  use ![n + 2, 2];
  norm_num [ Fin.forall_fin_two ];
  exact ⟨ hn, by ring ⟩

theorem erdos_493_chatgpt :
  ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∃ a : Fin k → ℤ,
      (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
      (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  -- Take `k = 2` and `N = 0`.
  refine ⟨2, 0, ?_⟩
  intro n hn
  -- Choose a₀ = 2 and a₁ = n + 2.
  let a : Fin 2 → ℤ := fun i => if (i : ℕ) = 0 then 2 else n + 2
  refine ⟨a, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [a]
    linarith [hn]
  · -- Compute `∏ aᵢ - ∑ aᵢ` on `Fin 2`.
    simp [a, Fin.prod_univ_two, Fin.sum_univ_two]
    ring

#print axioms erdos_493_aristotle
-- 'Erdos493.erdos_493_aristotle' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos493
