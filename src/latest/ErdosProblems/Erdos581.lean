/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 581.
https://www.erdosproblems.com/forum/thread/581

Informal authors:
- Noga Alon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos581.md
-/
import ErdosProblems.Erdos581.LowerBound
import ErdosProblems.Erdos581.UpperBound

/-!
# Erdős Problem 581

For `m` edges, `f m` is the largest integer forced as the number of edges in
a bipartite subgraph of every finite triangle-free graph.  Alon's resolution
is `f(m) = m/2 + Θ(m^(4/5))`.  The theorem below gives explicit absolute
constants.
-/

namespace Erdos581

/-- Complete resolution of Erdős Problem 581, with explicit constants. -/
theorem erdos_581 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ m : ℕ,
        (m : ℝ) / 2 + c₁ * (m : ℝ) ^ ((4 : ℝ) / 5) ≤ (f m : ℝ) ∧
        (f m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ ((4 : ℝ) / 5) := by
  refine ⟨1 / 1024, 1024, by norm_num, by norm_num, ?_⟩
  intro m
  constructor
  · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using lower_bound m
  · exact upper_bound m

end Erdos581

alias _root_.Erdos581.erdos581 := _root_.Erdos581.erdos_581
