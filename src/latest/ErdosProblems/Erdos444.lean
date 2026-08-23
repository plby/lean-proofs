/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 444.
https://www.erdosproblems.com/forum/thread/444

Informal authors:
- Paul Erdős
- András Sárközy

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos444.md
-/
import ErdosProblems.Erdos444.Divergent

/-!
# Erdős Problem 444

For an infinite set `A ⊆ ℕ`, let `d_A(n)` count the positive elements of
`A` dividing `n`.  This file proves that for every natural exponent `k`,

`limsup (max_{1 ≤ n < x} d_A(n)) / (∑_{a ∈ A, 1 ≤ a < x} 1/a)^k = ∞`.

The half-open real cutoff is represented literally by `positiveBelow`; the
limsup takes values in `EReal`, so equality to `⊤` is the exact formal
meaning of infinity.  A detailed mathematical proof and Leanization guide are
in `tex/444.tex`.
-/

open Filter Set

namespace Erdos444

/-- The answer to Erdős Problem 444 is yes. -/
theorem erdos_444 :
    ∀ (A : Set ℕ), A.Infinite → ∀ k : ℕ,
      atTop.limsup (fun x : ℝ ↦ (ratio A k x : EReal)) = ⊤ := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ A hA k
    exact limsup_coe_eq_top_of_tailUnbounded (ratio A k)
      (tailUnbounded_ratio_of_infinite A hA k)
  · intro _
    trivial

#print axioms Erdos444.erdos_444

end Erdos444
