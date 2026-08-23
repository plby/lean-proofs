/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 526.
https://www.erdosproblems.com/forum/thread/526

Informal authors:
- L. A. Shepp

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos526.md
-/
import ErdosProblems.Erdos526.Shepp

/-!
# Erdős Problem 526 (Dvoretzky--Shepp random covering)

The supporting modules formalize the circle model, the finite weighted
covering lemma, the kernel estimates, and Shepp's leftmost-gap argument.  This
file states the public order-invariant resolution.
-/

namespace Erdos526

open Filter MeasureTheory

/-- **Erdős Problem 526 (Shepp's theorem).**  Let `a` be nonnegative, tend to
zero, and have divergent sum.  There is a nonincreasing rearrangement `b` of
the positive terms of `a`, and independently centered arcs cover every point
of the unit circle infinitely often almost surely if and only if

`∑ n, exp (b 0 + ⋯ + b n) / (n + 1)² = ∞`.

The infinite-coverage formulation is the standard Dvoretzky--Shepp event.  It
also makes explicit why the series must be evaluated after rearrangement:
coverage is invariant under permutations, while prefix sums are not. -/
theorem erdos_526_resolution
    {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n)
    (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a) :
    ∃ b : ℕ → ℝ, IsDecreasingRearrangement a b ∧
      (sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition b) :=
  erdos_526_exists_rearrangement ha₀ halim hdiv

/-- The same criterion for any supplied decreasing rearrangement. -/
theorem erdos_526_resolution_for_rearrangement
    {a b : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n)
    (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a)
    (hrearr : IsDecreasingRearrangement a b) :
    sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition b :=
  erdos_526 ha₀ halim hdiv hrearr

#print axioms erdos_526_resolution

end Erdos526
