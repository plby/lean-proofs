/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exact targets from Theorem 1.1 of the attached July 22, 2026 writeup by
Omniscience Research Agent and Jeff Pickhardt.
Formal author: OpenAI Codex.

These are definitions of the requested statements, not hypotheses assumed by
the proof files and not assertions that the full theorem has been proved.
-/

import ErdosProblems.Erdos1189.Density
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Erdos1189

open Filter

def irreducibleSetsOfSize (k : ℕ) : Set (Finset ℕ) :=
  {D | IsIrreducibleCoveringSet D ∧ D.card = k}

noncomputable def irreducibleCount (k : ℕ) : ℕ := (irreducibleSetsOfSize k).ncard

/-- The series starts at `t = 1`; the natural index here is `t - 1`. -/
noncomputable def tau : ℝ :=
  ∑' t : ℕ, (Real.log (1 + 1 / ((t : ℝ) + 1))) ^ 2

def CountingAsymptotic : Prop :=
  (∀ k : ℕ, (irreducibleSetsOfSize k).Finite) ∧
    Tendsto (fun k : ℕ =>
      Real.log (irreducibleCount k) * Real.sqrt (Real.log k) /
        ((k : ℝ) * Real.sqrt k)) atTop (nhds (4 * Real.sqrt tau / 3))

def MaximumLargestModulusClaim : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    (∀ D ∈ irreducibleSetsOfSize k, D.sup id ≤ 3 * 2 ^ (k - 3)) ∧
    ∃ D ∈ irreducibleSetsOfSize k, D.sup id = 3 * 2 ^ (k - 3)

def MinimumLargestModulusClaim : Prop :=
  (∀ D : Finset ℕ, IsCoveringSet D → D.card + 1 ≤ D.sup id) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 5 ≤ k →
      ∃ D ∈ irreducibleSetsOfSize k, ∀ d ∈ D,
        (d : ℝ) ≤ C * k * (Real.log k) ^ 2

/-- Both constants are independent of `k`; both bounds hold for all sufficiently
large cardinalities, not just along a subsequence. -/
def MaximumReciprocalSumClaim : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
    (∀ D ∈ irreducibleSetsOfSize k, (reciprocalSum D : ℝ) ≤ C * Real.log k) ∧
    ∃ D ∈ irreducibleSetsOfSize k, c * Real.log k ≤ (reciprocalSum D : ℝ)

def DivisorFamilyClaim : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsIrreducibleCoveringSet (nontrivialDivisors (2 ^ (p - 1) * p))

/-- The full result requested by the user, with the paper's edge cases. -/
def Erdos1189Statement : Prop :=
  (∀ D : Finset ℕ, IsCoveringSet D → 5 ≤ D.card) ∧
    CountingAsymptotic ∧ MaximumLargestModulusClaim ∧ MinimumLargestModulusClaim ∧
    MaximumReciprocalSumClaim ∧ DivisorFamilyClaim ∧
    {n : ℕ | IsIrreducibleCoveringSet (nontrivialDivisors n)}.Infinite

end Erdos1189
