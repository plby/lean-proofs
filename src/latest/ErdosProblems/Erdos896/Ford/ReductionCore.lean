/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Defs

/-!
# Shared arithmetic definitions for Ford's reduction

This small module contains the squarefull definitions used by both the
arithmetic reduction and the analytic sieve estimates.  Keeping them here
prevents an import cycle between `Reduction` and `Sieve`.
-/

namespace Erdos896.Ford

/-- A positive natural number is squarefull when every prime occurring in
its factorization occurs to exponent at least two. -/
def Squarefull (n : ℕ) : Prop :=
  0 < n ∧ ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

instance : DecidablePred Squarefull := by
  intro n
  unfold Squarefull
  infer_instance

/-- The squarefull integers in `[1,x]`. -/
def squarefullSet (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter Squarefull

@[simp]
theorem mem_squarefullSet {q x : ℕ} :
    q ∈ squarefullSet x ↔ 1 ≤ q ∧ q ≤ x ∧ Squarefull q := by
  simp [squarefullSet, and_assoc]

/-- Squarefull integers in `(K,x]`. -/
def squarefullTailSet (x K : ℕ) : Finset ℕ :=
  (squarefullSet x).filter fun q ↦ K < q

@[simp]
theorem mem_squarefullTailSet {q x K : ℕ} :
    q ∈ squarefullTailSet x K ↔
      1 ≤ q ∧ q ≤ x ∧ Squarefull q ∧ K < q := by
  simp [squarefullTailSet, and_assoc]

end Erdos896.Ford
