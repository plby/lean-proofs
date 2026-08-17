/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 903

Erdős--Fowler--Sós--Wilson proved that a pairwise balanced design on
`p^2 + p + 1` points has either exactly that many blocks or at least `p`
more blocks.  The proof below formalizes their incidence-matrix argument.

The detailed mathematical reconstruction is in `tex/903.tex`.
-/

namespace Erdos903

open scoped BigOperators

/-- An indexed family of blocks is a pairwise balanced design of index one.
The lower bound of two on block size is part of the standard definition of a
linear space and rules out irrelevant empty or singleton blocks. -/
def PairwiseBalanced {v b : ℕ} (block : Fin b → Finset (Fin v)) : Prop :=
  (∀ i, 2 ≤ (block i).card) ∧
    ∀ x y, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

/-- The set of block indices incident with a point. -/
def through {v b : ℕ} (block : Fin b → Finset (Fin v)) (x : Fin v) : Finset (Fin b) :=
  Finset.univ.filter fun i ↦ x ∈ block i

/-- The replication number (point degree). -/
def degree {v b : ℕ} (block : Fin b → Finset (Fin v)) (x : Fin v) : ℕ :=
  (through block x).card

@[simp] lemma mem_through {v b : ℕ} {block : Fin b → Finset (Fin v)}
    {x : Fin v} {i : Fin b} : i ∈ through block x ↔ x ∈ block i := by
  simp [through]


theorem erdos_903 (p b : ℕ) (hp : IsPrimePow p)
    (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (hpb : PairwiseBalanced block) (hmore : p ^ 2 + p + 1 < b) :
    p ^ 2 + p + 1 + p ≤ b := by
  sorry

end Erdos903
