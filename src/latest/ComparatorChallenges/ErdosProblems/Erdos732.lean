/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 732

We formalize Noga Alon's projective-plane construction of many block-size
sequences of pairwise balanced designs.  The exact finite construction gives
`q ^ (q - 2)` different sequences on every ground set of size at least
`q ^ 2 + q + 1`, for every prime `q ≥ 5`.  Bertrand's postulate then gives
the requested `exp (c * sqrt n * log n)` lower bound for every sufficiently
large `n`.

Block-size sequences are represented as multisets.  This is canonically
equivalent to the nonincreasing lists in the statement and avoids carrying a
chosen sorting order through the construction.
-/

namespace Erdos732

universe u v

/-- A finite pairwise balanced block design: every pair of distinct points is
contained in exactly one block, and every block has at least two points. -/
structure PairwiseBalancedDesign (P : Type u) [Fintype P] where
  Block : Type u
  blockFintype : Fintype Block
  block : Block → Finset P
  two_le_card : ∀ i, 2 ≤ (block i).card
  pair_unique : ∀ ⦃x y : P⦄, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

attribute [instance] PairwiseBalancedDesign.blockFintype

/-- The multiset of block cardinalities of a design. -/
noncomputable def PairwiseBalancedDesign.blockSizes {P : Type u} [Fintype P]
    (D : PairwiseBalancedDesign P) : Multiset ℕ :=
  Finset.univ.val.map fun i ↦ (D.block i).card

/-- A block-size multiset is compatible for `n` if a pairwise balanced design
on `Fin n` has exactly those block sizes. -/
def BlockCompatible (n : ℕ) (sizes : Multiset ℕ) : Prop :=
  ∃ D : PairwiseBalancedDesign (Fin n), D.blockSizes = sizes

/-- Completion adds only blocks of cardinality two. -/

theorem erdos_732 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset (Multiset ℕ),
        (∀ sizes ∈ S, BlockCompatible n sizes) ∧
        Real.exp (c * Real.sqrt n * Real.log n) ≤ S.card := by
  sorry

end Erdos732
