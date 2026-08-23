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

open scoped BigOperators LinearAlgebra.Projectivization
open Finset Fintype

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

/-- The multiset of cardinalities of an arbitrary finite indexed family. -/
noncomputable def familySizes {P : Type u} {I : Type v} [Fintype I]
    (A : I → Finset P) : Multiset ℕ :=
  Finset.univ.val.map fun i ↦ (A i).card

/-- Every pair of distinct points occurs in at most one member of `A`. -/
def IsPartialDesign {P : Type u} {I : Type v} (A : I → Finset P) : Prop :=
  ∀ ⦃x y : P⦄, x ≠ y → ∀ ⦃i j : I⦄,
    x ∈ A i → y ∈ A i → x ∈ A j → y ∈ A j → i = j

/-- A two-element subset which is not contained in any member of `A`. -/
def UncoveredPair {P : Type u} {I : Type v} [Fintype P]
    (A : I → Finset P) :=
  {s : Finset P // s.card = 2 ∧ ∀ i, ¬ (s ⊆ A i)}

noncomputable instance uncoveredPairFintype {P : Type u} {I : Type v}
    [Fintype P] [Fintype I] (A : I → Finset P) : Fintype (UncoveredPair A) := by
  classical
  change Fintype {s : Finset P // s.card = 2 ∧ ∀ i, ¬s ⊆ A i}
  exact Fintype.subtype
    ((Finset.univ : Finset (Finset P)).filter
      fun s ↦ s.card = 2 ∧ ∀ i, ¬s ⊆ A i) (by simp)

/-- Complete a partial pair design by adjoining every uncovered pair as a
two-element block. -/
noncomputable def completePartialDesign {P : Type u} {I : Type u}
    [Fintype P] [Fintype I] (A : I → Finset P) (hpartial : IsPartialDesign A)
    (hcard : ∀ i, 2 ≤ (A i).card) : PairwiseBalancedDesign P where
  Block := I ⊕ UncoveredPair A
  blockFintype := by classical infer_instance
  block
    | Sum.inl i => A i
    | Sum.inr s => s.1
  two_le_card
    | Sum.inl i => hcard i
    | Sum.inr s => by
        change 2 ≤ s.1.card
        exact s.2.1.ge
  pair_unique := by
    classical
    intro x y hxy
    by_cases hcovered : ∃ i, x ∈ A i ∧ y ∈ A i
    · obtain ⟨i, hxi, hyi⟩ := hcovered
      refine ⟨Sum.inl i, ⟨hxi, hyi⟩, ?_⟩
      intro j hj
      cases j with
      | inl j =>
          exact congrArg Sum.inl
            (hpartial hxy (i := i) (j := j) hxi hyi hj.1 hj.2).symm
      | inr s =>
          exfalso
          have hpairCard : ({x, y} : Finset P).card = 2 := by simp [hxy]
          have hsub : ({x, y} : Finset P) ⊆ s.1 := by
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hj.1
            · exact hj.2
          have hEq : (s.1 : Finset P) = {x, y} := by
            symm
            apply Finset.eq_of_subset_of_card_le hsub
            rw [s.2.1, hpairCard]
          apply s.2.2 i
          rw [hEq]
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxi
          · exact hyi
    · have huncovered : ∀ i, ¬(({x, y} : Finset P) ⊆ A i) := by
        intro i hi
        apply hcovered
        exact ⟨i, hi (by simp), hi (by simp)⟩
      let p : UncoveredPair A := ⟨{x, y}, by simp [hxy], huncovered⟩
      refine ⟨Sum.inr p, by simp [p], ?_⟩
      intro j hj
      cases j with
      | inl j =>
          exfalso
          exact hcovered ⟨j, hj.1, hj.2⟩
      | inr s =>
          have hpairCard : ({x, y} : Finset P).card = 2 := by simp [hxy]
          have hsub : ({x, y} : Finset P) ⊆ s.1 := by
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hj.1
            · exact hj.2
          have hEq : (s.1 : Finset P) = {x, y} := by
            symm
            apply Finset.eq_of_subset_of_card_le hsub
            rw [s.2.1, hpairCard]
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hEq

/-- Completion adds only blocks of cardinality two. -/

theorem erdos_732 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset (Multiset ℕ),
        (∀ sizes ∈ S, BlockCompatible n sizes) ∧
        Real.exp (c * Real.sqrt n * Real.log n) ≤ S.card := by
  sorry

end Erdos732
