/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.KeyUnion
import ErdosProblems.Erdos565.RandomGraph

/-!
# The dependent structural count in the ACDFM key lemma

The structural tuple used in the key lemma contains two subsets `S` and `U`,
an `R`-vector, and, for every color, a graph whose vertex type is the subtype
cut out by `U`.  Thus the type of the color data genuinely depends on `U`.
This file counts those tuples after restricting `U` by an arbitrary predicate.
-/

open scoped BigOperators SimpleGraph

namespace Erdos565
namespace KeyStructure

/-- A finite predicate-restricted family of subsets, without requiring the
predicate to carry computational decidability data. -/
noncomputable instance fintypeSmallSets
    (V : Type*) [Fintype V] [DecidableEq V] (Small : Finset V → Prop) :
    Fintype {U : Finset V // Small U} :=
  Fintype.ofFinite _

/-- The dependent structural tuples indexed by sets `U` satisfying `Small`.

The second component is a subtype only to record the restriction `Small U`;
its value is the vertex set on which every graph in `colors` lives. -/
abbrev RestrictedStructure (V : Type*) [Fintype V] [DecidableEq V]
    (r N : ℕ) (Small : Finset V → Prop) :=
  (S : Finset V) × (U : {U : Finset V // Small U}) ×
    (KeyUnion.RVector r N × ((i : Fin r) → SimpleGraph ↑(U : Finset V)))

/-- Exact cardinality of the restricted dependent structural-data type. -/
theorem card_restrictedStructure
    (V : Type*) [Fintype V] [DecidableEq V]
    (r N : ℕ) (Small : Finset V → Prop) :
    Fintype.card (RestrictedStructure V r N Small) =
      ∑ _S : Finset V, ∑ U : {U : Finset V // Small U},
        (N + 1) ^ r * 2 ^ (r * U.1.card.choose 2) := by
  classical
  simp [RestrictedStructure, KeyUnion.card_rVector,
    RandomGraph.card_simpleGraph, Fintype.card_pi, pow_mul]
  apply Finset.sum_congr rfl
  intro U hU
  congr 1
  rw [← pow_mul, ← pow_mul]
  congr 1
  exact Nat.mul_comm _ _

/-- The corrected `3 N + 4 r D` count for the dependent structural tuples.

The two arbitrary vertex sets account for two factors `2^N`, the exact
`R`-vector count is absorbed by `hR`, and `hSmall` bounds the full vector of
color graphs on every admissible `U`. -/
theorem card_restrictedStructure_le_two_pow
    (V : Type*) [Fintype V] [DecidableEq V]
    (r N D : ℕ) (Small : Finset V → Prop)
    (hV : Fintype.card V = N)
    (hR : (N + 1) ^ r ≤ 2 ^ N)
    (hSmall : ∀ U : Finset V, Small U →
      r * U.card.choose 2 ≤ 4 * r * D) :
    Fintype.card (RestrictedStructure V r N Small) ≤
      2 ^ (3 * N + 4 * r * D) := by
  classical
  rw [card_restrictedStructure]
  calc
    ∑ _S : Finset V, ∑ U : {U : Finset V // Small U},
          (N + 1) ^ r * 2 ^ (r * U.1.card.choose 2) ≤
        ∑ _S : Finset V, ∑ _U : {U : Finset V // Small U},
          2 ^ N * 2 ^ (4 * r * D) := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro U hU
      exact Nat.mul_le_mul hR
        (Nat.pow_le_pow_right (by decide : 0 < 2) (hSmall U.1 U.2))
    _ = Fintype.card (Finset V) *
          (Fintype.card {U : Finset V // Small U} *
            (2 ^ N * 2 ^ (4 * r * D))) := by
      simp
    _ ≤ 2 ^ N * (2 ^ N * (2 ^ N * 2 ^ (4 * r * D))) := by
      have hsets : Fintype.card (Finset V) = 2 ^ N := by
        simp [hV]
      rw [hsets]
      gcongr
      exact (Fintype.card_subtype_le Small).trans_eq hsets
    _ = 2 ^ (3 * N + 4 * r * D) := by
      simp only [← pow_add]
      congr 1
      ring

end KeyStructure
end Erdos565
