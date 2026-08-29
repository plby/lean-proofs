/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UndirectedComponentwise

/-!
# Componentwise endpoint reversal for Erdős--Menger

The countable-endpoint theorem may be oriented independently in each
connected component.  Thus neither endpoint set needs to be globally
countable: it is enough that every connected component contain only
countably many vertices from at least one of the two endpoint sets.

This is the strongest direct connected-component reduction.  Its precise
residual case is a connected component in which both endpoint slices are
uncountable.
-/

noncomputable section

namespace Erdos599
namespace UndirectedComponentwiseEndpoint

open Set SimpleGraph

universe u

variable {V : Type u}

/-- Exact Erdős--Menger under a component-by-component choice of a
countable endpoint side.  Different components may choose different sides. -/
theorem erdos_599_of_componentwise_endpoint_countable
    (G : SimpleGraph V) (A B : Set V)
    (hcount : ∀ c : G.ConnectedComponent,
      (A ∩ c.supp).Countable ∨ (B ∩ c.supp).Countable) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  apply UndirectedComponentwise.assemble
  intro c
  rcases hcount c with hA | hB
  · exact UndirectedFiniteEndpoint.erdos_599_of_left_countable
      G (A ∩ c.supp) (B ∩ c.supp) hA
  · exact UndirectedFiniteEndpoint.erdos_599_of_right_countable
      G (A ∩ c.supp) (B ∩ c.supp) hB

/-- A convenient logically equivalent hypothesis: there is no connected
component in which both endpoint slices are uncountable. -/
theorem erdos_599_of_no_component_both_endpoint_uncountable
    (G : SimpleGraph V) (A B : Set V)
    (hcount : ∀ c : G.ConnectedComponent,
      ¬ ((¬ (A ∩ c.supp).Countable) ∧
        (¬ (B ∩ c.supp).Countable))) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  apply erdos_599_of_componentwise_endpoint_countable G A B
  intro c
  by_cases hA : (A ∩ c.supp).Countable
  · exact Or.inl hA
  · rcases not_and_or.mp (hcount c) with hAA | hBB
    · exact False.elim (hAA hA)
    · exact Or.inr (not_not.mp hBB)

/-- Assumption-free localization of the uncountable obstruction.  Either
the exact Erdős--Menger conclusion already follows by componentwise
countable-endpoint assembly, or one connected component contains
uncountably many endpoints on both sides. -/
theorem erdos_599_or_exists_component_both_endpoint_uncountable
    (G : SimpleGraph V) (A B : Set V) :
    (∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S) ∨
      ∃ c : G.ConnectedComponent,
        (¬ (A ∩ c.supp).Countable) ∧
          (¬ (B ∩ c.supp).Countable) := by
  classical
  by_cases hhard : ∃ c : G.ConnectedComponent,
      (¬ (A ∩ c.supp).Countable) ∧
        (¬ (B ∩ c.supp).Countable)
  · exact Or.inr hhard
  · apply Or.inl
    apply erdos_599_of_componentwise_endpoint_countable G A B
    intro c
    by_cases hA : (A ∩ c.supp).Countable
    · exact Or.inl hA
    · apply Or.inr
      by_contra hB
      exact hhard ⟨c, hA, hB⟩

#print axioms erdos_599_of_componentwise_endpoint_countable
#print axioms erdos_599_of_no_component_both_endpoint_uncountable
#print axioms erdos_599_or_exists_component_both_endpoint_uncountable

end UndirectedComponentwiseEndpoint
end Erdos599
