/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UndirectedComponentwise

/-!
# Source--target duality for the undirected Erdős--Menger conclusion

Reversing paths is not a source--target symmetry of an arbitrary directed
web: it replaces the digraph by its transpose.  The final Erdős 599 web is
special, because it is the bidirection of a simple graph.  At the public
undirected level, `UndirectedFiniteEndpoint.conclusion_symm` therefore lets
us choose either endpoint set as the source of a directed construction.

The reduction in this file combines that symmetry with connected-component
assembly.  Each component may choose its orientation independently.  Thus:

* without any uncountable-source theorem, it is enough to solve components
  in which both endpoint slices are uncountable;
* if the regular-source branch is available, it is enough to solve
  components in which both endpoint slices have singular cardinality.

In particular, reversal does **not** remove the singular case when a
connected component has singular endpoint slices on both sides.
-/

noncomputable section

namespace Erdos599
namespace SingularSourceTargetDuality

open Cardinal Set SimpleGraph

universe u

variable {V : Type u}

/-- The exact public undirected Erdős--Menger conclusion, given a short name
for the reduction statements below. -/
abbrev Conclusion (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∃ (P : Set (ABPath G A B)) (S : Set V),
    IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S

/-- A directed conclusion with the endpoint roles swapped is sufficient for
the public theorem when the directed graph is the bidirection of the given
simple graph.  We first forget directions and only then reverse undirected
paths; no invalid source--target symmetry of an arbitrary digraph is used. -/
theorem conclusion_of_reversed_bidirected
    (G : SimpleGraph V) (A B : Set V)
    (h : Bridge.DirectedMengerConclusion (DirectedPath.bidirect G) B A) :
    Conclusion G A B := by
  exact UndirectedFiniteEndpoint.conclusion_symm
    (Bridge.exists_orthogonal_pathPacking_of_directed h)

/-- For the actual bidirected web used by Erdős 599, a directed theorem in
either endpoint orientation proves the exact public conclusion. -/
theorem conclusion_of_bidirected_either_orientation
    (G : SimpleGraph V) (A B : Set V)
    (h : Bridge.DirectedMengerConclusion (DirectedPath.bidirect G) A B ∨
      Bridge.DirectedMengerConclusion (DirectedPath.bidirect G) B A) :
    Conclusion G A B := by
  rcases h with h | h
  · exact Bridge.exists_orthogonal_pathPacking_of_directed h
  · exact conclusion_of_reversed_bidirected G A B h

/-- If the only untreated connected components are those in which neither
endpoint slice is countable, local witnesses for those components suffice
for the exact global conclusion.

The two easy branches are genuinely undirected.  The right-countable branch
uses reversal inside `erdos_599_of_componentwise_right_countable`'s local
ingredient, rather than asserting a source--target symmetry for a fixed
arbitrary digraph. -/
theorem conclusion_of_componentwise_both_uncountable
    (G : SimpleGraph V) (A B : Set V)
    (hhard : ∀ c : G.ConnectedComponent,
      ¬ (A ∩ c.supp).Countable → ¬ (B ∩ c.supp).Countable →
        Conclusion G (A ∩ c.supp) (B ∩ c.supp)) :
    Conclusion G A B := by
  apply UndirectedComponentwise.assemble
  intro c
  by_cases hA : (A ∩ c.supp).Countable
  · exact UndirectedFiniteEndpoint.erdos_599_of_left_countable
      G (A ∩ c.supp) (B ∩ c.supp) hA
  by_cases hB : (B ∩ c.supp).Countable
  · exact UndirectedFiniteEndpoint.erdos_599_of_right_countable
      G (A ∩ c.supp) (B ∩ c.supp) hB
  exact hhard c hA hB

/-- Endpoint classification after the countable branches have been removed.
If neither set is countable, then each cardinal is regular or singular. -/
theorem regular_or_singular_endpoints_of_not_countable
    (X Y : Set V) (hX : ¬ X.Countable) (hY : ¬ Y.Countable) :
    ((#X).IsRegular ∨ (#X).IsSingular) ∧
      ((#Y).IsRegular ∨ (#Y).IsSingular) := by
  have hXuncountable : ℵ₀ < #X := by
    apply lt_of_not_ge
    intro hcard
    exact hX (Cardinal.le_aleph0_iff_set_countable.mp hcard)
  have hYuncountable : ℵ₀ < #Y := by
    apply lt_of_not_ge
    intro hcard
    exact hY (Cardinal.le_aleph0_iff_set_countable.mp hcard)
  exact ⟨Cardinal.isRegular_or_isSingular hXuncountable.le,
    Cardinal.isRegular_or_isSingular hYuncountable.le⟩

/-- Exact reduction to the both-singular residual.

`hregularSource` is a source-oriented theorem: it proves the conclusion when
the *left* endpoint has uncountable regular cardinality.  If instead the
right endpoint is regular, the proof applies `hregularSource` after swapping
the endpoint sets and then reverses the resulting undirected paths.

Consequently `hbothSingular` is required only on a connected component whose
two endpoint slices are both uncountable singular cardinals.  This is the
maximal reduction obtainable from endpoint reversal and componentwise
localization alone. -/
theorem conclusion_of_regular_source_and_componentwise_both_singular
    (G : SimpleGraph V) (A B : Set V)
    (hregularSource : ∀ (X Y : Set V), ℵ₀ < #X → (#X).IsRegular →
      Conclusion G X Y)
    (hbothSingular : ∀ c : G.ConnectedComponent,
      ¬ (A ∩ c.supp).Countable → ¬ (B ∩ c.supp).Countable →
      (#(A ∩ c.supp : Set V)).IsSingular →
      (#(B ∩ c.supp : Set V)).IsSingular →
        Conclusion G (A ∩ c.supp) (B ∩ c.supp)) :
    Conclusion G A B := by
  apply conclusion_of_componentwise_both_uncountable G A B
  intro c hA hB
  have hAuncountable : ℵ₀ < #(A ∩ c.supp : Set V) := by
    apply lt_of_not_ge
    intro hcard
    exact hA (Cardinal.le_aleph0_iff_set_countable.mp hcard)
  have hBuncountable : ℵ₀ < #(B ∩ c.supp : Set V) := by
    apply lt_of_not_ge
    intro hcard
    exact hB (Cardinal.le_aleph0_iff_set_countable.mp hcard)
  rcases Cardinal.isRegular_or_isSingular hAuncountable.le with
      hAregular | hAsingular
  · exact hregularSource (A ∩ c.supp) (B ∩ c.supp)
      hAuncountable hAregular
  rcases Cardinal.isRegular_or_isSingular hBuncountable.le with
      hBregular | hBsingular
  · exact UndirectedFiniteEndpoint.conclusion_symm
      (hregularSource (B ∩ c.supp) (A ∩ c.supp)
        hBuncountable hBregular)
  · exact hbothSingular c hA hB hAsingular hBsingular

#print axioms conclusion_of_componentwise_both_uncountable
#print axioms conclusion_of_reversed_bidirected
#print axioms conclusion_of_bidirected_either_orientation
#print axioms regular_or_singular_endpoints_of_not_countable
#print axioms conclusion_of_regular_source_and_componentwise_both_singular

end SingularSourceTargetDuality
end Erdos599
