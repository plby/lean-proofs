import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportTailDegree

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite support-overlap graph of sequence-lift base fibres

For a selected edge family, the active canonical base fibres form the vertices
of a finite graph.  Two distinct vertices are adjacent exactly when their
vertex-supports overlap.  This is only vocabulary for the ordering bridge:
it does not assert acyclicity.  In particular, linearity supplies pairwise
singleton-or-empty overlaps, but does not itself rule out cycles in this graph.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The support-overlap relation between two canonical base fibres. -/
def baseFiberSupportOverlap
    (S : Set (Edge G)) (q u : Node G) : Prop :=
  (((system G).edgeSupportSet (baseFiber S q) ∩
    (system G).edgeSupportSet (baseFiber S u)).Nonempty)

/-- Support overlap is symmetric. -/
theorem baseFiberSupportOverlap_comm
    (S : Set (Edge G)) (q u : Node G) :
    baseFiberSupportOverlap S q u ↔ baseFiberSupportOverlap S u q := by
  constructor
  · rintro ⟨p, hpq, hpu⟩
    exact ⟨p, hpu, hpq⟩
  · rintro ⟨p, hpu, hpq⟩
    exact ⟨p, hpq, hpu⟩

/-- The simple graph on active base nodes whose edges record nonempty
support-overlap of distinct canonical base fibres. -/
def baseFiberSupportOverlapGraph
    (S : Set (Edge G)) : SimpleGraph (activeBaseNodeIndex S) :=
  SimpleGraph.fromRel fun q u => baseFiberSupportOverlap S q.1 u.1

/-- Adjacency in the active base-fibre support-overlap graph is precisely a
distinct pair of base nodes with nonempty support overlap. -/
theorem baseFiberSupportOverlapGraph_adj_iff
    {S : Set (Edge G)} {q u : activeBaseNodeIndex S} :
    (baseFiberSupportOverlapGraph S).Adj q u ↔
      q ≠ u ∧ baseFiberSupportOverlap S q.1 u.1 := by
  change q ≠ u ∧
      (baseFiberSupportOverlap S q.1 u.1 ∨
        baseFiberSupportOverlap S u.1 q.1) ↔ _
  constructor
  · rintro ⟨hqu, hforward | hbackward⟩
    · exact ⟨hqu, hforward⟩
    · exact ⟨hqu, (baseFiberSupportOverlap_comm S _ _).mpr hbackward⟩
  · rintro ⟨hqu, hoverlap⟩
    exact ⟨hqu, Or.inl hoverlap⟩

end SequenceLift

end Erdos593
