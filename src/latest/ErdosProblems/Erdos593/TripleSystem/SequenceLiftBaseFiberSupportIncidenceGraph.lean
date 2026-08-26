import ErdosProblems.Erdos593.TripleSystem.EdgeRestriction
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIndex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite support-incidence graphs for sequence-lift base fibres

This module records the bipartite incidence graph between the active canonical
base fibres of a finite selected family and the points in its total support.
Unlike the projected support-overlap graph, a point shared by several fibres is
represented by one point-side vertex rather than a clique.  The module only
provides finite carriers and adjacency vocabulary; it does not assert an
acyclicity or ordering theorem.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The subtype of points in the total support of a selected edge family. -/
abbrev activeBaseFiberSupportPointIndex (S : Set (Edge G)) : Type u :=
  {p : Point G // p ∈ (system G).edgeSupportSet S}

/-- A finite selected family has a finite point-side support index subtype. -/
theorem finite_activeBaseFiberSupportPointIndex {S : Set (Edge G)}
    (hS : S.Finite) :
    Finite (activeBaseFiberSupportPointIndex S) :=
  ((system G).edgeSupportSet_finite hS).to_subtype

/-- A chosen finite enumeration of the point-side support index of a finite
selected family. This is supplied explicitly rather than as a global instance. -/
@[reducible]
noncomputable def activeBaseFiberSupportPointIndexFintype {S : Set (Edge G)}
    (hS : S.Finite) : Fintype (activeBaseFiberSupportPointIndex S) := by
  letI : Finite (activeBaseFiberSupportPointIndex S) :=
    finite_activeBaseFiberSupportPointIndex hS
  exact Fintype.ofFinite _

/-- The bipartite graph joining an active base-fibre index to each point in
that fibre's support.  The point-side carrier is the total support of `S`, so
it is finite whenever `S` is finite. -/
def baseFiberSupportIncidenceGraph (S : Set (Edge G)) :
    SimpleGraph
      (activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl q, .inr p =>
        p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1)
    | _, _ => False

/-- A fibre-side vertex is adjacent to a point-side vertex exactly when that
point belongs to the fibre support. -/
@[simp]
theorem baseFiberSupportIncidenceGraph_adj_inl_inr_iff
    {S : Set (Edge G)}
    {q : activeBaseNodeIndex S}
    {p : activeBaseFiberSupportPointIndex S} :
    (baseFiberSupportIncidenceGraph S).Adj (.inl q) (.inr p) ↔
      p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1) := by
  simp [baseFiberSupportIncidenceGraph, SimpleGraph.fromRel_adj]

/-- The incidence relation is symmetric when read from point-side to
fibre-side vertices. -/
@[simp]
theorem baseFiberSupportIncidenceGraph_adj_inr_inl_iff
    {S : Set (Edge G)}
    {q : activeBaseNodeIndex S}
    {p : activeBaseFiberSupportPointIndex S} :
    (baseFiberSupportIncidenceGraph S).Adj (.inr p) (.inl q) ↔
      p.1 ∈ (system G).edgeSupportSet (baseFiber S q.1) := by
  simp [baseFiberSupportIncidenceGraph, SimpleGraph.fromRel_adj]

/-- There are no fibre-side to fibre-side incidence edges. -/
@[simp]
theorem not_baseFiberSupportIncidenceGraph_adj_inl_inl
    {S : Set (Edge G)}
    {q r : activeBaseNodeIndex S} :
    ¬ (baseFiberSupportIncidenceGraph S).Adj (.inl q) (.inl r) := by
  simp [baseFiberSupportIncidenceGraph, SimpleGraph.fromRel_adj]

/-- There are no point-side to point-side incidence edges. -/
@[simp]
theorem not_baseFiberSupportIncidenceGraph_adj_inr_inr
    {S : Set (Edge G)}
    {p r : activeBaseFiberSupportPointIndex S} :
    ¬ (baseFiberSupportIncidenceGraph S).Adj (.inr p) (.inr r) := by
  simp [baseFiberSupportIncidenceGraph, SimpleGraph.fromRel_adj]

end SequenceLift

end Erdos593
