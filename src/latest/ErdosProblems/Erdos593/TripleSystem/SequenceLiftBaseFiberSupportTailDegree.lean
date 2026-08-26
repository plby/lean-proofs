import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportRunningOrder

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tail-degree support orders for sequence-lift base fibres

This module records a simple, stronger sufficient condition for a coherent
support running order: each newly attached base fibre has at most one
support-overlap neighbour in the already assembled tail.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A base-fibre running order has tail support degree at most one when, at
every head `q`, any two tail fibres which both have nonempty support overlap
with `baseFiber S q` are the same base node. -/
def baseFiberSupportTailAtMostOneNeighbor
    (S : Set (Edge G)) : List (Node G) → Prop
  | [] => True
  | q :: nodes =>
      baseFiberSupportTailAtMostOneNeighbor S nodes ∧
      ∀ u ∈ nodes, ∀ v ∈ nodes,
        (((system G).edgeSupportSet (baseFiber S q) ∩
          (system G).edgeSupportSet (baseFiber S u)).Nonempty) →
        (((system G).edgeSupportSet (baseFiber S q) ∩
          (system G).edgeSupportSet (baseFiber S v)).Nonempty) →
        u = v

/-- Tail support degree at most one is sufficient for the weaker condition
that all nonempty head-to-tail support intersections are equal. -/
theorem baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor
    {S : Set (Edge G)} {nodes : List (Node G)}
    (hdegree : baseFiberSupportTailAtMostOneNeighbor S nodes) :
    baseFiberSupportTailOverlapCoherent S nodes := by
  induction nodes with
  | nil =>
      trivial
  | cons q nodes ih =>
      change baseFiberSupportTailAtMostOneNeighbor S nodes ∧ _ at hdegree
      rcases hdegree with ⟨hdegreeTail, hdegreeHead⟩
      refine ⟨ih hdegreeTail, ?_⟩
      intro u hu v hv hqu hqv
      obtain rfl := hdegreeHead u hu v hv hqu hqv
      rfl

/-- Pairwise support linearity and a noduplicated tail-degree-one support
order give the exact recursive geometry required by
`baseFiberAssemblyCompatible`.  This packages the stronger local degree
condition through the coherent-running-order bridge. -/
theorem baseFiberAssemblyCompatible_of_linear_of_nodup_of_tailAtMostOneNeighbor
    {S : Set (Edge G)} {nodes : List (Node G)}
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hnodup : nodes.Nodup)
    (hdegree : baseFiberSupportTailAtMostOneNeighbor S nodes) :
    baseFiberAssemblyCompatible S nodes :=
  baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
    hlinear hnodup
    (baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor hdegree)

end SequenceLift

end Erdos593
