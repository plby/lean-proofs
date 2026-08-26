import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportTailDegree
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportRunningOrderEndpoints

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constructible and obligatory endpoints for tail-degree base-fibre orders

This module feeds the stronger tail-degree-one support order directly into the
existing coherent-order endpoints.  It makes no claim that the required order
is supplied by linearity or by the canonical active-base enumeration.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A noduplicated tail-degree-one base-fibre order gives a constructible
exact sequence-lift restriction once its fibres cover the selected edge set. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_tailDegreeBaseFiberAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) = S)
    (hnodup : nodes.Nodup)
    (hdegree : baseFiberSupportTailAtMostOneNeighbor S nodes) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_coherentBaseFiberAssembly
    hS hlinear hG nodes hcover hnodup
    (baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor hdegree)

/-- The base-node-cover form of the tail-degree-one constructibility
endpoint. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_tailDegreeBaseNodeCover
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes)
    (hnodup : nodes.Nodup)
    (hdegree : baseFiberSupportTailAtMostOneNeighbor S nodes) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_coherentBaseNodeCover
    hS hlinear hG nodes hcover hnodup
    (baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor hdegree)

/-- The canonical active-base enumeration gives a constructible exact
restriction when it satisfies the explicit tail-degree-one premise. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_activeBaseNodeSupportTailAtMostOneNeighbor
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hdegree :
      baseFiberSupportTailAtMostOneNeighbor S (activeBaseNodeList S hS)) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_activeBaseNodeSupportTailOverlapCoherent
    hS hlinear hG
    (baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor hdegree)

/-- The exact-cover tail-degree-one endpoint is obligatory by the completed
classical positive-atom closure theorem. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_tailDegreeBaseFiberAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) = S)
    (hnodup : nodes.Nodup)
    (hdegree : baseFiberSupportTailAtMostOneNeighbor S nodes) :
    ((system G).edgeRestriction S).IsObligatory :=
  edgeRestriction_isObligatory_of_linear_of_hostColorable_of_coherentBaseFiberAssembly
    hS hlinear hG nodes hcover hnodup
    (baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor hdegree)

/-- The base-node-cover tail-degree-one endpoint is obligatory. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_tailDegreeBaseNodeCover
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes)
    (hnodup : nodes.Nodup)
    (hdegree : baseFiberSupportTailAtMostOneNeighbor S nodes) :
    ((system G).edgeRestriction S).IsObligatory :=
  edgeRestriction_isObligatory_of_linear_of_hostColorable_of_coherentBaseNodeCover
    hS hlinear hG nodes hcover hnodup
    (baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor hdegree)

/-- The canonical active-base endpoint is obligatory when the explicit
tail-degree-one premise holds. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_activeBaseNodeSupportTailAtMostOneNeighbor
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hdegree :
      baseFiberSupportTailAtMostOneNeighbor S (activeBaseNodeList S hS)) :
    ((system G).edgeRestriction S).IsObligatory :=
  edgeRestriction_isObligatory_of_linear_of_hostColorable_of_activeBaseNodeSupportTailOverlapCoherent
    hS hlinear hG
    (baseFiberSupportTailOverlapCoherent_of_tailAtMostOneNeighbor hdegree)

end SequenceLift

end Erdos593
