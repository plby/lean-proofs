import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportForestOrderBridge
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportTailDegreeEndpoints

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constructibility endpoints from acyclic support-overlap graphs

An acyclic active support-overlap graph has a leaf-elimination order, which
supplies the tail-degree-one hypothesis required by the existing sequence-lift
assembly endpoints.  The acyclicity premise is explicit: it is not inferred
from linearity alone.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite selected family with an acyclic active base-fibre support-overlap
graph has a constructible restriction, provided the restriction is linear and
the host graph is two-colourable. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_supportOverlapAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hacyclic : (baseFiberSupportOverlapGraph S).IsAcyclic) :
    TripleSystem.Constructible ((system G).edgeRestriction S) := by
  obtain ⟨nodes, hnodup, hcover, hdegree⟩ :=
    exists_baseFiberSupportTailAtMostOneNeighbor_order_of_supportOverlapAcyclic
      hS hacyclic
  exact
    edgeRestriction_constructible_of_linear_of_hostColorable_of_tailDegreeBaseNodeCover
      hS hlinear hG nodes hcover hnodup hdegree

/-- Under the same explicit acyclicity premise, the finite restriction is
obligatory by the completed classical positive-atom closure theorem. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_supportOverlapAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hacyclic : (baseFiberSupportOverlapGraph S).IsAcyclic) :
    ((system G).edgeRestriction S).IsObligatory := by
  obtain ⟨nodes, hnodup, hcover, hdegree⟩ :=
    exists_baseFiberSupportTailAtMostOneNeighbor_order_of_supportOverlapAcyclic
      hS hacyclic
  exact
    edgeRestriction_isObligatory_of_linear_of_hostColorable_of_tailDegreeBaseNodeCover
      hS hlinear hG nodes hcover hnodup hdegree

end SequenceLift

end Erdos593
