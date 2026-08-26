import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportForestOrderBridge
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportTailDegree
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftFiniteLiftGenerated

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite-generation endpoint from acyclic base-fibre support overlap

An acyclic active base-fibre support-overlap graph has a leaf-elimination
order.  That order supplies the tail-degree-one compatibility required by the
generic host-relative finite-generation assembly theorem.

The acyclicity hypothesis remains explicit: it is not inferred from linearity
alone.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite linear sequence-lift restriction with acyclic active base-fibre
support overlap is host-relatively finitely generated. -/
theorem edgeRestriction_finiteLiftGenerated_of_linear_of_supportOverlapAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hacyclic : (baseFiberSupportOverlapGraph S).IsAcyclic) :
    TripleSystem.FiniteLiftGenerated G ((system G).edgeRestriction S) := by
  obtain ⟨nodes, hnodup, hcover, hdegree⟩ :=
    exists_baseFiberSupportTailAtMostOneNeighbor_order_of_supportOverlapAcyclic
      hS hacyclic
  exact
    edgeRestriction_finiteLiftGenerated_of_linear_of_baseFiberAssembly
      hS hlinear nodes
      (edgePieceUnion_baseFiber_eq_of_baseNode_mem nodes hcover)
      (baseFiberAssemblyCompatible_of_linear_of_nodup_of_tailAtMostOneNeighbor
        hlinear hnodup hdegree)

end SequenceLift

end Erdos593
