import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIncidenceForestOrderBridge
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportRunningOrderEndpoints
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftFiniteLiftGenerated

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Endpoints from acyclic base-fibre support incidence graphs

The incidence-forest order bridge supplies both the compatible base-fibre
assembly needed for finite generation and the coherent running order needed by
the existing constructibility and obligatoriness endpoints.  The incidence
acyclicity hypothesis is deliberately explicit here.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite linear selected family whose base-fibre support incidence graph is
acyclic is host-relatively finitely generated. -/
theorem edgeRestriction_finiteLiftGenerated_of_linear_of_incidenceAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hacyclic : (baseFiberSupportIncidenceGraph S).IsAcyclic) :
    TripleSystem.FiniteLiftGenerated G ((system G).edgeRestriction S) := by
  obtain ⟨nodes, _, hcover, hcompatible⟩ :=
    exists_baseFiberAssemblyCompatible_order_of_linear_of_incidenceAcyclic
      hS hlinear hacyclic
  exact edgeRestriction_finiteLiftGenerated_of_linear_of_baseFiberAssembly
    hS hlinear nodes
    (edgePieceUnion_baseFiber_eq_of_baseNode_mem nodes hcover)
    hcompatible

/-- Under the same explicit incidence-acyclicity premise, a two-colourable
host gives a constructible selected restriction. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_incidenceAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hacyclic : (baseFiberSupportIncidenceGraph S).IsAcyclic) :
    TripleSystem.Constructible ((system G).edgeRestriction S) := by
  obtain ⟨nodes, hnodup, hcover, hcoherent⟩ :=
    exists_baseFiberSupportTailOverlapCoherent_order_of_incidenceAcyclic
      hS hlinear hacyclic
  exact edgeRestriction_constructible_of_linear_of_hostColorable_of_coherentBaseNodeCover
    hS hlinear hG nodes hcover hnodup hcoherent

/-- Under the same explicit incidence-acyclicity premise, the selected
restriction is obligatory by the completed classical positive-atom closure. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_incidenceAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hacyclic : (baseFiberSupportIncidenceGraph S).IsAcyclic) :
    ((system G).edgeRestriction S).IsObligatory := by
  obtain ⟨nodes, hnodup, hcover, hcoherent⟩ :=
    exists_baseFiberSupportTailOverlapCoherent_order_of_incidenceAcyclic
      hS hlinear hacyclic
  exact edgeRestriction_isObligatory_of_linear_of_hostColorable_of_coherentBaseNodeCover
    hS hlinear hG nodes hcover hnodup hcoherent

end SequenceLift

end Erdos593
