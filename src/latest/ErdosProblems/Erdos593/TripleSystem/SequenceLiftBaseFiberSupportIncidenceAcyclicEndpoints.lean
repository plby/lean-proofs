import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIncidenceAcyclic
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIncidenceForestOrderEndpoints
import ErdosProblems.Erdos593.TripleSystem.FiniteLiftGeneratedConstructible

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional endpoints for finite linear sequence-lift restrictions

The incidence-acyclicity theorem turns the verified conditional incidence
endpoints into unconditional finite-linear endpoints.  The structural
finite-generation result has no host-colourability premise; the constructible
and obligatory consequences retain the explicit two-colourability condition.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Every finite linear selected restriction is host-relatively finitely
generated. -/
theorem edgeRestriction_finiteLiftGenerated_of_linear
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    TripleSystem.FiniteLiftGenerated G ((system G).edgeRestriction S) := by
  exact edgeRestriction_finiteLiftGenerated_of_linear_of_incidenceAcyclic
    hS hlinear
    (baseFiberSupportIncidenceGraph_isAcyclic_of_finite_linear hS hlinear)

/-- A finite linear selected restriction in a two-colourable host is
constructible. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) :
    TripleSystem.Constructible ((system G).edgeRestriction S) := by
  exact TripleSystem.FiniteLiftGenerated.constructible_of_hostColorable hG
    (edgeRestriction_finiteLiftGenerated_of_linear hS hlinear)

/-- A finite linear selected restriction in a two-colourable host is
obligatory by the completed classical positive-atom closure theorem. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) :
    ((system G).edgeRestriction S).IsObligatory := by
  exact TripleSystem.FiniteLiftGenerated.isObligatory_of_hostColorable hG
    (edgeRestriction_finiteLiftGenerated_of_linear hS hlinear)

end SequenceLift

end Erdos593
