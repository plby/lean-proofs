import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberConstructible
import ErdosProblems.Erdos593.TripleSystem.ConstructiblePositiveObligatory

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Obligatory linear sequence-lift base fibres

This is the fibre-local use of the established classical positive-atom theorem:
once a finite linear base fibre has a two-colourable canonical base-letter
subgraph, its private-vertex-expansion description makes it constructible and
hence obligatory.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite linear base fibre is obligatory when the graph selected by its
canonical base letters is two-colourable. -/
theorem baseFiber_isObligatory_of_linear_of_colorable
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hcolor : (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe.Colorable 2) :
    ((system G).edgeRestriction (baseFiber S q)).IsObligatory :=
  TripleSystem.Constructible.isObligatory
    (baseFiber_constructible_of_linear_of_colorable hS q hlinear hcolor)

/-- A finite linear base fibre is obligatory whenever its ambient host graph
is two-colourable. -/
theorem baseFiber_isObligatory_of_linear_of_hostColorable
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) :
    ((system G).edgeRestriction (baseFiber S q)).IsObligatory :=
  TripleSystem.Constructible.isObligatory
    (baseFiber_constructible_of_linear_of_hostColorable hS q hlinear hG)

end SequenceLift

end Erdos593
