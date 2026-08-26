import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberExpansion
import ErdosProblems.Erdos593.TripleSystem.Constructive

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constructible linear sequence-lift base fibres

This module records the exact conditional bridge from the local graph-side
description of a linear sequence-lift base fibre to constructibility.  The
extra two-colourability hypothesis is explicit: linearity alone does not make
the canonical base-letter subgraph bipartite.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite linear base fibre is constructible when the graph selected by its
canonical base letters is two-colourable. -/
theorem baseFiber_constructible_of_linear_of_colorable
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hcolor : (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe.Colorable 2) :
    TripleSystem.Constructible ((system G).edgeRestriction (baseFiber S q)) := by
  classical
  letI : Finite (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts :=
    Set.finite_coe_iff.mpr <|
      baseLetterSubgraph_finite_verts G <|
        (hS.subset (baseFiber_subset S q)).image baseLetter
  letI : Fintype (baseLetterSubgraph G (baseLetter '' baseFiber S q)).verts :=
    Fintype.ofFinite _
  exact TripleSystem.Constructible.ofIso
    (TripleSystem.Constructible.ofExpansion
      (baseLetterSubgraph G (baseLetter '' baseFiber S q)).coe hcolor)
    (baseFiber_privateVertexExpansionIso_of_linear q hlinear)

/-- A finite linear base fibre is constructible whenever its ambient host
graph is two-colourable.  The required local colouring is pulled back through
the canonical non-induced factor of the selected base-letter subgraph. -/
theorem baseFiber_constructible_of_linear_of_hostColorable
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) :
    TripleSystem.Constructible ((system G).edgeRestriction (baseFiber S q)) :=
  baseFiber_constructible_of_linear_of_colorable hS q hlinear
    (_root_.SimpleGraph.Colorable.of_hom
      (baseFiberLetterSubgraphFactor S q).toHom hG)

end SequenceLift

end Erdos593
