import ErdosProblems.Erdos593.TripleSystem.ConstructiblePositiveObligatory
import ErdosProblems.Erdos593.TripleSystem.FiniteLiftGenerated

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Positive consequences of host-relative finite generation

This module turns host-relative finite generation into the existing positive
consequences when the ambient host graph is two-colourable.  The only local
input at a graph-factor atom is its explicit adjacency-preserving factor map
into the host; colourability pulls back along that map.
-/

namespace Erdos593

universe u w

namespace TripleSystem

variable {V : Type u} {G : _root_.SimpleGraph V}

namespace FiniteLiftGenerated

/-- A finite system generated relative to a two-colourable host is
constructible. -/
theorem constructible_of_hostColorable
    {X I : Type w} {K : TripleSystem X I}
    (hG : G.Colorable 2) (hK : FiniteLiftGenerated G K) :
    Constructible K := by
  induction hK with
  | ofEdgeless X =>
      exact Constructible.ofEdgeless X
  | ofFactorExpansion f =>
      exact Constructible.ofExpansion _
        (_root_.SimpleGraph.Colorable.of_hom f.toHom hG)
  | disjointUnion hF hH ihF ihH =>
      exact Constructible.disjointUnion ihF ihH
  | amalgam hF hH x y ihF ihH =>
      exact Constructible.amalgam ihF ihH x y
  | ofIso hF f ihF =>
      exact Constructible.ofIso ihF f

/-- A finite system generated relative to a two-colourable host is obligatory,
by the completed constructive positive theorem. -/
theorem isObligatory_of_hostColorable
    {X I : Type w} {K : TripleSystem X I}
    (hG : G.Colorable 2) (hK : FiniteLiftGenerated G K) :
    K.IsObligatory :=
  Constructible.isObligatory (constructible_of_hostColorable hG hK)

end FiniteLiftGenerated

end TripleSystem

end Erdos593
