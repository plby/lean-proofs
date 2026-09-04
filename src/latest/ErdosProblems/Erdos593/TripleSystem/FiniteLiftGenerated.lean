import ErdosProblems.Erdos593.Graph.NonInducedFactor
import ErdosProblems.Erdos593.TripleSystem.BridgeBlockRunningIntersection
import ErdosProblems.Erdos593.TripleSystem.Constructive
import ErdosProblems.Erdos593.TripleSystem.DisjointUnion
import ErdosProblems.Erdos593.TripleSystem.EdgeRestrictionReconstruction
import ErdosProblems.Erdos593.TripleSystem.Expansion
import ErdosProblems.Erdos593.TripleSystem.Isomorph
import ErdosProblems.Erdos593.TripleSystem.OnePointAmalgamation

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite generation relative to a host graph

`FiniteLiftGenerated G` is a deliberately local, host-relative construction
class.  Its graph atoms are private-vertex expansions of finite graphs that
carry a non-induced factor map into `G`; no colourability condition is built
into the definition.  It is closed under the two exact gluing operations used
by `RunningEdgeAssemblyGeometry` and under relabelling by triple-system
isomorphism.

This module only records finite generation data.  In particular, it makes no
claim that a generated system is `Constructible`, intrinsic, or colourable.
-/

namespace Erdos593

universe u w

namespace TripleSystem

variable {V : Type u} (G : _root_.SimpleGraph V)

/-- Finite triple systems generated relative to a host graph `G`.

The graph-atom constructor remembers an explicit non-induced factor into the
host.  Thus the predicate is intentionally stronger than merely being a
private-vertex expansion of some finite graph, while deliberately avoiding any
host-colourability hypothesis. -/
inductive FiniteLiftGenerated : {X I : Type w} → TripleSystem X I → Prop
  | ofEdgeless (X : Type w) [Fintype X] :
      FiniteLiftGenerated (edgeless X)
  | ofFactorExpansion {X : Type w} [Fintype X]
      {J : _root_.SimpleGraph X}
      (f : Erdos593.SimpleGraph.NonInducedFactor J G) :
      FiniteLiftGenerated (privateVertexExpansion J)
  | disjointUnion {X I Y J : Type w}
      {F : TripleSystem X I} {H : TripleSystem Y J}
      (hF : FiniteLiftGenerated F) (hH : FiniteLiftGenerated H) :
      FiniteLiftGenerated (F.disjointUnion H)
  | amalgam {X I Y J : Type w}
      {F : TripleSystem X I} {H : TripleSystem Y J}
      (hF : FiniteLiftGenerated F) (hH : FiniteLiftGenerated H)
      (x : X) (y : Y) :
      FiniteLiftGenerated (OnePointAmalgamation.amalgam F H x y)
  | ofIso {X I Y J : Type w}
      {F : TripleSystem X I} {H : TripleSystem Y J}
      (hF : FiniteLiftGenerated F) (f : Iso F H) :
      FiniteLiftGenerated H

namespace FiniteLiftGenerated

/-- Ergonomic name for the host-factor expansion atom. -/
theorem ofExpansion {X : Type w} [Fintype X]
    {J : _root_.SimpleGraph X}
    (f : Erdos593.SimpleGraph.NonInducedFactor J G) :
    FiniteLiftGenerated G (privateVertexExpansion J) :=
  ofFactorExpansion f

/-- Running-intersection geometry assembles locally host-generated exact
pieces into a host-generated exact restriction of their total edge union.

The geometry supplies only the two permitted gluing cases; the hypothesis on
the listed pieces supplies their local generation witnesses. -/
theorem ofRunningEdgeAssemblyGeometry
    {X I : Type w} (K : TripleSystem X I)
    (pieces : List (Set I))
    (hgeometry : BridgeBlock.RunningEdgeAssemblyGeometry K pieces)
    (hpieces : ∀ S ∈ pieces,
      FiniteLiftGenerated G (K.edgeRestriction S)) :
    FiniteLiftGenerated G (K.edgeRestriction (edgePieceUnion pieces)) := by
  induction pieces with
  | nil =>
      let : IsEmpty (K.EdgeSupport ∅) := ⟨by
        intro x
        rcases x.2 with ⟨e, he, _⟩
        exact he⟩
      let : Fintype (K.EdgeSupport ∅) := Fintype.ofFinite _
      exact FiniteLiftGenerated.ofIso
        (FiniteLiftGenerated.ofEdgeless (K.EdgeSupport ∅))
        (edgelessIsoEdgeRestrictionEmpty K)
  | cons S pieces ih =>
      rcases hgeometry with ⟨hprevious, hEdges, hSupports⟩
      have hPrev :
          FiniteLiftGenerated G
            (K.edgeRestriction (edgePieceUnion pieces)) :=
        ih hprevious (fun T hT => hpieces T (by simp [hT]))
      have hS : FiniteLiftGenerated G (K.edgeRestriction S) :=
        hpieces S (by simp)
      rcases hSupports with hDisjoint | ⟨r, hRoot⟩
      · exact FiniteLiftGenerated.ofIso
          (FiniteLiftGenerated.disjointUnion hPrev hS)
          (K.edgeRestrictionUnionIsoDisjointUnion hEdges hDisjoint)
      · exact FiniteLiftGenerated.ofIso
          (FiniteLiftGenerated.amalgam hPrev hS
            (K.edgeSupportLeftRoot hRoot)
            (K.edgeSupportRightRoot hRoot))
          (K.edgeRestrictionUnionIsoOnePointAmalgamation hEdges hRoot)

end FiniteLiftGenerated

end TripleSystem

end Erdos593
