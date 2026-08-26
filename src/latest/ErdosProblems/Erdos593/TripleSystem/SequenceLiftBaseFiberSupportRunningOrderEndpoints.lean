import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportRunningOrder

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constructible and obligatory endpoints for coherent base-fibre orders

The support-tail-overlap coherence condition is a genuinely additional global
ordering premise.  This module merely feeds its verified geometric consequence
into the existing N5 assembly endpoints; it does not claim that linearity or
the canonical active-base enumeration supplies that premise.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The canonical active-base enumeration has no repeated base node. -/
theorem activeBaseNodeList_nodup
    {S : Set (Edge G)} (hS : S.Finite) :
    (activeBaseNodeList S hS).Nodup := by
  change
    ((@Finset.univ (activeBaseNodeIndex S)
      (activeBaseNodeIndexFintype hS)).toList.map Subtype.val).Nodup
  exact (Finset.nodup_toList _).map Subtype.val_injective

/-- A noduplicated coherent support running order gives a constructible exact
sequence-lift restriction once its base fibres cover the selected edge set. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_coherentBaseFiberAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) = S)
    (hnodup : nodes.Nodup)
    (hcoherent : baseFiberSupportTailOverlapCoherent S nodes) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_baseFiberAssembly
    hS hlinear hG nodes hcover
    (baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
      hlinear hnodup hcoherent)

/-- The canonical-base-node cover form of the coherent-running-order
constructibility theorem. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_coherentBaseNodeCover
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes)
    (hnodup : nodes.Nodup)
    (hcoherent : baseFiberSupportTailOverlapCoherent S nodes) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_baseNodeCover
    hS hlinear hG nodes hcover
    (baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
      hlinear hnodup hcoherent)

/-- The canonical active-base enumeration yields a constructible exact
restriction when its explicit support-tail-overlap coherence premise holds. -/
theorem edgeRestriction_constructible_of_linear_of_hostColorable_of_activeBaseNodeSupportTailOverlapCoherent
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hcoherent :
      baseFiberSupportTailOverlapCoherent S (activeBaseNodeList S hS)) :
    TripleSystem.Constructible ((system G).edgeRestriction S) :=
  edgeRestriction_constructible_of_linear_of_hostColorable_of_activeBaseNodeAssembly
    hS hlinear hG
    (baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
      hlinear (activeBaseNodeList_nodup hS) hcoherent)

/-- The exact-cover coherent-running-order endpoint is obligatory by the
completed classical positive-atom closure theorem. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_coherentBaseFiberAssembly
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : TripleSystem.edgePieceUnion (nodes.map (baseFiber S)) = S)
    (hnodup : nodes.Nodup)
    (hcoherent : baseFiberSupportTailOverlapCoherent S nodes) :
    ((system G).edgeRestriction S).IsObligatory :=
  edgeRestriction_isObligatory_of_linear_of_hostColorable_of_baseFiberAssembly
    hS hlinear hG nodes hcover
    (baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
      hlinear hnodup hcoherent)

/-- The canonical-base-node-cover coherent-running-order endpoint is
obligatory. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_coherentBaseNodeCover
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2) (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes)
    (hnodup : nodes.Nodup)
    (hcoherent : baseFiberSupportTailOverlapCoherent S nodes) :
    ((system G).edgeRestriction S).IsObligatory :=
  edgeRestriction_isObligatory_of_linear_of_hostColorable_of_baseNodeCover
    hS hlinear hG nodes hcover
    (baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
      hlinear hnodup hcoherent)

/-- The canonical active-base endpoint is obligatory when the explicit
support-tail-overlap coherence premise holds. -/
theorem edgeRestriction_isObligatory_of_linear_of_hostColorable_of_activeBaseNodeSupportTailOverlapCoherent
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hG : G.Colorable 2)
    (hcoherent :
      baseFiberSupportTailOverlapCoherent S (activeBaseNodeList S hS)) :
    ((system G).edgeRestriction S).IsObligatory :=
  edgeRestriction_isObligatory_of_linear_of_hostColorable_of_activeBaseNodeAssembly
    hS hlinear hG
    (baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
      hlinear (activeBaseNodeList_nodup hS) hcoherent)

end SequenceLift

end Erdos593
