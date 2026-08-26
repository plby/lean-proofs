import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberExpansion
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIndex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite fibre-local expansion spine for sequence lifts

This module packages the canonical finite partition of a selected edge family
into active base fibres together with the already-established factor and
private-vertex-expansion data for each individual fibre.

It deliberately does not glue the fibre factors, identify the selected system
with a disjoint union of the fibre restrictions, or make any global atom or
constructibility assertion: distinct base fibres need not have disjoint vertex
supports or disjoint base-letter images.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite linear selected family has a canonical finite family of nonempty,
pairwise edge-disjoint base fibres whose union is the selected family.  Each
fibre carries its own finite base-letter-subgraph factor into the host graph
and is isomorphic to that factor's private-vertex expansion.

The conclusion is intentionally fibre-indexed.  It supplies no global gluing
of the local graph factors or triple-system isomorphisms. -/
theorem finite_baseFiberExpansionFactorSpine_of_linear
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    Finite (activeBaseNodeIndex S) ∧
      (⋃ q : activeBaseNodeIndex S, baseFiber S q.1) = S ∧
      Set.PairwiseDisjoint Set.univ
        (fun q : activeBaseNodeIndex S => baseFiber S q.1) ∧
      (∀ q : activeBaseNodeIndex S, (baseFiber S q.1).Nonempty) ∧
      ∀ q : activeBaseNodeIndex S,
        Exists (fun _ : Fintype
          (baseLetterSubgraph G (baseLetter '' baseFiber S q.1)).verts =>
          And
            (Nonempty (Erdos593.SimpleGraph.NonInducedFactor
              (baseLetterSubgraph G (baseLetter '' baseFiber S q.1)).coe G))
            (Nonempty (TripleSystem.Iso
              (TripleSystem.privateVertexExpansion
                (baseLetterSubgraph G (baseLetter '' baseFiber S q.1)).coe)
              ((system G).edgeRestriction (baseFiber S q.1))))) := by
  refine ⟨finite_activeBaseNodeIndex hS,
    iUnion_baseFiber_activeBaseNodeIndex S,
    pairwiseDisjoint_baseFiber_activeBaseNodeIndex S, ?_, ?_⟩
  · intro q
    exact baseFiber_nonempty_activeBaseNodeIndex S q
  · intro q
    exact exists_fintype_baseFiberLetterSubgraphFactorExpansionIso_of_linear
      hS q.1 hlinear

end SequenceLift

end Erdos593
