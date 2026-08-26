import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberEquiv
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIndex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tagged base-letter equivalence for sequence lifts

A selected family of lift edges is canonically equivalent to the sigma type of
its base fibres.  Under linearity, this composes with the fibre-local
base-letter equivalences.  The base-node tag remains part of the codomain, so
equal base letters from different fibres are never identified here.  In
particular, this module does not construct an untagged global base-letter
union or a trace decomposition.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The selected edges are canonically equivalent to their base fibres, with
the active base node retained as a sigma tag. -/
noncomputable def sigmaBaseFiberEquivSelectedEdge
    (S : Set (Edge G)) :
    Equiv (Sigma (fun q : activeBaseNodeIndex S => baseFiber S q.1)) S :=
  (Equiv.sigmaCongrRight (fun (q : activeBaseNodeIndex S) =>
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun e : Edge G => e ∈ S)
      (fun e => baseNode e = q.1)).symm)).trans
    (Equiv.sigmaSubtypeFiberEquiv
      (fun e : S => baseNode e.1)
      (fun q : Node G => q ∈ activeBaseNodes S)
      (by
        intro e
        exact mem_activeBaseNodes.mpr ⟨e.1, e.2, rfl⟩))

/-- Under a linear restriction, selected edges are equivalent to the sigma of
the separate base-letter images of their canonical base fibres.  The sigma
tag retains the originating base fibre. -/
noncomputable def selectedEdgeEquiv_sigmaBaseLetterImage_of_linear
    {S : Set (Edge G)}
    (hlinear : ((system G).edgeRestriction S).Linear) :
    Equiv S (Sigma (fun q : activeBaseNodeIndex S =>
      baseLetter '' baseFiber S q.1)) :=
  (sigmaBaseFiberEquivSelectedEdge S).symm.trans
    (Equiv.sigmaCongrRight
      (fun q => baseFiberEquivBaseLetterImage_of_linear q.1 hlinear))

end SequenceLift

end Erdos593
