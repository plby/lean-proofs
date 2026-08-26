import ErdosProblems.Erdos593.TripleSystem.SequenceLiftTaggedBaseLetterEquiv

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tagged base-letter equivalence for embedded source edges

Under linearity of its selected image, an embedded source edge type is
canonically equivalent to the sigma of the separate local base-letter images.
The active base-node tag remains present, so no letters from distinct fibres
are identified and no untagged union or trace decomposition is asserted.
-/

namespace Erdos593

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Under a linear selected image, source-edge indices are equivalent to the
sigma of the separate local base-letter images of their canonical base fibres.
The sigma tag retains the originating base fibre. -/
noncomputable def edgeIndexEquiv_sigmaBaseLetterImage_of_linear
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G))
    (hlinear : ((system G).edgeRestriction f.edgeImage).Linear) :
    Equiv E (Sigma (fun q : activeBaseNodeIndex f.edgeImage =>
      baseLetter '' baseFiber f.edgeImage q.1)) :=
  (f.edgeImageEdgeEquiv).trans
    (selectedEdgeEquiv_sigmaBaseLetterImage_of_linear hlinear)

end SequenceLift

end Erdos593
