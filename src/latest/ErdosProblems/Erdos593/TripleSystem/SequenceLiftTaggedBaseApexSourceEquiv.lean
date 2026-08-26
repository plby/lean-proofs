import ErdosProblems.Erdos593.TripleSystem.SequenceLiftTaggedBaseApexEquiv

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tagged apex-image equivalence for embedded sequence lifts

For an embedding into a sequence lift, linearity of the embedded edge image
identifies the source edge type with the sigma of the canonical-apex images
of its separate canonical base fibres. The active base-node tag is retained.
-/

namespace Erdos593

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Under linearity of an embedded edge image, the source edge type is
equivalent to the sigma of the canonical-apex images of its separate
canonical base fibres, retaining the active base-node tag. -/
noncomputable def edgeIndexEquiv_sigmaBaseApexImage_of_linear
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G))
    (hlinear : ((system G).edgeRestriction f.edgeImage).Linear) :
    Equiv E (Sigma (fun q : activeBaseNodeIndex f.edgeImage =>
      baseApex '' baseFiber f.edgeImage q.1)) :=
  (f.edgeImageEdgeEquiv).trans
    (selectedEdgeEquiv_sigmaBaseApexImage_of_linear hlinear)

end SequenceLift

end Erdos593
