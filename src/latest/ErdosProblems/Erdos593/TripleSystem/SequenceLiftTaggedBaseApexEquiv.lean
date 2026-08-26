import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseApexEquiv
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftTaggedBaseLetterEquiv

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tagged apex-image equivalence for sequence lifts

Under a linear restriction, selected lifted edges are explicitly equivalent
to the sigma type of the canonical-apex images of their separate canonical
base fibres. The active base-node tag is retained, so this creates neither an
untagged union nor a cross-fibre identification.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Under a linear restriction, the selected edge family is equivalent to
the sigma of its individual canonical-apex images, retaining the active
base-node tag. -/
noncomputable def selectedEdgeEquiv_sigmaBaseApexImage_of_linear
    {S : Set (Edge G)}
    (hlinear : ((system G).edgeRestriction S).Linear) :
    Equiv S (Sigma (fun q : activeBaseNodeIndex S =>
      baseApex '' baseFiber S q.1)) :=
  (sigmaBaseFiberEquivSelectedEdge S).symm.trans
    (Equiv.sigmaCongrRight
      (fun q => baseFiberEquivBaseApexImage_of_linear q.1 hlinear))

end SequenceLift

end Erdos593
