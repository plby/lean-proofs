import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberIndex
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseApexEquiv

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Source-indexed apex equivalence for sequence lifts

For an embedded sequence lift with linear edge image, the source-edge
indices in one canonical base fibre are equivalent to the canonical-apex
image of that fibre.
-/

namespace Erdos593

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The exact source-edge index subtype at a chosen base node is equivalent
to the corresponding canonical base fibre of the embedded edge image. -/
noncomputable def baseFiberIndexEquivBaseFiber
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) (q : Node G) :
    Equiv (baseFiberIndex f q) (baseFiber f.edgeImage q) :=
  (Equiv.ofInjective (fun i : baseFiberIndex f q => f.edge i.1) (by
    intro i j hij
    apply Subtype.ext
    exact f.edge_injective hij)).trans
    (Equiv.setCongr (baseFiber_edgeImage_eq_range f q).symm)

/-- Under linearity of the embedded edge image, the source-edge indices in
one canonical base fibre are equivalent to the canonical-apex image of that
fibre. -/
noncomputable def baseFiberIndexEquivBaseApexImage_of_linear
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) (q : Node G)
    (hlinear : ((system G).edgeRestriction f.edgeImage).Linear) :
    Equiv (baseFiberIndex f q) (baseApex '' baseFiber f.edgeImage q) :=
  (baseFiberIndexEquivBaseFiber f q).trans
    (baseFiberEquivBaseApexImage_of_linear q hlinear)

end SequenceLift

end Erdos593
