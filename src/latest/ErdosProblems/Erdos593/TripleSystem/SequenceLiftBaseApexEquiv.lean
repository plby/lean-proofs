import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseApex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fibre-local apex equivalence for sequence lifts

Under a linear restriction, the canonical apex map gives an explicit
equivalence from one selected base fibre to its own apex image. This remains
fibre-local: it makes no identification between images from different base
fibres and asserts no global union, cardinality, or trace decomposition.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Under a linear restriction, the canonical apex map identifies one
canonical base fibre with its own apex image. -/
noncomputable def baseFiberEquivBaseApexImage_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    Equiv (baseFiber S q) (baseApex '' baseFiber S q) :=
  Equiv.ofBijective
    (fun e =>
      Subtype.mk (baseApex e.val)
        (by
          exact Exists.intro e.val (And.intro e.property rfl)))
    (by
      exact And.intro
        (by
          intro e1 e2 h
          apply Subtype.ext
          exact baseApex_injOn_baseFiber_of_linear q hlinear e1.property e2.property
            (congrArg Subtype.val h))
        (by
          intro y
          apply Exists.elim y.property
          intro e he
          exact Exists.intro (Subtype.mk e he.left) (Subtype.ext he.right)))

end SequenceLift

end Erdos593
