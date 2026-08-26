import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiber

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fibre-local equivalence for sequence lifts

Under a linear restriction, the canonical base letter is an explicit
equivalence from each selected base fibre to its own image.  This is a
fibre-local structural interface; it makes no identification between images
from different base fibres and asserts no global trace decomposition.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Under a linear restriction, the canonical base letter identifies one
canonical base fibre with its own base-letter image. -/
noncomputable def baseFiberEquivBaseLetterImage_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    baseFiber S q ≃ (baseLetter '' baseFiber S q) :=
  Equiv.ofBijective
    (fun e => ⟨baseLetter e.1, ⟨e.1, e.2, rfl⟩⟩)
    (by
      constructor
      · intro e₁ e₂ h
        apply Subtype.ext
        exact baseLetter_injOn_baseFiber_of_linear q hlinear e₁.2 e₂.2
          (congrArg Subtype.val h)
      · rintro ⟨letter, e, he, rfl⟩
        exact ⟨⟨e, he⟩, rfl⟩)

end SequenceLift

end Erdos593
