import ErdosProblems.Erdos593.TripleSystem.SequenceLiftEmbeddedSourceBridge
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftChromatic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Missing-bridge obstruction in the sequence lift

A finite linear source whose isolated reduction is missing an incident Levi
bridge cannot be obligatory: the one-apex sequence lift of any graph without
a countable colouring is an uncountably chromatic witness which avoids it.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}
variable {X I : Type u} {F : TripleSystem X I}

/-- A missing Levi bridge in the isolated reduction of a finite linear source
is witnessed against obligatoriness by the uncountably chromatic sequence
lift. -/
theorem not_isObligatory_of_linear_of_not_isolatedReduction_bridgeAtEveryEdge
    [Fintype I]
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.BridgeAtEveryEdge) :
    ¬ F.IsObligatory := by
  classical
  intro hF
  exact not_nonempty_embedding_of_not_isolatedReduction_bridgeAtEveryEdge
    hlinear hno
    (hF _ _ (system G) (aleph0_lt_chromaticCardinal hG))

end SequenceLift

end Erdos593
