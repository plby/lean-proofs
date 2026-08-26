import ErdosProblems.Erdos593.TripleSystem.FiniteLiftGeneratedBridge
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftEmbeddedSourceEndpoints

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Bridge obstruction for finite linear sources embedded in a sequence lift

The finite lift-generation endpoint already gives the isolated reduction of a
finite linear embedded source. The generic finite-lift bridge invariant then
turns that into the structural bridge-at-every-edge witness used by the
classical classification obstruction side.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}
variable {X I : Type u} {F : TripleSystem X I}

/-- The isolated reduction of a finite linear source embedded in a sequence
lift has a Levi bridge incident to every hyperedge. -/
theorem isolatedReduction_bridgeAtEveryEdge_of_linear_of_embedding
    [Fintype I]
    (f : F.Embedding (system G)) (hlinear : F.Linear) :
    F.isolatedReduction.BridgeAtEveryEdge := by
  exact TripleSystem.FiniteLiftGenerated.bridgeAtEveryEdge G
    (isolatedReduction_finiteLiftGenerated_of_linear_of_embedding f hlinear)

/-- A finite linear source whose isolated reduction has no Levi bridge
incident to some hyperedge cannot embed into a sequence lift. -/
theorem not_nonempty_embedding_of_not_isolatedReduction_bridgeAtEveryEdge
    [Fintype I]
    (hlinear : F.Linear)
    (hno : Not F.isolatedReduction.BridgeAtEveryEdge) :
    Not (Nonempty (F.Embedding (system G))) := by
  intro h
  cases h with
  | intro f =>
      exact hno (isolatedReduction_bridgeAtEveryEdge_of_linear_of_embedding f hlinear)

end SequenceLift

end Erdos593
