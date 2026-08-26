import ErdosProblems.Erdos593.TripleSystem.ObligatoryAtoms
import ErdosProblems.Erdos593.TripleSystem.PositiveAtomClassical

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The all-parameter balanced expansion atom theorem

This module packages the zero-size atom and the positive-size classical
endpoint into the single natural-number statement used by downstream results.
-/

namespace Erdos593

universe u

namespace TripleSystem

/-- Every balanced complete-bipartite private-vertex-expansion atom is
obligatory. -/
theorem completeBipartiteExpansionAtom_isObligatory (n : Nat) :
    (completeBipartiteExpansionAtom.{u} n).IsObligatory := by
  cases n with
  | zero => exact completeBipartiteExpansionAtom_zero_isObligatory
  | succ n =>
      exact completeBipartiteExpansionAtom_positive_isObligatory n.succ n.succ_pos

end TripleSystem

end Erdos593
