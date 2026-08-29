/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate

/-!
# A total choice from a family of vertex sets

Registration coordinates need an extensional, total choice operation on a
family of possible vertex sets.  On a nonempty family it chooses a member;
on the empty family it returns the empty set.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

universe u

variable {V : Type u}

/-- Choose a member of a nonempty family of vertex sets, with `∅` as the
total fallback for an empty family. -/
noncomputable def chooseVertexSet (families : Set (Set V)) : Set V := by
  classical
  exact if h : families.Nonempty then Classical.choose h else ∅

/-- On a nonempty family, `chooseVertexSet` really is a member. -/
theorem chooseVertexSet_mem {families : Set (Set V)}
    (h : families.Nonempty) :
    chooseVertexSet families ∈ families := by
  rw [chooseVertexSet, dif_pos h]
  exact Classical.choose_spec h

end SliceCandidate
end CardinalInduction
end Erdos599
