/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPortToggleProjection

/-!
# Incoming projected incidence at an unmatched sending port

If a relation has no outgoing pair at a vertex, none of its incoming
pairs there is diagonal. Thus the exact toggle range identity applies
unchanged to the projected original-edge relation at such sinks.
-/

namespace Erdos599.GroundingPortToggle

open Set DirectedPath Alternating

universe u

variable {V : Type u} {G : DWeb V} {M : V → V → Prop}

theorem nonDiagonal_hasIncoming_iff_of_noOutgoing (x : V) (hno : ∀ y, ¬ M x y) :
    HasIncoming (nonDiagonal M) x ↔ ∃ y, M y x := by
  constructor
  · rintro ⟨y, hy, _⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, hy, ?_⟩
    intro heq
    have hyx : y = x := heq
    exact hno x (hyx ▸ hy)

theorem AugmentingPath.projectedEdges_incoming_iff_of_noOutgoing
    (D : AugmentingPath G M) (x : V)
    (hOld : ∀ y, ¬ M x y) (hNew : ∀ y, ¬ D.toggled x y) :
    HasIncoming D.projectedEdges x ↔ HasIncoming (nonDiagonal M) x ∨ x = D.last := by
  rw [AugmentingPath.projectedEdges, nonDiagonal_hasIncoming_iff_of_noOutgoing x hNew,
    D.toggled_incoming_iff, nonDiagonal_hasIncoming_iff_of_noOutgoing x hOld]

#print axioms nonDiagonal_hasIncoming_iff_of_noOutgoing
#print axioms AugmentingPath.projectedEdges_incoming_iff_of_noOutgoing

end Erdos599.GroundingPortToggle
