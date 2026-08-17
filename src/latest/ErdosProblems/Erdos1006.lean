/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle, Boris Alexeev
-/

import ErdosProblems.Erdos1006.Core
import ErdosProblems.Erdos1006.NesetrilRodl

/-!
# Erdős Problem 1006

Nešetřil and Rödl's finite ordered-cycle construction gives a graph with no
triangles or quadrilaterals for which every orientation is already cyclic or
becomes cyclic after one edge is reversed.  Thus the answer to the question
is negative.
-/

namespace Erdos1006

/-- The strong, literal orientation form of the negative answer: every exact
orientation of one graph of girth greater than four either already contains a
directed cycle or acquires one after reversing a single arc. -/
theorem erdos1006_orientation_counterexample :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      GirthGreaterThanFour G ∧
        ∀ D : Digraph (Fin n), IsOrientation G D →
          ¬DirectedAcyclic D ∨
            ∃ a b, D a b ∧ ¬DirectedAcyclic (reverseArc D a b) := by
  obtain ⟨G, hgirth, hmono⟩ :=
    exists_girthGreaterThanFour_everyOrderHasMonotoneFiveCycle
  exact ⟨Erdos1006NR5.N, G, hgirth,
    fun D hD ↦
      orientation_cyclic_or_badReversal_of_everyOrderHasMonotoneCycle
        hmono D hD⟩

/-- Erdős Problem 1006 has a negative answer: a finite graph with no cycle
of length three or four need not possess an acyclic orientation that remains
acyclic after every one-edge reversal. -/
theorem erdos1006 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      GirthGreaterThanFour G ∧ ¬HasGoodOrientation G := by
  obtain ⟨G, hgirth, hmono⟩ :=
    exists_girthGreaterThanFour_everyOrderHasMonotoneFiveCycle
  exact ⟨Erdos1006NR5.N, G, hgirth,
    not_hasGoodOrientation_of_everyOrderHasMonotoneCycle hmono⟩

/-- Equivalently, the universal assertion asked in Problem 1006 is false. -/
theorem erdos1006_universal_claim_false :
    ¬∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      GirthGreaterThanFour G → HasGoodOrientation G := by
  rintro hall
  obtain ⟨n, G, hgirth, hbad⟩ := erdos1006
  exact hbad (hall n G hgirth)

#print axioms erdos1006

end Erdos1006
