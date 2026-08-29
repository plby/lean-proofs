/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentProducedRunWalk
import ErdosProblems.Erdos599.HalfwayCrossContactInternalSafety

/-!
# Contact coordinates in an actual finite compressed run walk

The projection compiler's `FiniteRunWalk` has an injective vertex sequence.
Every vertex of its compressed trace therefore has a unique bounded numeric
position.  Moreover, if all backward links avoid a cut `X`, every occurrence
of an `X`-contact belongs to a forward run.  These are the concrete ordering
facts needed by the full contact splitter.
-/

noncomputable section

open Set

namespace Erdos599.Alternating

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteRunWalk

/-- Last traversal coordinate used by the finite compressed walk. -/
def finalPosition (W : FiniteRunWalk D) : Nat :=
  (W.run W.lastRunIndex).last

/-- A concrete occurrence of a trace vertex in one of the compressed runs. -/
structure VertexOccurrence (W : FiniteRunWalk D) (x : V) where
  runIndex : Fin (W.lastIndex + 1)
  position : Nat
  first_le : (W.run runIndex).first ≤ position
  le_last : position ≤ (W.run runIndex).last
  value_eq : W.vertex position = x

namespace VertexOccurrence

variable {W : FiniteRunWalk D} {x : V}

theorem le_finalPosition (O : W.VertexOccurrence x) :
    O.position ≤ W.finalPosition := by
  exact O.le_last.trans (W.run_last_le_final O.runIndex)

theorem mem_run_support (O : W.VertexOccurrence x) :
    x ∈ (W.run O.runIndex).link.path.support := by
  rw [(W.run O.runIndex).support_eq]
  exact ⟨O.position, ⟨O.first_le, O.le_last⟩, O.value_eq⟩

/-- The compiler's bounded injectivity makes the numeric position of an
occurrence independent of the chosen containing run. -/
theorem position_eq (O P : W.VertexOccurrence x) :
    O.position = P.position := by
  apply W.vertex_injective_on O.le_finalPosition P.le_finalPosition
  exact O.value_eq.trans P.value_eq.symm

end VertexOccurrence

/-- Every vertex of the exact compressed trace has an actual run occurrence. -/
theorem exists_vertexOccurrence (W : FiniteRunWalk D) {x : V}
    (hx : x ∈ (AltPath.finite W.toFiniteTrace).vertexSet) :
    Nonempty (W.VertexOccurrence x) := by
  simp only [AltPath.vertexSet, FiniteTrace.vertexSet, Set.mem_iUnion] at hx
  obtain ⟨i, hxi⟩ := hx
  change x ∈ (W.run i).link.path.support at hxi
  rw [(W.run i).support_eq] at hxi
  obtain ⟨n, hn, hv⟩ := hxi
  exact ⟨⟨i, n, hn.1, hn.2, hv⟩⟩

/-- Canonical numeric coordinate of a compressed-trace vertex. -/
noncomputable def vertexPosition (W : FiniteRunWalk D) (x : V)
    (hx : x ∈ (AltPath.finite W.toFiniteTrace).vertexSet) : Nat :=
  (W.exists_vertexOccurrence hx).some.position

theorem vertex_vertexPosition (W : FiniteRunWalk D) (x : V)
    (hx : x ∈ (AltPath.finite W.toFiniteTrace).vertexSet) :
    W.vertex (W.vertexPosition x hx) = x :=
  (W.exists_vertexOccurrence hx).some.value_eq

theorem vertexPosition_le_final (W : FiniteRunWalk D) (x : V)
    (hx : x ∈ (AltPath.finite W.toFiniteTrace).vertexSet) :
    W.vertexPosition x hx ≤ W.finalPosition :=
  (W.exists_vertexOccurrence hx).some.le_finalPosition

theorem vertexPosition_eq_occurrence (W : FiniteRunWalk D) {x : V}
    (hx : x ∈ (AltPath.finite W.toFiniteTrace).vertexSet)
    (O : W.VertexOccurrence x) :
    W.vertexPosition x hx = O.position :=
  (W.exists_vertexOccurrence hx).some.position_eq O

theorem vertexPosition_injective (W : FiniteRunWalk D)
    {x y : V}
    (hx : x ∈ (AltPath.finite W.toFiniteTrace).vertexSet)
    (hy : y ∈ (AltPath.finite W.toFiniteTrace).vertexSet)
    (hpos : W.vertexPosition x hx = W.vertexPosition y hy) : x = y := by
  rw [← W.vertex_vertexPosition x hx, ← W.vertex_vertexPosition y hy, hpos]

/-- A trace vertex in `X` cannot occur in a backward run when every parent
backward link avoids `X`. -/
theorem VertexOccurrence.direction_eq_forward_of_mem
    (W : FiniteRunWalk D) {X : Set V} {x : V}
    (hbackwardOff : ∀ l ∈ (AltPath.finite W.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (hxX : x ∈ X) (O : W.VertexOccurrence x) :
    (W.run O.runIndex).link.direction = .forward := by
  cases hdir : (W.run O.runIndex).link.direction with
  | forward => rfl
  | backward =>
      exact False.elim (Set.disjoint_left.1
        (hbackwardOff (W.run O.runIndex).link
          (W.run_link_mem O.runIndex) hdir) O.mem_run_support hxX)

/-- Every actual contact has a forward-run occurrence at its unique numeric
coordinate. -/
theorem exists_forward_vertexOccurrence_of_mem
    (W : FiniteRunWalk D) {X : Set V} {x : V}
    (hbackwardOff : ∀ l ∈ (AltPath.finite W.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (hx : x ∈ (AltPath.finite W.toFiniteTrace).vertexSet)
    (hxX : x ∈ X) :
    ∃ O : W.VertexOccurrence x,
      (W.run O.runIndex).link.direction = .forward := by
  let O := (W.exists_vertexOccurrence hx).some
  exact ⟨O, O.direction_eq_forward_of_mem W hbackwardOff hxX⟩

end FiniteRunWalk
end Erdos599.Alternating

#print axioms Erdos599.Alternating.FiniteRunWalk.exists_vertexOccurrence
#print axioms Erdos599.Alternating.FiniteRunWalk.vertexPosition_injective
#print axioms Erdos599.Alternating.FiniteRunWalk.exists_forward_vertexOccurrence_of_mem
