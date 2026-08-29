/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingGapRepairObstruction
import ErdosProblems.Erdos599.SafeSwitchingRelationalBalance
import ErdosProblems.Erdos599.FiniteColouredOccurrenceWord
import Mathlib.Tactic.FinCases

/-!
# A relational Rule-2 repair of the gap obstruction

The normalized obstruction in `TwoWarpMatchingGapRepairObstruction` does
have a sound interval-convex repair, but it changes the exposed terminal.
The chronological occurrence word is

`u, c, z, t, d, c, q`.

It inserts `u-c`, `z-t`, and `c-q`, while removing the complete reference
interval `z-c-d-t`.  The repeated occurrence of `c` is essential and is
precisely what a literal `AltPath.CompatibleInOrder` cannot encode.  This
file verifies the repair through the relational interval-switching theorem:
the output is an augmenting warp with new endpoints `u` and `q`.  It does
not claim that the originally exposed `v` is preserved.
-/

namespace Erdos599
namespace TwoWarpMatchingGapRepairObstruction

open Set
open _root_.Erdos599.DirectedPath
open Alternating
open Alternating.SwitchingCore.RelationalInterval
open Vertex

/-- Forward edges read from the occurrence word
`u,c,z,t,d,c,q`. -/
def repairForward : Set (Vertex × Vertex) := {(u, c), (z, t), (c, q)}

/-- Reference edges read backwards from the same occurrence word. -/
def repairBackward : Set (Vertex × Vertex) := {(z, c), (c, d), (d, t)}

theorem familyEdges_W : familyEdges W =
    {(u, c), (c, q), (r, a), (b, d), (d, v), (z, t)} := by
  ext e
  simp [W, familyEdges]
  aesop

theorem familyEdges_Y : familyEdges Y =
    {(b, a), (z, c), (c, d), (d, t)} := by
  ext e
  simp [Y, familyEdges]
  aesop

/-- The chronological Rule-2 word.  The ambient vertex `c` occurs twice,
but no same-colour actual edge is reused. -/
def repairWord : FiniteColouredOccurrenceWord W Y where
  length := 6
  vertex := ![u, c, z, t, d, c, q]
  direction :=
    ![.forward, .backward, .forward, .backward, .backward, .forward]
  actualEdge_spec := by
    intro i
    fin_cases i <;> simp [familyEdges_W, familyEdges_Y]
  occurrence_injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

/-- The balance law of the repeated-contact route is a consequence of its
coloured occurrence word, rather than an additional certificate. -/
theorem repairWord_balance (x : Vertex) :
    edgeBalance repairWord.forwardEdges x -
        edgeBalance repairWord.backwardEdges x =
      propInt (x = u) - propInt (x = q) := by
  simpa [repairWord] using
    repairWord.edgeBalance_forward_sub_backward W_isWarp Y_isWarp x

theorem repairWord_forwardEdges : repairWord.forwardEdges = repairForward := by
  ext e
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    fin_cases i <;>
      simp [repairWord, FiniteColouredOccurrenceWord.forwardEdge,
        FiniteColouredOccurrenceWord.actualEdge, repairForward] at hi ⊢
  · intro he
    simp only [repairForward, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · change ∃ i : {i : Fin 6 //
          ![.forward, .backward, .forward, .backward, .backward, .forward] i =
            Direction.forward}, _ = (u, c)
      exact ⟨⟨0, rfl⟩, rfl⟩
    · change ∃ i : {i : Fin 6 //
          ![.forward, .backward, .forward, .backward, .backward, .forward] i =
            Direction.forward}, _ = (z, t)
      exact ⟨⟨2, rfl⟩, rfl⟩
    · change ∃ i : {i : Fin 6 //
          ![.forward, .backward, .forward, .backward, .backward, .forward] i =
            Direction.forward}, _ = (c, q)
      exact ⟨⟨5, rfl⟩, rfl⟩

theorem repairWord_backwardEdges : repairWord.backwardEdges = repairBackward := by
  ext e
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    fin_cases i <;>
      simp [repairWord, FiniteColouredOccurrenceWord.backwardEdge,
        FiniteColouredOccurrenceWord.actualEdge, repairBackward] at hi ⊢
  · intro he
    simp only [repairBackward, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · change ∃ i : {i : Fin 6 //
          ![.forward, .backward, .forward, .backward, .backward, .forward] i ≠
            Direction.forward}, _ = (z, c)
      exact ⟨⟨1, by decide⟩, rfl⟩
    · change ∃ i : {i : Fin 6 //
          ![.forward, .backward, .forward, .backward, .backward, .forward] i ≠
            Direction.forward}, _ = (c, d)
      exact ⟨⟨4, by decide⟩, rfl⟩
    · change ∃ i : {i : Fin 6 //
          ![.forward, .backward, .forward, .backward, .backward, .forward] i ≠
            Direction.forward}, _ = (d, t)
      exact ⟨⟨3, by decide⟩, rfl⟩

theorem W_hasFiniteCharacter : web.HasFiniteCharacter W := by
  intro p hp
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨ucq, rfl⟩
  · exact ⟨ra, rfl⟩
  · exact ⟨bdv, rfl⟩
  · exact ⟨zt, rfl⟩

theorem Y_hasFiniteCharacter : web.HasFiniteCharacter Y := by
  intro p hp
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨ba, rfl⟩
  · exact ⟨zcdt, rfl⟩

theorem repairBackward_subset : repairBackward ⊆ familyEdges Y := by
  rw [familyEdges_Y]
  simp [repairBackward]

theorem repairForward_subset : repairForward ⊆ familyEdges W := by
  rw [familyEdges_W]
  intro e he
  simp [repairForward] at he ⊢
  aesop

theorem repairForward_disjoint_reference :
    Disjoint repairForward (familyEdges Y) := by
  rw [familyEdges_Y]
  simp [repairForward, Set.disjoint_left]

theorem repair_incident_incoming
    {a b x : Vertex} (hF : (a, x) ∈ repairForward)
    (hY : (b, x) ∈ familyEdges Y) : (b, x) ∈ repairBackward := by
  rw [familyEdges_Y] at hY
  simp [repairForward, repairBackward] at hF hY ⊢
  aesop

theorem repair_incident_outgoing
    {x a b : Vertex} (hF : (x, a) ∈ repairForward)
    (hY : (x, b) ∈ familyEdges Y) : (x, b) ∈ repairBackward := by
  rw [familyEdges_Y] at hY
  simp [repairForward, repairBackward] at hF hY ⊢
  aesop

theorem repairBackward_interval :
    ∀ p ∈ Y, IsEdgeInterval (repairBackward ∩ p.edgeSet) p := by
  intro p hp
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · left
    ext e
    simp [repairBackward]
  · right
    refine ⟨.inl zcdt, Path.isSubpathOf_self _, ?_⟩
    ext e
    simp [repairBackward]

theorem repairForward_endpoint_pure
    {x y : Vertex} (hxy : (x, y) ∈ repairForward) :
    y ∉ web.initialSet Y ∧ x ∉ web.terminalFrontier Y := by
  have hAdj : web.graph.Adj x y :=
    familyEdges_subset_adj W (repairForward_subset hxy)
  have hnorm := web_isNormalized hAdj
  exact ⟨fun hy ↦ hnorm.1 (W_initialSet_subset_source
      (Y_initialSet_subset_W hy)),
    fun hx ↦ hnorm.2 (W_terminalFrontier_subset_target
      (Y_terminalFrontier_subset_W hx))⟩

theorem u_not_mem_vertexSet_Y : u ∉ web.vertexSet Y := by
  rintro ⟨p, hp, hup⟩
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · change u ∈ ba.support at hup
    simpa using hup
  · change u ∈ zcdt.support at hup
    simpa using hup

theorem q_not_mem_vertexSet_Y : q ∉ web.vertexSet Y := by
  rintro ⟨p, hp, hqp⟩
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · change q ∈ ba.support at hqp
    simpa using hqp
  · change q ∈ zcdt.support at hqp
    simpa using hqp

/-- The finite occurrence word has the exact one-point augmentation
balance, despite visiting `c` twice. -/
theorem repair_balance (x : Vertex) :
    edgeBalance repairForward x - edgeBalance repairBackward x =
      propInt (x = u) - propInt (x = q) := by
  rw [← repairWord_forwardEdges, ← repairWord_backwardEdges]
  exact repairWord_balance x

/-- The relational Rule-2 repair is an honest augmenting warp.  Its exposed
terminal is `q`, not the terminal `v` of the unnormalized raw matching
prefix. -/
theorem exists_gapRepairedAugmentingWarp :
    ∃ U : Set web.DPath, web.IsWarp U ∧ web.HasFiniteCharacter U ∧
      familyEdges U = (familyEdges Y \ repairBackward) ∪ repairForward ∧
      isolatedVertices U = isolatedVertices Y ∧
      web.initialSet U = web.initialSet Y ∪ {u} ∧
      web.terminalFrontier U = web.terminalFrontier Y ∪ {q} := by
  exact exists_finiteWarp_augmenting_of_balanced_intervalSwitch
    W_isWarp Y_isWarp W_hasFiniteCharacter Y_hasFiniteCharacter
    repairBackward_subset repairForward_subset
    repairForward_disjoint_reference repair_incident_incoming
    repair_incident_outgoing repairBackward_interval
    repairForward_endpoint_pure (by decide) u_not_mem_vertexSet_Y
    q_not_mem_vertexSet_Y repair_balance

#print axioms repair_balance
#print axioms repairWord_balance
#print axioms exists_gapRepairedAugmentingWarp

end TwoWarpMatchingGapRepairObstruction
end Erdos599
