/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.InfiniteColouredOccurrenceBalance
import ErdosProblems.Erdos599.ColouredOccurrenceEndpointPurity

/-!
# Endpoint balance for every infinite occurrence word

Raw finite restrictions need not be safe, but they are genuine coloured
prefixes. Their chronological limit is exactly the original infinite word,
so the proved stabilization argument supplies its signed endpoint balance.
-/

namespace Erdos599.Alternating.InfiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Restrict an infinite word to its first `n` actual transitions. -/
def take (Q : InfiniteColouredOccurrenceWord W Y) (n : ℕ) :
    FiniteColouredOccurrenceWord W Y where
  length := n
  vertex := fun i ↦ Q.vertex i.val
  direction := fun i ↦ Q.direction i.val
  actualEdge_spec := fun i ↦ Q.actualEdge_spec i.val
  occurrence_injective := by
    intro i j hij
    exact Fin.ext (Q.occurrence_injective hij)

/-- The chain of all raw finite restrictions, without a prefix-safeness
claim. -/
def prefixChain (Q : InfiniteColouredOccurrenceWord W Y) :
    FiniteColouredOccurrencePrefixChain W Y where
  stage := Q.take
  grows := fun n ↦ {
    length_le := Nat.le_succ n
    vertex_eq := fun _ ↦ rfl
    direction_eq := fun _ ↦ rfl }
  length_strict := fun n ↦ Nat.lt_succ_self n

theorem ext_of_vertex_direction_eq
    {Q P : InfiniteColouredOccurrenceWord W Y}
    (hv : Q.vertex = P.vertex) (hd : Q.direction = P.direction) : Q = P := by
  cases Q
  cases P
  cases hv
  cases hd
  rfl

@[simp] theorem prefixChain_limit (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.prefixChain.limit = Q := by
  apply ext_of_vertex_direction_eq
  · funext n
    exact (Q.prefixChain.stage_vertex_eq_limit n (Fin.last n)).symm
  · funext n
    rfl

/-- The signed balance of an arbitrary infinite fresh occurrence word. -/
theorem edgeBalance_forward_sub_backward
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) (x : V) :
    edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
      propInt (x = Q.vertex 0) := by
  have h := Q.prefixChain.limit_edgeBalance_forward_sub_backward hW hY x
  simpa only [Q.prefixChain_limit] using h

theorem endpoint_pure_of_incidence_of_initial_outside
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (hin : ∀ {a b x}, (a, x) ∈ Q.forwardEdges →
      (b, x) ∈ familyEdges Y → (b, x) ∈ Q.backwardEdges)
    (hout : ∀ {x a b}, (x, a) ∈ Q.forwardEdges →
      (x, b) ∈ familyEdges Y → (x, b) ∈ Q.backwardEdges)
    (hfirst : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hisolated : ∀ {x y}, (x, y) ∈ Q.forwardEdges →
      x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y)
    {x y : V} (hxy : (x, y) ∈ Q.forwardEdges) :
    y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y := by
  apply endpoint_pure_of_incidence_balance hY hYfin
    Q.backwardEdges_subset_familyEdges hin hout _ hisolated hxy
  intro z hz
  have hzFirst : z ≠ Q.vertex 0 := fun h ↦ hfirst (h ▸ hz)
  have hb := Q.edgeBalance_forward_sub_backward hW hY z
  simp only [propInt, hzFirst, ↓reduceIte] at hb
  omega

#print axioms prefixChain_limit
#print axioms edgeBalance_forward_sub_backward
#print axioms endpoint_pure_of_incidence_of_initial_outside

end Erdos599.Alternating.InfiniteColouredOccurrenceWord
