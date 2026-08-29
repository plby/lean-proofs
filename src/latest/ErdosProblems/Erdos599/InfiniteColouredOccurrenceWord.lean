/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceAppend

/-!
# Infinite coloured occurrence words and finite prefixes

The infinite word remembers literal forward and backward edge occurrences,
with freshness imposed on the colour/edge pair.  Ambient vertices may repeat.
The finite prefix relation records the coordinate agreement needed for a
genuine omega-chain limit; its edge-preservation lemmas are derived rather
than stored as additional fields.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A countably infinite occurrence word with coloured, literally owned
transitions. -/
structure InfiniteColouredOccurrenceWord
    (W Y : Set Gamma.DPath) where
  vertex : ℕ → V
  direction : ℕ → Direction
  actualEdge_spec : ∀ i,
    match direction i with
    | .forward => (vertex i, vertex (i + 1)) ∈ familyEdges W
    | .backward => (vertex (i + 1), vertex i) ∈ familyEdges Y
  occurrence_injective : Function.Injective
    (fun i ↦ (direction i,
      match direction i with
      | .forward => (vertex i, vertex (i + 1))
      | .backward => (vertex (i + 1), vertex i)))

namespace InfiniteColouredOccurrenceWord

variable {W Y : Set Gamma.DPath}

/-- The actual ambient edge, stored in graph orientation. -/
def actualEdge (Q : InfiniteColouredOccurrenceWord W Y) (i : ℕ) : V × V :=
  match Q.direction i with
  | .forward => (Q.vertex i, Q.vertex (i + 1))
  | .backward => (Q.vertex (i + 1), Q.vertex i)

def ForwardIndex (Q : InfiniteColouredOccurrenceWord W Y) :=
  {i : ℕ // Q.direction i = .forward}

def BackwardIndex (Q : InfiniteColouredOccurrenceWord W Y) :=
  {i : ℕ // Q.direction i ≠ .forward}

theorem backwardIndex_direction (Q : InfiniteColouredOccurrenceWord W Y)
    (i : Q.BackwardIndex) : Q.direction i.1 = .backward := by
  cases h : Q.direction i.1 with
  | forward => exact False.elim (i.2 h)
  | backward => rfl

def forwardEdge (Q : InfiniteColouredOccurrenceWord W Y)
    (i : Q.ForwardIndex) : V × V := Q.actualEdge i.1

def backwardEdge (Q : InfiniteColouredOccurrenceWord W Y)
    (i : Q.BackwardIndex) : V × V := Q.actualEdge i.1

def forwardEdges (Q : InfiniteColouredOccurrenceWord W Y) : Set (V × V) :=
  Set.range Q.forwardEdge

def backwardEdges (Q : InfiniteColouredOccurrenceWord W Y) : Set (V × V) :=
  Set.range Q.backwardEdge

def vertexSet (Q : InfiniteColouredOccurrenceWord W Y) : Set V :=
  Set.range Q.vertex

theorem vertexSet_countable (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.vertexSet.Countable := Set.countable_range _

theorem forwardEdges_countable (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.forwardEdges.Countable := by
  apply (Set.countable_range Q.actualEdge).mono
  rintro e ⟨i, rfl⟩
  exact ⟨i.1, rfl⟩

theorem backwardEdges_countable (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.backwardEdges.Countable := by
  apply (Set.countable_range Q.actualEdge).mono
  rintro e ⟨i, rfl⟩
  exact ⟨i.1, rfl⟩

theorem forwardEdge_eq (Q : InfiniteColouredOccurrenceWord W Y)
    (i : Q.ForwardIndex) :
    Q.forwardEdge i = (Q.vertex i.1, Q.vertex (i.1 + 1)) := by
  simp [forwardEdge, actualEdge, i.2]

theorem backwardEdge_eq (Q : InfiniteColouredOccurrenceWord W Y)
    (i : Q.BackwardIndex) :
    Q.backwardEdge i = (Q.vertex (i.1 + 1), Q.vertex i.1) := by
  simp [backwardEdge, actualEdge, Q.backwardIndex_direction i]

theorem forwardEdges_subset_familyEdges
    (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.forwardEdges ⊆ familyEdges W := by
  rintro e ⟨i, rfl⟩
  simpa [forwardEdge, actualEdge, i.2] using Q.actualEdge_spec i.1

theorem backwardEdges_subset_familyEdges
    (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.backwardEdges ⊆ familyEdges Y := by
  rintro e ⟨i, rfl⟩
  simpa [backwardEdge, actualEdge, Q.backwardIndex_direction i] using
    Q.actualEdge_spec i.1

theorem forwardEdge_injective (Q : InfiniteColouredOccurrenceWord W Y) :
    Function.Injective Q.forwardEdge := by
  intro i j hij
  apply Subtype.ext
  apply Q.occurrence_injective
  exact Prod.ext (i.2.trans j.2.symm) hij

theorem backwardEdge_injective (Q : InfiniteColouredOccurrenceWord W Y) :
    Function.Injective Q.backwardEdge := by
  intro i j hij
  apply Subtype.ext
  apply Q.occurrence_injective
  exact Prod.ext ((Q.backwardIndex_direction i).trans
    (Q.backwardIndex_direction j).symm) hij

end InfiniteColouredOccurrenceWord

namespace FiniteColouredOccurrenceWord

variable {W Y : Set Gamma.DPath}

/-- Coordinate prefix for finite coloured words. -/
structure Prefix (Q P : FiniteColouredOccurrenceWord W Y) : Prop where
  length_le : Q.length ≤ P.length
  vertex_eq : ∀ i : Fin (Q.length + 1),
    P.vertex (i.castLE (by omega)) = Q.vertex i
  direction_eq : ∀ i : Fin Q.length,
    P.direction (i.castLE (by omega)) = Q.direction i

namespace Prefix

theorem refl (Q : FiniteColouredOccurrenceWord W Y) : Q.Prefix Q where
  length_le := le_rfl
  vertex_eq := by intro i; congr
  direction_eq := by intro i; congr

theorem trans {Q P R : FiniteColouredOccurrenceWord W Y}
    (hQP : Q.Prefix P) (hPR : P.Prefix R) : Q.Prefix R where
  length_le := hQP.length_le.trans hPR.length_le
  vertex_eq := by
    intro i
    have h₁ := hPR.vertex_eq (i.castLE (Nat.succ_le_succ hQP.length_le))
    have h₂ := hQP.vertex_eq i
    simpa using h₁.trans h₂
  direction_eq := by
    intro i
    have h₁ := hPR.direction_eq (i.castLE hQP.length_le)
    have h₂ := hQP.direction_eq i
    simpa using h₁.trans h₂

theorem actualEdge_eq {Q P : FiniteColouredOccurrenceWord W Y}
    (h : Q.Prefix P) (i : Fin Q.length) :
    P.actualEdge (i.castLE h.length_le) = Q.actualEdge i := by
  cases hd : Q.direction i with
  | forward =>
      have hdP : P.direction (i.castLE h.length_le) = .forward :=
        (h.direction_eq i).trans hd
      simp only [FiniteColouredOccurrenceWord.actualEdge, hd, hdP]
      exact Prod.ext (h.vertex_eq i.castSucc) (h.vertex_eq i.succ)
  | backward =>
      have hdP : P.direction (i.castLE h.length_le) = .backward :=
        (h.direction_eq i).trans hd
      simp only [FiniteColouredOccurrenceWord.actualEdge, hd, hdP]
      exact Prod.ext (h.vertex_eq i.succ) (h.vertex_eq i.castSucc)

theorem vertexSet_subset {Q P : FiniteColouredOccurrenceWord W Y}
    (h : Q.Prefix P) : Q.vertexSet ⊆ P.vertexSet := by
  rintro x ⟨i, rfl⟩
  exact ⟨i.castLE (Nat.succ_le_succ h.length_le), h.vertex_eq i⟩

theorem forwardEdges_subset {Q P : FiniteColouredOccurrenceWord W Y}
    (h : Q.Prefix P) : Q.forwardEdges ⊆ P.forwardEdges := by
  rintro e ⟨⟨i, hi⟩, rfl⟩
  let j : Fin P.length := i.castLE h.length_le
  have hj : P.direction j = .forward := (h.direction_eq i).trans hi
  exact ⟨⟨j, hj⟩, by simpa [forwardEdge, j] using h.actualEdge_eq i⟩

theorem backwardEdges_subset {Q P : FiniteColouredOccurrenceWord W Y}
    (h : Q.Prefix P) : Q.backwardEdges ⊆ P.backwardEdges := by
  rintro e ⟨⟨i, hi⟩, rfl⟩
  let j : Fin P.length := i.castLE h.length_le
  have hj : P.direction j ≠ .forward := by
    intro hj
    exact hi ((h.direction_eq i).symm.trans hj)
  exact ⟨⟨j, hj⟩, by simpa [backwardEdge, j] using h.actualEdge_eq i⟩

end Prefix

theorem prefix_appendForwardPath (Q : FiniteColouredOccurrenceWord W Y)
    (p : FinitePath Gamma.graph) (hjoin hp hfresh) :
    Q.Prefix (Q.appendForwardPath p hjoin hp hfresh) where
  length_le := by simp
  vertex_eq := by
    intro i
    exact Q.append_vertex_left (ofForwardPath (Y := Y) p hp) _ _ _ i
  direction_eq := by
    intro i
    change Fin.append Q.direction (ofForwardPath (Y := Y) p hp).direction
        (i.castLE (by simp)) = Q.direction i
    rw [show i.castLE (by simp) =
        i.castAdd (ofForwardPath (Y := Y) p hp).length by apply Fin.ext; rfl]
    exact Fin.append_left _ _ _

theorem prefix_appendBackwardPath (Q : FiniteColouredOccurrenceWord W Y)
    (p : FinitePath Gamma.graph) (hjoin hp hfresh) :
    Q.Prefix (Q.appendBackwardPath p hjoin hp hfresh) where
  length_le := by simp
  vertex_eq := by
    intro i
    exact Q.append_vertex_left (ofBackwardPath (W := W) p hp) _ _ _ i
  direction_eq := by
    intro i
    change Fin.append Q.direction (ofBackwardPath (W := W) p hp).direction
        (i.castLE (by simp)) = Q.direction i
    rw [show i.castLE (by simp) =
        i.castAdd (ofBackwardPath (W := W) p hp).length by apply Fin.ext; rfl]
    exact Fin.append_left _ _ _

end FiniteColouredOccurrenceWord

#print axioms InfiniteColouredOccurrenceWord.vertexSet_countable
#print axioms InfiniteColouredOccurrenceWord.forwardEdges_subset_familyEdges
#print axioms FiniteColouredOccurrenceWord.Prefix.vertexSet_subset
#print axioms FiniteColouredOccurrenceWord.Prefix.forwardEdges_subset
#print axioms FiniteColouredOccurrenceWord.prefix_appendForwardPath
#print axioms FiniteColouredOccurrenceWord.prefix_appendBackwardPath

end Alternating
end Erdos599
