/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteEdgeBalance
import ErdosProblems.Erdos599.SafeSwitching

/-!
# Finite coloured occurrence words

A source Rule-2 route is not necessarily a literal `AltPath`: the same
ambient vertex may occur several times, even in the same local role.  The
correct finite combinatorial object is therefore a word of vertex
occurrences whose transitions are coloured forward or backward.

Forward transitions use an edge of `W` in chronological order.  Backward
transitions use an edge of `Y` in the opposite order.  Freshness is imposed
on the pair consisting of the colour and the actual oriented edge; ambient
vertices are deliberately not required to be injective.

This file proves the key invariant rather than storing it: the balance of
the forward edge relation minus the balance of the backward edge relation
is exactly `+1` at the first occurrence and `-1` at the last occurrence.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A finite occurrence word with coloured, literally owned transitions.
Repeated ambient vertices are allowed; repeated same-colour actual edges
are not. -/
structure FiniteColouredOccurrenceWord
    (W Y : Set Gamma.DPath) where
  length : ℕ
  vertex : Fin (length + 1) → V
  direction : Fin length → Direction
  actualEdge_spec : ∀ i,
    match direction i with
    | .forward => (vertex i.castSucc, vertex i.succ) ∈ familyEdges W
    | .backward => (vertex i.succ, vertex i.castSucc) ∈ familyEdges Y
  occurrence_injective : Function.Injective
    (fun i ↦ (direction i,
      match direction i with
      | .forward => (vertex i.castSucc, vertex i.succ)
      | .backward => (vertex i.succ, vertex i.castSucc)))

namespace FiniteColouredOccurrenceWord

variable {W Y : Set Gamma.DPath}

/-- The actual ambient edge, always stored in its graph orientation. -/
def actualEdge (Q : FiniteColouredOccurrenceWord W Y)
    (i : Fin Q.length) : V × V :=
  match Q.direction i with
  | .forward => (Q.vertex i.castSucc, Q.vertex i.succ)
  | .backward => (Q.vertex i.succ, Q.vertex i.castSucc)

/-- Indices of the forward transitions. -/
def ForwardIndex (Q : FiniteColouredOccurrenceWord W Y) :=
  {i : Fin Q.length // Q.direction i = .forward}

/-- Indices of the backward transitions. -/
def BackwardIndex (Q : FiniteColouredOccurrenceWord W Y) :=
  {i : Fin Q.length // Q.direction i ≠ .forward}

theorem backwardIndex_direction (Q : FiniteColouredOccurrenceWord W Y)
    (i : Q.BackwardIndex) : Q.direction i.1 = .backward := by
  cases h : Q.direction i.1 with
  | forward => exact False.elim (i.2 h)
  | backward => rfl

/-- The actual oriented forward edge at a forward occurrence. -/
def forwardEdge (Q : FiniteColouredOccurrenceWord W Y)
    (i : Q.ForwardIndex) : V × V := Q.actualEdge i.1

/-- The actual oriented reference edge at a backward occurrence. -/
def backwardEdge (Q : FiniteColouredOccurrenceWord W Y)
    (i : Q.BackwardIndex) : V × V := Q.actualEdge i.1

/-- The inserted relation encoded by the word. -/
def forwardEdges (Q : FiniteColouredOccurrenceWord W Y) : Set (V × V) :=
  Set.range Q.forwardEdge

/-- The removed reference relation encoded by the word. -/
def backwardEdges (Q : FiniteColouredOccurrenceWord W Y) : Set (V × V) :=
  Set.range Q.backwardEdge

/-- All ambient vertices occurring in the chronological word. -/
def vertexSet (Q : FiniteColouredOccurrenceWord W Y) : Set V :=
  Set.range Q.vertex

theorem vertexSet_finite (Q : FiniteColouredOccurrenceWord W Y) :
    Q.vertexSet.Finite := Set.finite_range _

theorem vertexSet_countable (Q : FiniteColouredOccurrenceWord W Y) :
    Q.vertexSet.Countable := Q.vertexSet_finite.to_countable

theorem forwardEdges_finite (Q : FiniteColouredOccurrenceWord W Y) :
    Q.forwardEdges.Finite := by
  classical
  letI : Fintype Q.ForwardIndex := by
    unfold ForwardIndex
    infer_instance
  exact Set.finite_range _

theorem backwardEdges_finite (Q : FiniteColouredOccurrenceWord W Y) :
    Q.backwardEdges.Finite := by
  classical
  letI : Fintype Q.BackwardIndex := by
    unfold BackwardIndex
    infer_instance
  exact Set.finite_range _

theorem forwardEdges_countable (Q : FiniteColouredOccurrenceWord W Y) :
    Q.forwardEdges.Countable := Q.forwardEdges_finite.to_countable

theorem backwardEdges_countable (Q : FiniteColouredOccurrenceWord W Y) :
    Q.backwardEdges.Countable := Q.backwardEdges_finite.to_countable

theorem forwardEdge_eq (Q : FiniteColouredOccurrenceWord W Y)
    (i : Q.ForwardIndex) :
    Q.forwardEdge i = (Q.vertex i.1.castSucc, Q.vertex i.1.succ) := by
  simp [forwardEdge, FiniteColouredOccurrenceWord.actualEdge, i.2]

theorem backwardEdge_eq (Q : FiniteColouredOccurrenceWord W Y)
    (i : Q.BackwardIndex) :
    Q.backwardEdge i = (Q.vertex i.1.succ, Q.vertex i.1.castSucc) := by
  simp [backwardEdge, actualEdge, Q.backwardIndex_direction i]

theorem forwardEdges_subset_familyEdges
    (Q : FiniteColouredOccurrenceWord W Y) :
    Q.forwardEdges ⊆ familyEdges W := by
  rintro e ⟨i, rfl⟩
  simpa [forwardEdge, actualEdge, i.2] using Q.actualEdge_spec i.1

theorem backwardEdges_subset_familyEdges
    (Q : FiniteColouredOccurrenceWord W Y) :
    Q.backwardEdges ⊆ familyEdges Y := by
  rintro e ⟨i, rfl⟩
  simpa [backwardEdge, actualEdge, Q.backwardIndex_direction i] using
    Q.actualEdge_spec i.1

theorem forwardEdge_injective (Q : FiniteColouredOccurrenceWord W Y) :
    Function.Injective Q.forwardEdge := by
  intro i j hij
  apply Subtype.ext
  apply Q.occurrence_injective
  apply Prod.ext
  · exact i.2.trans j.2.symm
  · exact hij

theorem backwardEdge_injective (Q : FiniteColouredOccurrenceWord W Y) :
    Function.Injective Q.backwardEdge := by
  intro i j hij
  apply Subtype.ext
  apply Q.occurrence_injective
  apply Prod.ext
  · exact (Q.backwardIndex_direction i).trans
      (Q.backwardIndex_direction j).symm
  · exact hij

theorem forwardEdges_biUnique (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ Q.forwardEdges) := by
  have hbi := IsWarp.familyEdges_biUnique hW
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1
      (Q.forwardEdges_subset_familyEdges h₁)
      (Q.forwardEdges_subset_familyEdges h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2
      (Q.forwardEdges_subset_familyEdges h₁)
      (Q.forwardEdges_subset_familyEdges h₂)⟩

theorem backwardEdges_biUnique (Q : FiniteColouredOccurrenceWord W Y)
    (hY : Gamma.IsWarp Y) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ Q.backwardEdges) := by
  have hbi := IsWarp.familyEdges_biUnique hY
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1
      (Q.backwardEdges_subset_familyEdges h₁)
      (Q.backwardEdges_subset_familyEdges h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2
      (Q.backwardEdges_subset_familyEdges h₁)
      (Q.backwardEdges_subset_familyEdges h₂)⟩

/-- Splitting the word by colour converts the two edge balances to the
ordinary chronological contribution of every adjacent occurrence. -/
private theorem edgeBalance_difference_eq_sum
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) (x : V) :
    edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
      ∑ i : Fin Q.length,
        (propInt (x = Q.vertex i.castSucc) -
          propInt (x = Q.vertex i.succ)) := by
  classical
  letI forwardFintype : Fintype Q.ForwardIndex := by
    unfold ForwardIndex
    infer_instance
  letI backwardFintype : Fintype Q.BackwardIndex := by
    unfold BackwardIndex
    infer_instance
  let contribution : Fin Q.length → Int := fun i ↦
    propInt (x = Q.vertex i.castSucc) -
      propInt (x = Q.vertex i.succ)
  have hF := edgeBalance_range_eq_sum Q.forwardEdge
    Q.forwardEdge_injective (Q.forwardEdges_biUnique hW) x
  have hB := edgeBalance_range_eq_sum Q.backwardEdge
    Q.backwardEdge_injective (Q.backwardEdges_biUnique hY) x
  change edgeBalance (Set.range Q.forwardEdge) x -
      edgeBalance (Set.range Q.backwardEdge) x = _
  rw [hF, hB]
  have hFcontrib :
      (∑ i : Q.ForwardIndex,
          (propInt (x = (Q.forwardEdge i).1) -
            propInt (x = (Q.forwardEdge i).2))) =
        ∑ i : Q.ForwardIndex, contribution i.1 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.forwardEdge_eq]
  have hBcontrib :
      (∑ i : Q.BackwardIndex,
          (propInt (x = (Q.backwardEdge i).1) -
            propInt (x = (Q.backwardEdge i).2))) =
        ∑ i : Q.BackwardIndex, - contribution i.1 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.backwardEdge_eq]
    dsimp [contribution]
    omega
  rw [hFcontrib, hBcontrib, Finset.sum_neg_distrib, sub_neg_eq_add]
  exact Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin Q.length ↦ Q.direction i = .forward) contribution

/-- The exact signed balance law.  It follows solely from the chronological
word, literal edge ownership, and same-colour edge freshness; no vertex
injectivity or `CompatibleInOrder` hypothesis is used. -/
theorem edgeBalance_forward_sub_backward
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) (x : V) :
    edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
      propInt (x = Q.vertex 0) -
        propInt (x = Q.vertex (Fin.last Q.length)) := by
  rw [Q.edgeBalance_difference_eq_sum hW hY]
  exact sum_adjacent_propInt_eq_boundary Q.length Q.vertex x

#print axioms vertexSet_countable
#print axioms forwardEdges_countable
#print axioms backwardEdges_countable
#print axioms edgeBalance_forward_sub_backward

end FiniteColouredOccurrenceWord
end Alternating
end Erdos599
