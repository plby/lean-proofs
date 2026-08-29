/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceFiniteReachability

/-!
# Boundary bookkeeping for finite families of safe occurrence words

Hall counting ultimately uses a saturated finite family of fixed-forward
safe words.  This file isolates the part of that argument which does not
depend on saturation.  Unions of word edge relations retain literal colour
ownership and the two incidence-removal laws.  Consequently a negative
boundary outside the reference carrier is the last vertex of one of the
selected words, while every nontrivial exposed first vertex is a positive
boundary.

No Hall inequality or sign assertion on the reference carrier is assumed or
proved here.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Union of the inserted forward relations of a family of words. -/
def familyForwardEdges
    (A : Set (FiniteColouredOccurrenceWord W Y)) : Set (V × V) :=
  ⋃ Q ∈ A, Q.forwardEdges

/-- Union of the removed reference relations of a family of words. -/
def familyBackwardEdges
    (A : Set (FiniteColouredOccurrenceWord W Y)) : Set (V × V) :=
  ⋃ Q ∈ A, Q.backwardEdges

theorem mem_familyForwardEdges_iff
    {A : Set (FiniteColouredOccurrenceWord W Y)} {e : V × V} :
    e ∈ familyForwardEdges A ↔ ∃ Q ∈ A, e ∈ Q.forwardEdges := by
  simp [familyForwardEdges]

theorem mem_familyBackwardEdges_iff
    {A : Set (FiniteColouredOccurrenceWord W Y)} {e : V × V} :
    e ∈ familyBackwardEdges A ↔ ∃ Q ∈ A, e ∈ Q.backwardEdges := by
  simp [familyBackwardEdges]

theorem familyForwardEdges_finite
    {A : Set (FiniteColouredOccurrenceWord W Y)} (hA : A.Finite) :
    (familyForwardEdges A).Finite := by
  exact hA.biUnion fun Q _ ↦ Q.forwardEdges_finite

theorem familyBackwardEdges_finite
    {A : Set (FiniteColouredOccurrenceWord W Y)} (hA : A.Finite) :
    (familyBackwardEdges A).Finite := by
  exact hA.biUnion fun Q _ ↦ Q.backwardEdges_finite

theorem familyForwardEdges_subset_familyEdges
    (A : Set (FiniteColouredOccurrenceWord W Y)) :
    familyForwardEdges A ⊆ familyEdges W := by
  intro e he
  obtain ⟨Q, _hQA, heQ⟩ := mem_familyForwardEdges_iff.mp he
  exact Q.forwardEdges_subset_familyEdges heQ

theorem familyBackwardEdges_subset_familyEdges
    (A : Set (FiniteColouredOccurrenceWord W Y)) :
    familyBackwardEdges A ⊆ familyEdges Y := by
  intro e he
  obtain ⟨Q, _hQA, heQ⟩ := mem_familyBackwardEdges_iff.mp he
  exact Q.backwardEdges_subset_familyEdges heQ

theorem familyForwardEdges_biUnique
    (hW : Gamma.IsWarp W) (A : Set (FiniteColouredOccurrenceWord W Y)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ familyForwardEdges A) := by
  have hbi := IsWarp.familyEdges_biUnique hW
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1
      (familyForwardEdges_subset_familyEdges A h₁)
      (familyForwardEdges_subset_familyEdges A h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2
      (familyForwardEdges_subset_familyEdges A h₁)
      (familyForwardEdges_subset_familyEdges A h₂)⟩

theorem familyBackwardEdges_biUnique
    (hY : Gamma.IsWarp Y) (A : Set (FiniteColouredOccurrenceWord W Y)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ familyBackwardEdges A) := by
  have hbi := IsWarp.familyEdges_biUnique hY
  exact ⟨fun _ _ _ h₁ h₂ ↦ hbi.1
      (familyBackwardEdges_subset_familyEdges A h₁)
      (familyBackwardEdges_subset_familyEdges A h₂),
    fun _ _ _ h₁ h₂ ↦ hbi.2
      (familyBackwardEdges_subset_familyEdges A h₁)
      (familyBackwardEdges_subset_familyEdges A h₂)⟩

/-- Incidence removal is stable under arbitrary unions of safe words. -/
theorem family_incoming_removed
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hA : ∀ Q ∈ A, Q.IsIntervalSafe)
    {a b x : V} (hax : (a, x) ∈ familyForwardEdges A)
    (hbx : (b, x) ∈ familyEdges Y) :
    (b, x) ∈ familyBackwardEdges A := by
  obtain ⟨Q, hQA, haxQ⟩ := mem_familyForwardEdges_iff.mp hax
  exact mem_familyBackwardEdges_iff.mpr
    ⟨Q, hQA, (hA Q hQA).incoming_removed haxQ hbx⟩

/-- The outgoing incidence-removal law is stable under the same union. -/
theorem family_outgoing_removed
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hA : ∀ Q ∈ A, Q.IsIntervalSafe)
    {x a b : V} (hxa : (x, a) ∈ familyForwardEdges A)
    (hxb : (x, b) ∈ familyEdges Y) :
    (x, b) ∈ familyBackwardEdges A := by
  obtain ⟨Q, hQA, hxaQ⟩ := mem_familyForwardEdges_iff.mp hxa
  exact mem_familyBackwardEdges_iff.mpr
    ⟨Q, hQA, (hA Q hQA).outgoing_removed hxaQ hxb⟩

theorem family_endpoint_pure
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hA : ∀ Q ∈ A, Q.IsIntervalSafe)
    {x y : V} (hxy : (x, y) ∈ familyForwardEdges A) :
    y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y := by
  obtain ⟨Q, hQA, hxyQ⟩ := mem_familyForwardEdges_iff.mp hxy
  exact (hA Q hQA).endpoint_pure hxyQ

private theorem no_backward_incidence_of_not_mem_reference
    (A : Set (FiniteColouredOccurrenceWord W Y)) {x : V}
    (hx : x ∉ Gamma.vertexSet Y) :
    ¬ HasOutgoing (familyBackwardEdges A) x ∧
      ¬ HasIncoming (familyBackwardEdges A) x := by
  constructor
  · rintro ⟨y, hxy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y
      (familyBackwardEdges_subset_familyEdges A hxy)).1
  · rintro ⟨y, hyx⟩
    exact hx (familyEdges_subset_vertexSet_prod Y
      (familyBackwardEdges_subset_familyEdges A hyx)).2

private theorem backwardBalance_zero_of_not_mem_reference
    (A : Set (FiniteColouredOccurrenceWord W Y)) {x : V}
    (hx : x ∉ Gamma.vertexSet Y) :
    edgeBalance (familyBackwardEdges A) x = 0 := by
  obtain ⟨hout, hin⟩ := no_backward_incidence_of_not_mem_reference A hx
  simp [edgeBalance, hout, hin]

/-- A negative boundary of the union outside the reference carrier is an
actual last occurrence of one of the words.  The proof chooses a word
which supplies the incoming forward edge; absence of a union outgoing edge
then forces its exact word balance to be `-1`. -/
theorem exists_word_ending_at_of_negativeBoundary_outside
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hfirst : ∀ Q ∈ A, Q.vertex 0 ∈ Gamma.initialSet W)
    {x : V} (hx : x ∉ Gamma.vertexSet Y)
    (hnegative : edgeBalance (familyForwardEdges A) x -
      edgeBalance (familyBackwardEdges A) x = -1) :
    ∃ Q ∈ A, Q.vertex (Fin.last Q.length) = x := by
  have hbackZero := backwardBalance_zero_of_not_mem_reference A hx
  have hforwardNeg : edgeBalance (familyForwardEdges A) x = -1 := by
    omega
  obtain ⟨hin, hnoOut⟩ := edgeBalance_eq_neg_one_iff.mp hforwardNeg
  obtain ⟨a, hax⟩ := hin
  obtain ⟨Q, hQA, haxQ⟩ := mem_familyForwardEdges_iff.mp hax
  have hQnoOut : ¬ HasOutgoing Q.forwardEdges x := by
    rintro ⟨y, hxy⟩
    exact hnoOut ⟨y, mem_familyForwardEdges_iff.mpr ⟨Q, hQA, hxy⟩⟩
  have hQin : HasIncoming Q.forwardEdges x := ⟨a, haxQ⟩
  have hQforwardNeg : edgeBalance Q.forwardEdges x = -1 :=
    edgeBalance_eq_neg_one_iff.mpr ⟨hQin, hQnoOut⟩
  have hQbackZero : edgeBalance Q.backwardEdges x = 0 := by
    have hQout : ¬ HasOutgoing Q.backwardEdges x := by
      rintro ⟨y, hxy⟩
      exact hx (familyEdges_subset_vertexSet_prod Y
        (Q.backwardEdges_subset_familyEdges hxy)).1
    have hQin' : ¬ HasIncoming Q.backwardEdges x := by
      rintro ⟨y, hyx⟩
      exact hx (familyEdges_subset_vertexSet_prod Y
        (Q.backwardEdges_subset_familyEdges hyx)).2
    simp [edgeBalance, hQout, hQin']
  have hxFirst : x ≠ Q.vertex 0 := by
    intro heq
    rw [heq] at hQin
    rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hfirst
    exact (hfirst Q hQA).2
      (by
        obtain ⟨y, hy⟩ := hQin
        exact ⟨y, Q.forwardEdges_subset_familyEdges hy⟩)
  have hbalance := Q.edgeBalance_forward_sub_backward hW hY x
  rw [hQforwardNeg, hQbackZero] at hbalance
  have hxLast : x = Q.vertex (Fin.last Q.length) := by
    by_contra hne
    simp [propInt, hxFirst, hne] at hbalance
  exact ⟨Q, hQA, hxLast.symm⟩

/-- A nontrivial exposed first occurrence contributes a positive boundary
to the union. -/
theorem positiveBoundary_of_word_first
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    {Q : FiniteColouredOccurrenceWord W Y} (hQA : Q ∈ A)
    (hfirst : Q.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length)) :
    edgeBalance (familyForwardEdges A) (Q.vertex 0) -
      edgeBalance (familyBackwardEdges A) (Q.vertex 0) = 1 := by
  let s := Q.vertex 0
  have hQbackZero : edgeBalance Q.backwardEdges s = 0 := by
    have hout : ¬ HasOutgoing Q.backwardEdges s := by
      rintro ⟨y, hsy⟩
      exact hfirstOff (familyEdges_subset_vertexSet_prod Y
        (Q.backwardEdges_subset_familyEdges hsy)).1
    have hin : ¬ HasIncoming Q.backwardEdges s := by
      rintro ⟨y, hys⟩
      exact hfirstOff (familyEdges_subset_vertexSet_prod Y
        (Q.backwardEdges_subset_familyEdges hys)).2
    simp [edgeBalance, hout, hin]
  have hQbalance := Q.edgeBalance_forward_sub_backward hW hY s
  have hQforwardPos : edgeBalance Q.forwardEdges s = 1 := by
    rw [hQbackZero] at hQbalance
    simpa [s, propInt, hne] using hQbalance
  obtain ⟨hQout, _hQnoIn⟩ := edgeBalance_eq_one_iff.mp hQforwardPos
  have hUnionOut : HasOutgoing (familyForwardEdges A) s := by
    obtain ⟨y, hy⟩ := hQout
    exact ⟨y, mem_familyForwardEdges_iff.mpr ⟨Q, hQA, hy⟩⟩
  have hUnionNoIn : ¬ HasIncoming (familyForwardEdges A) s := by
    rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hfirst
    rintro ⟨y, hy⟩
    exact hfirst.2 ⟨y, familyForwardEdges_subset_familyEdges A hy⟩
  have hUnionForward : edgeBalance (familyForwardEdges A) s = 1 :=
    edgeBalance_eq_one_iff.mpr ⟨hUnionOut, hUnionNoIn⟩
  have hUnionBackward := backwardBalance_zero_of_not_mem_reference A hfirstOff
  rw [hUnionForward, hUnionBackward]
  norm_num

#print axioms familyForwardEdges_finite
#print axioms familyBackwardEdges_finite
#print axioms family_incoming_removed
#print axioms family_outgoing_removed
#print axioms exists_word_ending_at_of_negativeBoundary_outside
#print axioms positiveBoundary_of_word_first

end Erdos599.Alternating.FiniteColouredOccurrenceWord
