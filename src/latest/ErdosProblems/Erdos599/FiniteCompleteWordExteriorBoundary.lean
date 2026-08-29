/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteCompleteWordDefectCounting

/-!
# Exact exterior boundaries of nontrivial complete-word families

For words starting at original initials and ending at original terminals,
the exterior positive defects are exactly the first vertices, and negative
defects exactly the last vertices. Nontriviality is explicit: a zero-length
word contributes neither sign and must be handled separately in Hall.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}
variable {A : Set (FiniteColouredOccurrenceWord W Y)} {x : V}

private theorem backwardBalance_zero_outside (Q : FiniteColouredOccurrenceWord W Y)
    (hx : x ∉ Gamma.vertexSet Y) : edgeBalance Q.backwardEdges x = 0 := by
  have hout : ¬HasOutgoing Q.backwardEdges x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y
      (Q.backwardEdges_subset_familyEdges hy)).1
  have hin : ¬HasIncoming Q.backwardEdges x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y
      (Q.backwardEdges_subset_familyEdges hy)).2
  simp [edgeBalance, hout, hin]

theorem familyDefect_eq_forwardBalance_outside
    (hx : x ∉ Gamma.vertexSet Y) :
    familyDefect A x = edgeBalance (familyForwardEdges A) x := by
  have hout : ¬HasOutgoing (familyBackwardEdges A) x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y
      (familyBackwardEdges_subset_familyEdges A hy)).1
  have hin : ¬HasIncoming (familyBackwardEdges A) x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y
      (familyBackwardEdges_subset_familyEdges A hy)).2
  simp [familyDefect, edgeBalance, hout, hin]

/-- Every positive exterior defect is an actual first occurrence, obtained
by selecting a word that supplies its outgoing forward edge. -/
theorem exists_word_starting_at_of_positiveDefect_outside
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hx : x ∉ Gamma.vertexSet Y) (hpos : familyDefect A x = 1) :
    ∃ Q ∈ A, Q.vertex 0 = x := by
  rw [familyDefect_eq_forwardBalance_outside hx] at hpos
  obtain ⟨⟨y, hxy⟩, hnoIn⟩ := edgeBalance_eq_one_iff.mp hpos
  obtain ⟨Q, hQA, hxyQ⟩ := mem_familyForwardEdges_iff.mp hxy
  have hQnoIn : ¬HasIncoming Q.forwardEdges x := by
    rintro ⟨z, hz⟩
    exact hnoIn ⟨z, mem_familyForwardEdges_iff.mpr ⟨Q, hQA, hz⟩⟩
  have hQbalance := Q.edgeBalance_forward_sub_backward hW hY x
  have hQforward : edgeBalance Q.forwardEdges x = 1 :=
    edgeBalance_eq_one_iff.mpr ⟨⟨y, hxyQ⟩, hQnoIn⟩
  rw [hQforward, backwardBalance_zero_outside Q hx] at hQbalance
  have hfirst : x = Q.vertex 0 := by
    by_contra hne
    by_cases hlast : x = Q.vertex (Fin.last Q.length)
    · simp only [propInt, if_neg hne, if_pos hlast] at hQbalance
      omega
    · simp only [propInt, if_neg hne, if_neg hlast] at hQbalance
      omega
  exact ⟨Q, hQA, hfirst.symm⟩

/-- For a nontrivial complete family, the exterior positive defects are
precisely its first-vertex image. -/
theorem positiveDefect_iff_first_outside
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hfirst : ∀ Q ∈ A, Q.vertex 0 ∈ Gamma.initialSet W)
    (hne : ∀ Q ∈ A, Q.vertex 0 ≠ Q.vertex (Fin.last Q.length))
    (hx : x ∉ Gamma.vertexSet Y) :
    familyDefect A x = 1 ↔ ∃ Q ∈ A, Q.vertex 0 = x := by
  constructor
  · exact exists_word_starting_at_of_positiveDefect_outside hW hY hx
  · rintro ⟨Q, hQA, hQx⟩
    have h := positiveBoundary_of_word_first hW hY hWfin hQA
      (hfirst Q hQA) (hQx ▸ hx) (hne Q hQA)
    simpa only [familyDefect, hQx] using h

/-- An actual nontrivial last occurrence at an original terminal gives a
negative union defect: no other word can add an outgoing forward edge. -/
theorem negativeDefect_of_word_last
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    {Q : FiniteColouredOccurrenceWord W Y} (hQA : Q ∈ A)
    (hlast : Q.vertex (Fin.last Q.length) ∈ Gamma.terminalFrontier W)
    (hlastOff : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    (hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length)) :
    familyDefect A (Q.vertex (Fin.last Q.length)) = -1 := by
  let t := Q.vertex (Fin.last Q.length)
  have hQbalance := Q.edgeBalance_forward_sub_backward hW hY t
  rw [backwardBalance_zero_outside Q hlastOff] at hQbalance
  have hQt : edgeBalance Q.forwardEdges t = -1 := by
    simpa [t, propInt, Ne.symm hne] using hQbalance
  obtain ⟨⟨y, hy⟩, _⟩ := edgeBalance_eq_neg_one_iff.mp hQt
  have hUnionIn : HasIncoming (familyForwardEdges A) t :=
    ⟨y, mem_familyForwardEdges_iff.mpr ⟨Q, hQA, hy⟩⟩
  have hUnionNoOut : ¬HasOutgoing (familyForwardEdges A) t := by
    rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at hlast
    rintro ⟨y, hy⟩
    exact hlast.2 ⟨y, familyForwardEdges_subset_familyEdges A hy⟩
  rw [familyDefect_eq_forwardBalance_outside hlastOff]
  exact edgeBalance_eq_neg_one_iff.mpr ⟨hUnionIn, hUnionNoOut⟩

/-- The negative exterior defects are exactly the last-vertex image for
nontrivial words with original initial and terminal boundaries. -/
theorem negativeDefect_iff_last_outside
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hfirst : ∀ Q ∈ A, Q.vertex 0 ∈ Gamma.initialSet W)
    (hlast : ∀ Q ∈ A, Q.vertex (Fin.last Q.length) ∈ Gamma.terminalFrontier W)
    (hne : ∀ Q ∈ A, Q.vertex 0 ≠ Q.vertex (Fin.last Q.length))
    (hx : x ∉ Gamma.vertexSet Y) :
    familyDefect A x = -1 ↔ ∃ Q ∈ A, Q.vertex (Fin.last Q.length) = x := by
  constructor
  · exact exists_word_ending_at_of_negativeBoundary_outside hW hY hWfin hfirst hx
  · rintro ⟨Q, hQA, hQx⟩
    have h := negativeDefect_of_word_last hW hY hWfin hQA
      (hlast Q hQA) (hQx ▸ hx) (hne Q hQA)
    simpa only [hQx] using h

/-- For an actual finite family of nontrivial complete words, its source
versus terminal cardinal inequality is exactly the unproved interior-defect
inequality. No finite Hall or exchange assertion is included as a premise. -/
theorem first_last_ncard_le_iff_interior_defects
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hA : A.Finite) (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    (hfirst : ∀ Q ∈ A, Q.vertex 0 ∈ Gamma.initialSet W)
    (hlast : ∀ Q ∈ A, Q.vertex (Fin.last Q.length) ∈ Gamma.terminalFrontier W)
    (hne : ∀ Q ∈ A, Q.vertex 0 ≠ Q.vertex (Fin.last Q.length)) :
    ((fun Q : FiniteColouredOccurrenceWord W Y ↦ Q.vertex 0) '' A).ncard ≤
        ((fun Q : FiniteColouredOccurrenceWord W Y ↦
          Q.vertex (Fin.last Q.length)) '' A).ncard ↔
      {x | x ∈ Gamma.vertexSet Y ∧ familyDefect A x = -1}.ncard ≤
        {x | x ∈ Gamma.vertexSet Y ∧ familyDefect A x = 1}.ncard := by
  classical
  obtain ⟨C, hC, hzero⟩ := exists_finite_defectCarrier hA
  let P := C.filter (fun x ↦ familyDefect A x = 1)
  let N := C.filter (fun x ↦ familyDefect A x = -1)
  have hmemC {x : V} {sign : Int} (hsgn : sign ≠ 0)
      (hx : familyDefect A x = sign) : x ∈ C := by
    by_contra hnot
    exact hsgn (hx.symm.trans (hzero x hnot))
  have hPouter : (↑(P.filter (fun x ↦ x ∉ Gamma.vertexSet Y)) : Set V) =
      (fun Q : FiniteColouredOccurrenceWord W Y ↦ Q.vertex 0) '' A := by
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨hxP, hxY⟩
      obtain ⟨_hxC, hpos⟩ := Finset.mem_filter.mp hxP
      exact exists_word_starting_at_of_positiveDefect_outside hW hY hxY hpos
    · rintro ⟨Q, hQA, hQx⟩
      have hxY : x ∉ Gamma.vertexSet Y := hQx ▸ (hends Q hQA).1
      have hpos := (positiveDefect_iff_first_outside hW hY hWfin hfirst hne hxY).mpr
        ⟨Q, hQA, hQx⟩
      exact ⟨Finset.mem_filter.mpr ⟨hmemC (by decide) hpos, hpos⟩, hxY⟩
  have hNouter : (↑(N.filter (fun x ↦ x ∉ Gamma.vertexSet Y)) : Set V) =
      (fun Q : FiniteColouredOccurrenceWord W Y ↦ Q.vertex (Fin.last Q.length)) '' A := by
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨hxN, hxY⟩
      obtain ⟨_hxC, hneg⟩ := Finset.mem_filter.mp hxN
      exact (negativeDefect_iff_last_outside hW hY hWfin hfirst hlast hne hxY).mp hneg
    · rintro ⟨Q, hQA, hQx⟩
      have hxY : x ∉ Gamma.vertexSet Y := hQx ▸ (hends Q hQA).2
      have hneg := (negativeDefect_iff_last_outside hW hY hWfin hfirst hlast hne hxY).mpr
        ⟨Q, hQA, hQx⟩
      exact ⟨Finset.mem_filter.mpr ⟨hmemC (by decide) hneg, hneg⟩, hxY⟩
  have hPinner : (↑(P.filter (fun x ↦ x ∈ Gamma.vertexSet Y)) : Set V) =
      {x | x ∈ Gamma.vertexSet Y ∧ familyDefect A x = 1} := by
    ext x
    simp only [P, Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq]
    constructor
    · exact fun hx ↦ ⟨hx.2, hx.1.2⟩
    · exact fun hx ↦ ⟨⟨hmemC (by decide) hx.2, hx.2⟩, hx.1⟩
  have hNinner : (↑(N.filter (fun x ↦ x ∈ Gamma.vertexSet Y)) : Set V) =
      {x | x ∈ Gamma.vertexSet Y ∧ familyDefect A x = -1} := by
    ext x
    simp only [N, Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq]
    constructor
    · exact fun hx ↦ ⟨hx.2, hx.1.2⟩
    · exact fun hx ↦ ⟨⟨hmemC (by decide) hx.2, hx.2⟩, hx.1⟩
  rw [← hPouter, ← hNouter, ← hNinner, ← hPinner]
  simpa only [Set.ncard_coe_finset] using
    (exterior_defect_inequality_iff_interior hW hY hYfin hA hsafe hends C hC
      (Gamma.vertexSet Y))

#print axioms positiveDefect_iff_first_outside
#print axioms negativeDefect_iff_last_outside
#print axioms first_last_ncard_le_iff_interior_defects

end Erdos599.Alternating.FiniteColouredOccurrenceWord
