/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceHallBoundary

/-!
# A concrete finite complete-word family with all safe terminal rows

For finitely many exposed sources without infinite safe words, the union of
their safe search carriers is finite. All complete safe words supported in
that region form a finite family. Normalization proves that this family has
every original safe terminal, with its individual source preserved.

This is not an assertion that all global complete words are supported there,
nor does it assert a Hall inequality or aggregate reference-boundary sign.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Exposed original forward initials, with their literal endpoint facts. -/
abbrev ExposedInitial (W Y : Set Gamma.DPath) :=
  {s : V // s ∈ Gamma.initialSet W \ Gamma.vertexSet Y}

/-- The common search region for a set of exposed sources. -/
def finiteSaturationCarrier (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (J : Set (ExposedInitial W Y)) : Set V :=
  ⋃ s ∈ J, safeSearchCarrier hW hY (initialSet_subset_vertexSet W s.property.1)

theorem sourceSearchCarrier_subset_finiteSaturationCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {J : Set (ExposedInitial W Y)} {s : ExposedInitial W Y} (hs : s ∈ J) :
    safeSearchCarrier hW hY (initialSet_subset_vertexSet W s.property.1) ⊆
      finiteSaturationCarrier hW hY J := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, hx⟩⟩

theorem finiteSaturationCarrier_finite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    (finiteSaturationCarrier hW hY J).Finite := by
  exact hJ.biUnion fun s hs ↦ safeSearchCarrier_finite hW hY hWfin hYfin
    (initialSet_subset_vertexSet W s.property.1) (hno s hs)

theorem finiteSaturationCarrier_referenceClosed
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (J : Set (ExposedInitial W Y)) {x : V}
    (hx : x ∈ finiteSaturationCarrier hW hY J) :
    coveredPathSupport hY x ⊆ finiteSaturationCarrier hW hY J := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hsJ, hxC⟩ := Set.mem_iUnion.mp hs
  exact (safeSearchCarrier_referenceClosed hW hY
    (initialSet_subset_vertexSet W s.property.1) s.property.2 hxC).trans
      (sourceSearchCarrier_subset_finiteSaturationCarrier hW hY hsJ)

/-- All complete safe words in the specified region, not arbitrary prefix
nodes and not an unspecified choice of one witness per endpoint. -/
def completeSafeWordsInCarrier (J : Set (ExposedInitial W Y)) (C : Set V) :
    Set (FiniteColouredOccurrenceWord W Y) :=
  {Q | Q.IsIntervalSafe ∧ Q.vertex 0 ∈ Subtype.val '' J ∧
    Q.vertex (Fin.last Q.length) ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y ∧
      Q.vertexSet ⊆ C}

theorem completeSafeWordsInCarrier_finite
    (J : Set (ExposedInitial W Y)) {C : Set V} (hC : C.Finite) :
    (completeSafeWordsInCarrier J C).Finite :=
  (finite_setOf_vertexSet_subset C hC).subset fun _ hQ ↦ hQ.2.2.2

/-- The finite complete-word family covers each original safe row, retaining
the exact individual source as well as its terminal. -/
theorem exists_completeWordInCarrier_of_mem_safelyReachable
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} {s : ExposedInitial W Y}
    (hs : s ∈ J) {t : V}
    (ht : t ∈ ColouredSafeReverseReachability.safelyReachable W Y s.1) :
    ∃ Q ∈ completeSafeWordsInCarrier J (finiteSaturationCarrier hW hY J),
      Q.vertex 0 = s.1 ∧ Q.vertex (Fin.last Q.length) = t := by
  obtain ⟨Q, hQ, hfirst, hlast, hQC⟩ :=
    exists_word_in_safeSearchCarrier_of_mem_safelyReachable hW hY hWfin hYfin
      s.property.1 s.property.2 ht
  refine ⟨Q, ⟨hQ, ?_, ?_, ?_⟩, hfirst, hlast⟩
  · exact ⟨s, hs, hfirst.symm⟩
  · rw [hlast]
    exact ht.1
  · exact hQC.trans (sourceSearchCarrier_subset_finiteSaturationCarrier hW hY hs)

/-- Conversely every member of the finite family witnesses a row belonging
to one of the specified original sources. -/
theorem completeWordInCarrier_mem_safelyReachable
    {J : Set (ExposedInitial W Y)} {C : Set V}
    {Q : FiniteColouredOccurrenceWord W Y}
    (hQ : Q ∈ completeSafeWordsInCarrier J C) :
    ∃ s ∈ J, Q.vertex 0 = s.1 ∧
      Q.vertex (Fin.last Q.length) ∈
        ColouredSafeReverseReachability.safelyReachable W Y s.1 := by
  obtain ⟨s, hsJ, hsFirst⟩ := hQ.2.1
  exact ⟨s, hsJ, hsFirst.symm,
    hQ.2.2.1, Q, hQ.1, hsFirst.symm, rfl⟩

/-- Both literal union relations in the actual complete-word family are
finite. The remaining Hall argument must prove its reference-boundary sign;
that sign is not included in this certificate. -/
theorem completeWordFamily_edges_finite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    (familyForwardEdges
      (completeSafeWordsInCarrier J (finiteSaturationCarrier hW hY J))).Finite ∧
    (familyBackwardEdges
      (completeSafeWordsInCarrier J (finiteSaturationCarrier hW hY J))).Finite := by
  have hA := completeSafeWordsInCarrier_finite J
    (finiteSaturationCarrier_finite hW hY hWfin hYfin hJ hno)
  exact ⟨familyForwardEdges_finite hA, familyBackwardEdges_finite hA⟩

#print axioms finiteSaturationCarrier_finite
#print axioms exists_completeWordInCarrier_of_mem_safelyReachable
#print axioms completeWordFamily_edges_finite

end Erdos599.Alternating.FiniteColouredOccurrenceWord
