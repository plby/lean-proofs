/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeTrivialRows
import ErdosProblems.Erdos599.FiniteCompleteWordExteriorBoundary

/-!
# Exact finite Hall obligation for the actual saturated safe-word family

The complete words in the proved finite saturation carrier have precisely
the prescribed source image and the original safe-terminal union. Cancelling
trivial rows makes all remaining words nontrivial, so the checked exterior
count applies. This reduces finite Hall to the interior-defect inequality
for this concrete family; that inequality is not asserted here.
-/

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- All complete safe words in the actual source search carrier. -/
def saturatedCompleteWords (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (J : Set (ExposedInitial W Y)) : Set (FiniteColouredOccurrenceWord W Y) :=
  completeSafeWordsInCarrier J (finiteSaturationCarrier hW hY J)

theorem saturatedCompleteWords_finite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    (saturatedCompleteWords hW hY J).Finite :=
  completeSafeWordsInCarrier_finite J
    (finiteSaturationCarrier_finite hW hY hWfin hYfin hJ hno)

/-- Absence of the infinite alternative ensures that every prescribed
source actually occurs in the normalized complete-word family. -/
theorem first_image_saturatedCompleteWords
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (ExposedInitial W Y)}
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    (fun Q : FiniteColouredOccurrenceWord W Y ↦ Q.vertex 0) ''
      saturatedCompleteWords hW hY J = Subtype.val '' J := by
  ext x
  constructor
  · rintro ⟨Q, hQA, hQx⟩
    exact hQx ▸ hQA.2.1
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨t, ht, _hroute⟩ := exists_safeTerminal_residualPath_of_no_safeInfinite
      hW hY hWfin hYfin hsource hterminal s.property.1 s.property.2 (hno s hs)
    obtain ⟨Q, hQA, hfirst, _hlast⟩ :=
      exists_completeWordInCarrier_of_mem_safelyReachable hW hY hWfin hYfin hs ht
    exact ⟨Q, hQA, hfirst⟩

/-- The complete family captures all original safe terminals, including
their individual source witnesses, and creates no artificial terminal. -/
theorem last_image_saturatedCompleteWords
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (J : Set (ExposedInitial W Y)) :
    (fun Q : FiniteColouredOccurrenceWord W Y ↦ Q.vertex (Fin.last Q.length)) ''
      saturatedCompleteWords hW hY J = safeTerminalUnion J := by
  ext t
  constructor
  · rintro ⟨Q, hQA, hlast⟩
    obtain ⟨s, hs, _hfirst, ht⟩ := completeWordInCarrier_mem_safelyReachable hQA
    exact hlast ▸ mem_safeTerminalUnion_of_mem_safelyReachable hs ht
  · intro ht
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hsJ, hts⟩ := Set.mem_iUnion.mp hs
    obtain ⟨Q, hQA, _hfirst, hlast⟩ :=
      exists_completeWordInCarrier_of_mem_safelyReachable hW hY hWfin hYfin hsJ hts
    exact ⟨Q, hQA, hlast⟩

theorem saturatedCompleteWords_safe
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {J : Set (ExposedInitial W Y)} {Q : FiniteColouredOccurrenceWord W Y}
    (hQ : Q ∈ saturatedCompleteWords hW hY J) : Q.IsIntervalSafe := hQ.1

theorem saturatedCompleteWords_first_initial
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {J : Set (ExposedInitial W Y)} {Q : FiniteColouredOccurrenceWord W Y}
    (hQ : Q ∈ saturatedCompleteWords hW hY J) : Q.vertex 0 ∈ Gamma.initialSet W := by
  obtain ⟨s, _hs, hfirst⟩ := hQ.2.1
  exact hfirst ▸ s.property.1

theorem saturatedCompleteWords_ends_off_reference
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {J : Set (ExposedInitial W Y)} {Q : FiniteColouredOccurrenceWord W Y}
    (hQ : Q ∈ saturatedCompleteWords hW hY J) :
    Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y := by
  obtain ⟨s, _hs, hfirst⟩ := hQ.2.1
  exact ⟨hfirst ▸ s.property.2, hQ.2.2.1.2⟩

theorem saturatedCompleteWords_nonterminal_ne
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {J : Set (ExposedInitial W Y)} {Q : FiniteColouredOccurrenceWord W Y}
    (hQ : Q ∈ saturatedCompleteWords hW hY (nonterminalSources J)) :
    Q.vertex 0 ≠ Q.vertex (Fin.last Q.length) := by
  obtain ⟨s, hs, hfirst⟩ := hQ.2.1
  intro heq
  exact hs.2 ((hfirst.trans heq) ▸ hQ.2.2.1.1)

/-- The exact remaining finite Hall assertion, instantiated on the
constructed family after cancelling all zero-transition source rows. -/
theorem hall_iff_saturated_interior_defects
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    J.ncard ≤ (safeTerminalUnion J).ncard ↔
      {x | x ∈ Gamma.vertexSet Y ∧
        familyDefect (saturatedCompleteWords hW hY (nonterminalSources J)) x = -1}.ncard ≤
      {x | x ∈ Gamma.vertexSet Y ∧
        familyDefect (saturatedCompleteWords hW hY (nonterminalSources J)) x = 1}.ncard := by
  rw [hall_iff_nonterminalSources hW hY hWfin hYfin hJ hno]
  have hnoPlus : ∀ s ∈ nonterminalSources J,
      ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s.1 := fun s hs ↦ hno s hs.1
  have hA := saturatedCompleteWords_finite hW hY hWfin hYfin
    (hJ.subset (nonterminalSources_subset J)) hnoPlus
  have hcount := first_last_ncard_le_iff_interior_defects hW hY hWfin hYfin hA
    (fun _ hQ ↦ saturatedCompleteWords_safe hW hY hQ)
    (fun _ hQ ↦ saturatedCompleteWords_ends_off_reference hW hY hQ)
    (fun _ hQ ↦ saturatedCompleteWords_first_initial hW hY hQ)
    (fun _ hQ ↦ hQ.2.2.1.1)
    (fun _ hQ ↦ saturatedCompleteWords_nonterminal_ne hW hY hQ)
  rw [first_image_saturatedCompleteWords hW hY hWfin hYfin hsource hterminal hnoPlus,
    last_image_saturatedCompleteWords hW hY hWfin hYfin,
    Set.ncard_image_of_injective _ Subtype.val_injective] at hcount
  exact hcount

#print axioms first_image_saturatedCompleteWords
#print axioms last_image_saturatedCompleteWords
#print axioms hall_iff_saturated_interior_defects

end Erdos599.Alternating.FiniteColouredOccurrenceWord
