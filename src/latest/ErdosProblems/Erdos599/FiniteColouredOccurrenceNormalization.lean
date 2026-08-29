/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalizationStep

/-!
# Normalizing one fixed finite safe occurrence word

The local normalization step cannot continue indefinitely: every strict
successor adds a new coloured edge occurrence, while all of its forward and
backward edges lie in the fixed finite total word.  Consequently the process
terminates at a safe word with the same source and the same terminal.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Inclusion of both coloured edge relations gives a numerical length
bound.  The injection is constructed by choosing the unique occurrence of
each same-colour edge in the fixed total word. -/
theorem length_le_of_forward_backward_subset
    {Q total : FiniteColouredOccurrenceWord W Y}
    (hforward : Q.forwardEdges ⊆ total.forwardEdges)
    (hbackward : Q.backwardEdges ⊆ total.backwardEdges) :
    Q.length ≤ total.length := by
  classical
  have hexists (i : Fin Q.length) :
      ∃ j : Fin total.length,
        total.direction j = Q.direction i ∧
          total.actualEdge j = Q.actualEdge i := by
    cases hd : Q.direction i with
    | forward =>
        have hmemQ : Q.actualEdge i ∈ Q.forwardEdges := by
          exact ⟨⟨i, hd⟩, rfl⟩
        obtain ⟨j, hj⟩ := hforward hmemQ
        exact ⟨j.1, j.2, hj⟩
    | backward =>
        have hi : Q.direction i ≠ .forward := by simp [hd]
        have hmemQ : Q.actualEdge i ∈ Q.backwardEdges := by
          exact ⟨⟨i, hi⟩, rfl⟩
        obtain ⟨j, hj⟩ := hbackward hmemQ
        exact ⟨j.1, total.backwardIndex_direction j, hj⟩
  let f : Fin Q.length → Fin total.length := fun i ↦ (hexists i).choose
  have hf_spec (i : Fin Q.length) :
      total.direction (f i) = Q.direction i ∧
        total.actualEdge (f i) = Q.actualEdge i :=
    (hexists i).choose_spec
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Q.occurrence_injective
    apply Prod.ext
    · exact (hf_spec i).1.symm.trans
        ((congrArg total.direction hij).trans (hf_spec j).1)
    · exact (hf_spec i).2.symm.trans
        ((congrArg total.actualEdge hij).trans (hf_spec j).2)
  simpa using Fintype.card_le_of_injective f hfinj

theorem FixedSafePrefixState.length_le_total
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) : S.word.length ≤ total.length :=
  length_le_of_forward_backward_subset S.forward_subset S.backward_subset

/-- The one-step relation underlying the fixed normalization history. -/
def FixedNormalizationSuccessorRelation
    {total : FiniteColouredOccurrenceWord W Y}
    (S T : FixedSafePrefixState total) : Prop :=
  ∃ N : FixedSafePrefixSuccessor S, N.next = T

/-- The last anchored state either already is the normalized terminal word,
or is followed by the one literal forward suffix retained by
`FixedNormalizedTerminalExtension`. -/
structure FixedNormalizationConclusion
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) : Type u where
  terminal : FixedNormalizedTerminal S
  local_step : terminal.word = S.word ∨
    ∃ E : FixedNormalizedTerminalExtension S,
      E.terminal.word = terminal.word

/-- The finite normalization history itself.  `reach` retains every actual
strict successor, while `terminal` retains the final forward suffix. -/
structure FixedNormalizationDerivation
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total) : Type u where
  last : FixedSafePrefixState total
  reach : Relation.ReflTransGen FixedNormalizationSuccessorRelation S last
  embedding : Prefix (S.word) (last.word)
  conclusion : FixedNormalizationConclusion last

/-- Compose the literal prefix embeddings along a finite derivation. -/
def FixedNormalizationDerivation.toTerminal
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total}
    (D : FixedNormalizationDerivation S) : FixedNormalizedTerminal S := {
  word := D.conclusion.terminal.word
  safe := D.conclusion.terminal.safe
  first_eq := D.conclusion.terminal.first_eq
  last_eq := D.conclusion.terminal.last_eq
  forward_subset := D.conclusion.terminal.forward_subset
  backward_subset := D.conclusion.terminal.backward_subset
  embedding := D.embedding.trans D.conclusion.terminal.embedding
  length_le := D.embedding.length_le.trans D.conclusion.terminal.length_le }

/-- The actual finite sequence of canonical full-lower normalization states
exists from every fixed-prefix state. -/
theorem FixedSafePrefixState.exists_normalizationDerivation
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (S : FixedSafePrefixState total) :
    Nonempty (FixedNormalizationDerivation S) := by
  classical
  let P : ℕ → Prop := fun n ↦ ∀ S : FixedSafePrefixState total,
    total.length - S.word.length = n →
      Nonempty (FixedNormalizationDerivation S)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hremaining
        by_cases hdone : S.word.vertex (Fin.last S.word.length) =
            total.vertex (Fin.last total.length)
        · exact ⟨{
            last := S
            reach := .refl
            embedding := Prefix.refl S.word
            conclusion := {
              terminal := {
                word := S.word
                safe := S.safe
                first_eq := S.first_eq
                last_eq := hdone
                forward_subset := S.forward_subset
                backward_subset := S.backward_subset
                embedding := Prefix.refl S.word
                length_le := le_rfl }
              local_step := Or.inl rfl } }⟩
        · obtain ⟨step⟩ := S.exists_normalizationStep hW hY hWfin hYfin
            htotal hfirst hfirstOff hlast hlastOff hdone
          rcases step with terminal | successor
          · exact ⟨{
              last := S
              reach := .refl
              embedding := Prefix.refl S.word
              conclusion := {
                terminal := terminal.terminal
                local_step := Or.inr ⟨terminal, rfl⟩ } }⟩
          · have hnextBound := successor.next.length_le_total
            have hless : total.length - successor.next.word.length < n := by
              have hstateTotal : S.word.length < total.length :=
                successor.length_lt.trans_le hnextBound
              have hsub := Nat.sub_lt_sub_left hstateTotal successor.length_lt
              simpa only [hremaining] using hsub
            obtain ⟨tail⟩ := ih _ hless successor.next rfl
            exact ⟨{
              last := tail.last
              reach := (Relation.ReflTransGen.single ⟨successor, rfl⟩).trans
                tail.reach
              embedding := successor.embedding.trans tail.embedding
              conclusion := tail.conclusion }⟩
  exact hP (total.length - S.word.length) S rfl

/-- Every fixed safe word satisfying the common endpoint conditions has a
safe full-lower normalization with the same source and terminal and with no
new coloured edges. -/
theorem FixedSafePrefixState.exists_normalizedTerminal
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y)
    (S : FixedSafePrefixState total) :
    Nonempty (FixedNormalizedTerminal S) := by
  obtain ⟨D⟩ := S.exists_normalizationDerivation hW hY hWfin hYfin
    htotal hfirst hfirstOff hlast hlastOff
  exact ⟨D.toTerminal⟩

/-- The root-tight normalization, started from the empty word at the fixed
source. -/
theorem exists_normalized_same_terminal
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (total : FiniteColouredOccurrenceWord W Y)
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    ∃ Q : FiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = total.vertex 0 ∧
      Q.vertex (Fin.last Q.length) = total.vertex (Fin.last total.length) ∧
      Q.forwardEdges ⊆ total.forwardEdges ∧
      Q.backwardEdges ⊆ total.backwardEdges := by
  obtain ⟨T⟩ := (FixedSafePrefixState.initial total).exists_normalizedTerminal
    hW hY hWfin hYfin htotal hfirst hfirstOff hlast hlastOff
  exact ⟨T.word, T.safe, T.first_eq, T.last_eq,
    T.forward_subset, T.backward_subset⟩

#print axioms length_le_of_forward_backward_subset
#print axioms FixedSafePrefixState.exists_normalizationDerivation
#print axioms FixedSafePrefixState.exists_normalizedTerminal
#print axioms exists_normalized_same_terminal

end Erdos599.Alternating.FiniteColouredOccurrenceWord
