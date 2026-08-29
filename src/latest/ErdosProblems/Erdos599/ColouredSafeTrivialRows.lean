/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceResidualHallRoot

/-!
# Cancelling the trivial rows in the fixed safe-terminal problem

An exposed original initial that is also an original terminal has exactly
its own singleton safe row. No nonterminal source reaches such a vertex.
The resulting disjoint union gives an exact cancellation in finite Hall
counting. No matching or Hall inequality is assumed or asserted here.
-/

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

theorem first_eq_last_of_length_zero (Q : FiniteColouredOccurrenceWord W Y)
    (hzero : Q.length = 0) : Q.vertex 0 = Q.vertex (Fin.last Q.length) := by
  congr 1
  exact Fin.ext (by simp [hzero])

/-- A terminal outside the reference has no possible first transition. -/
theorem length_zero_of_first_terminal
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hterminal : Q.vertex 0 ∈ Gamma.terminalFrontier W)
    (hoff : Q.vertex 0 ∉ Gamma.vertexSet Y) : Q.length = 0 := by
  by_contra hne
  let i : Fin Q.length := ⟨0, Nat.pos_of_ne_zero hne⟩
  have hfirst : i.castSucc = 0 := Fin.ext rfl
  have hedge := Q.actualEdge_spec i
  cases hdir : Q.direction i with
  | forward =>
      simp only [hdir, hfirst] at hedge
      rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin] at hterminal
      exact hterminal.2 ⟨Q.vertex i.succ, hedge⟩
  | backward =>
      simp only [hdir, hfirst] at hedge
      exact hoff (familyEdges_subset_vertexSet_prod Y hedge).2

/-- An initial outside the reference has no possible final transition. -/
theorem length_zero_of_last_initial
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hinitial : Q.vertex (Fin.last Q.length) ∈ Gamma.initialSet W)
    (hoff : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y) : Q.length = 0 := by
  cases hlen : Q.length with
  | zero => rfl
  | succ n =>
      let i : Fin Q.length := ⟨n, by omega⟩
      have hlast : i.succ = Fin.last Q.length := Fin.ext (by simp [i, hlen])
      have hedge := Q.actualEdge_spec i
      exfalso
      cases hdir : Q.direction i with
      | forward =>
          simp only [hdir, hlast] at hedge
          rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin] at hinitial
          exact hinitial.2 ⟨Q.vertex i.castSucc, hedge⟩
      | backward =>
          simp only [hdir, hlast] at hedge
          exact hoff (familyEdges_subset_vertexSet_prod Y hedge).1

/-- Source indices which cannot be served by a zero-transition word. -/
def nonterminalSources (J : Set (ExposedInitial W Y)) : Set (ExposedInitial W Y) :=
  {s ∈ J | s.1 ∉ Gamma.terminalFrontier W}

theorem nonterminalSources_subset (J : Set (ExposedInitial W Y)) :
    nonterminalSources J ⊆ J := fun _ hs ↦ hs.1

theorem safelyReachable_eq_singleton_of_terminal
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    {s : V} (hterminal : s ∈ Gamma.terminalFrontier W)
    (hoff : s ∉ Gamma.vertexSet Y) : safelyReachable W Y s = {s} := by
  ext t
  constructor
  · rintro ⟨_ht, Q, _hQ, hfirst, hlast⟩
    have hzero := Q.length_zero_of_first_terminal hW hWfin
      (hfirst ▸ hterminal) (hfirst ▸ hoff)
    have heq := Q.first_eq_last_of_length_zero hzero
    exact Set.mem_singleton_iff.mpr (hlast.symm.trans (heq.symm.trans hfirst))
  · intro hts
    have hts' : t = s := Set.mem_singleton_iff.mp hts
    subst t
    exact ⟨⟨hterminal, hoff⟩, emptyAt s, emptyAt_isIntervalSafe s,
      emptyAt_first s, emptyAt_last s⟩

/-- A safe row from a nonterminal source never ends at an original initial. -/
theorem not_initial_of_mem_safelyReachable_nonterminal
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    {s t : V} (hs : s ∉ Gamma.terminalFrontier W)
    (ht : t ∈ safelyReachable W Y s) : t ∉ Gamma.initialSet W := by
  intro htInitial
  obtain ⟨htBoundary, Q, _hQ, hfirst, hlast⟩ := ht
  have hzero := Q.length_zero_of_last_initial hW hWfin
    (hlast ▸ htInitial) (hlast ▸ htBoundary.2)
  have hst := hfirst.symm.trans ((Q.first_eq_last_of_length_zero hzero).trans hlast)
  exact hs (hst ▸ htBoundary.1)

theorem safeTerminalUnion_split_nonterminal
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (J : Set (ExposedInitial W Y)) :
    safeTerminalUnion J = safeTerminalUnion (nonterminalSources J) ∪
      Subtype.val '' (J \ nonterminalSources J) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hsJ, hts⟩ := Set.mem_iUnion.mp hs
    by_cases hsTerminal : s.1 ∈ Gamma.terminalFrontier W
    · right
      rw [safelyReachable_eq_singleton_of_terminal hW hWfin hsTerminal s.property.2] at hts
      refine ⟨s, ⟨hsJ, ?_⟩, (Set.mem_singleton_iff.mp hts).symm⟩
      exact fun hsPlus ↦ hsPlus.2 hsTerminal
    · exact Or.inl (mem_safeTerminalUnion_of_mem_safelyReachable
        (J := nonterminalSources J) ⟨hsJ, hsTerminal⟩ hts)
  · rintro (ht | ⟨s, hs, rfl⟩)
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
      obtain ⟨hsPlus, hts⟩ := Set.mem_iUnion.mp hs
      exact mem_safeTerminalUnion_of_mem_safelyReachable hsPlus.1 hts
    · have hsTerminal : s.1 ∈ Gamma.terminalFrontier W := by
        by_contra hnot
        exact hs.2 ⟨hs.1, hnot⟩
      apply mem_safeTerminalUnion_of_mem_safelyReachable hs.1
      rw [safelyReachable_eq_singleton_of_terminal hW hWfin hsTerminal s.property.2]
      exact Set.mem_singleton _

theorem safeTerminalUnion_disjoint_trivialSources
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (J : Set (ExposedInitial W Y)) :
    Disjoint (safeTerminalUnion (nonterminalSources J))
      (Subtype.val '' (J \ nonterminalSources J)) := by
  apply Set.disjoint_left.mpr
  intro t ht htrivial
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
  obtain ⟨hsPlus, hts⟩ := Set.mem_iUnion.mp hs
  obtain ⟨r, _hr, hrval⟩ := htrivial
  exact not_initial_of_mem_safelyReachable_nonterminal hW hWfin hsPlus.2 hts
    (hrval ▸ r.property.1)

/-- The full finite Hall inequality is equivalent to that for the
nonterminal rows, with the same original warp and the same safe-word notion. -/
theorem hall_iff_nonterminalSources
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    J.ncard ≤ (safeTerminalUnion J).ncard ↔
      (nonterminalSources J).ncard ≤ (safeTerminalUnion (nonterminalSources J)).ncard := by
  have hplus := hJ.subset (nonterminalSources_subset J)
  have hN := safeTerminalUnion_finite hW hY hWfin hYfin hplus
    (fun s hs ↦ hno s hs.1)
  have hJcount := Set.ncard_sdiff_add_ncard_of_subset (nonterminalSources_subset J) hJ
  rw [safeTerminalUnion_split_nonterminal hW hWfin J,
    Set.ncard_union_eq (safeTerminalUnion_disjoint_trivialSources hW hWfin J)
      hN (hJ.sdiff.image Subtype.val),
    Set.ncard_image_of_injective _ Subtype.val_injective]
  omega

#print axioms safelyReachable_eq_singleton_of_terminal
#print axioms safeTerminalUnion_disjoint_trivialSources
#print axioms hall_iff_nonterminalSources

end Erdos599.Alternating.FiniteColouredOccurrenceWord
