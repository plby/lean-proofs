/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeDichotomy
import ErdosProblems.Erdos599.FiniteDeletion

/-!
# Removing an isolated source in the coloured safe dichotomy

If the selected source is an isolated member of the fixed warp, its entire
finite reduction is the zero-transition coloured word and deletion of the
corresponding trivial path.  The edge relation is unchanged, while the
initial, terminal, and isolated boundaries each lose exactly that source.

Combining this observation with the nonisolated dichotomy gives a total
single-source result.  The finite branch keeps the sharp uniform identity
`isolatedVertices U = isolatedVertices W \ {s}`; for a nonisolated source
the right-hand side is simply `isolatedVertices W`.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeReverseReachability

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Removing an isolated trivial member preserves the warp property. -/
theorem IsWarp.sdiff_trivialPath
    (hW : Gamma.IsWarp W) {s : V} (_hs : s ∈ isolatedVertices W) :
    Gamma.IsWarp (W \ {Gamma.trivialPath s}) :=
  DWeb.IsWarp.sdiff_singleton Gamma hW (Gamma.trivialPath s)

/-- Removing one member preserves finite character. -/
theorem hasFiniteCharacter_sdiff_trivialPath
    (hWfin : Gamma.HasFiniteCharacter W) (s : V) :
    Gamma.HasFiniteCharacter (W \ {Gamma.trivialPath s}) :=
  DWeb.hasFiniteCharacter_sdiff_singleton Gamma hWfin (Gamma.trivialPath s)

/-- An isolated trivial member contributes no family edge. -/
theorem familyEdges_sdiff_trivialPath
    (W : Set Gamma.DPath) (s : V) :
    familyEdges (W \ {Gamma.trivialPath s}) = familyEdges W := by
  ext e
  simp only [familyEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp.1, he⟩
  · rintro ⟨p, hp, he⟩
    by_cases hps : p = Gamma.trivialPath s
    · subst p
      simpa [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
        FinitePath.trivial, Walk.edgeSet] using he
    · exact ⟨p, ⟨hp, hps⟩, he⟩

/-- Removing the trivial member at `s` removes exactly `s` from the
explicit isolated-vertex set. -/
theorem isolatedVertices_sdiff_trivialPath
    (W : Set Gamma.DPath) (s : V) :
    isolatedVertices (W \ {Gamma.trivialPath s}) =
      isolatedVertices W \ {s} := by
  ext x
  constructor
  · rintro ⟨hxW, hxne⟩
    refine ⟨hxW, ?_⟩
    intro hxs
    have hxs' : x = s := Set.mem_singleton_iff.mp hxs
    exact hxne (Set.mem_singleton_iff.2 (by simpa [hxs']))
  · rintro ⟨hxW, hxne⟩
    refine ⟨hxW, ?_⟩
    intro hpaths
    have hxs : x = s := by
      have := congrArg DirectedPath.Path.initial
        (Set.mem_singleton_iff.mp hpaths)
      simpa using this
    exact hxne (Set.mem_singleton_iff.2 hxs)

/-- Exact initial boundary after deleting an isolated trivial member. -/
theorem initialSet_sdiff_trivialPath
    (hW : Gamma.IsWarp W) {s : V} (hs : s ∈ isolatedVertices W) :
    Gamma.initialSet (W \ {Gamma.trivialPath s}) =
      Gamma.initialSet W \ {s} := by
  simpa using DWeb.IsWarp.initialSet_sdiff_singleton Gamma hW hs

/-- Exact terminal boundary after deleting an isolated trivial member. -/
theorem terminalFrontier_sdiff_trivialPath
    (hW : Gamma.IsWarp W) {s : V} (hs : s ∈ isolatedVertices W) :
    Gamma.terminalFrontier (W \ {Gamma.trivialPath s}) =
      Gamma.terminalFrontier W \ {s} := by
  simpa using DWeb.IsWarp.terminalFrontier_sdiff_singleton Gamma hW hs
    (Gamma.terminal?_trivialPath s)

/-- The zero-transition word and deletion of the trivial member give the
complete finite branch for an isolated source. -/
theorem exists_isolated_safeFinite_reduction
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    {s : V} (hsiso : s ∈ isolatedVertices W)
    (hsOff : s ∉ Gamma.vertexSet Y) :
    ∃ t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
        Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t ∧
        ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
          Gamma.HasFiniteCharacter U ∧
          familyEdges U ⊆ familyEdges W ∪ familyEdges Y ∧
          isolatedVertices U = isolatedVertices W \ {s} ∧
          Gamma.initialSet U = Gamma.initialSet W \ {s} ∧
          Gamma.terminalFrontier U = Gamma.terminalFrontier W \ {t} := by
  let Q : FiniteColouredOccurrenceWord W Y :=
    FiniteColouredOccurrenceWord.emptyAt s
  let U : Set Gamma.DPath := W \ {Gamma.trivialPath s}
  have hsTerminal : s ∈ Gamma.terminalFrontier W :=
    ⟨Gamma.trivialPath s, hsiso, Gamma.terminal?_trivialPath s⟩
  refine ⟨s, ⟨hsTerminal, hsOff⟩, Q,
    FiniteColouredOccurrenceWord.emptyAt_isIntervalSafe s, ?_, ?_, U,
    IsWarp.sdiff_trivialPath hW hsiso,
    hasFiniteCharacter_sdiff_trivialPath hWfin s, ?_, ?_, ?_, ?_⟩
  · exact FiniteColouredOccurrenceWord.emptyAt_first s
  · exact FiniteColouredOccurrenceWord.emptyAt_last s
  · rw [familyEdges_sdiff_trivialPath W s]
    exact Set.subset_union_left
  · exact isolatedVertices_sdiff_trivialPath W s
  · exact initialSet_sdiff_trivialPath hW hsiso
  · exact terminalFrontier_sdiff_trivialPath hW hsiso

/-- Total single-source coloured safe dichotomy, including isolated
sources. -/
theorem exists_safe_occurrence_dichotomy_total
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y) :
    (∃ Q : InfiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
      Q.vertex 0 = s ∧
      ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
        familyEdges U = (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges ∧
        isolatedVertices U = isolatedVertices Y ∧
        Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
        Gamma.terminalFrontier U = Gamma.terminalFrontier Y) ∨
    (∃ t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
        Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t ∧
        ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
          familyEdges U ⊆ familyEdges W ∪ familyEdges Y ∧
          isolatedVertices U = isolatedVertices W \ {s} ∧
          Gamma.initialSet U = Gamma.initialSet W \ {s} ∧
          Gamma.terminalFrontier U = Gamma.terminalFrontier W \ {t}) := by
  classical
  by_cases hsiso : s ∈ isolatedVertices W
  · exact Or.inr (exists_isolated_safeFinite_reduction hW hWfin hsiso hsOff)
  · rcases exists_safe_occurrence_dichotomy hW hY hWfin hYfin
      hsource hinitial hterminal hs hsOff hsiso with hinfinite | hfinite
    · exact Or.inl hinfinite
    · right
      obtain ⟨t, ht, Q, hsafe, hfirst, hlast, U, hU, hUfin, hUE,
        hUI, hUinitial, hUterminal⟩ := hfinite
      refine ⟨t, ht, Q, hsafe, hfirst, hlast, U, hU, hUfin, hUE, ?_,
        hUinitial, hUterminal⟩
      rw [hUI]
      ext x
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact ⟨hx, fun hxs ↦ hsiso (hxs ▸ hx)⟩
      · exact fun hx ↦ hx.1

#print axioms exists_isolated_safeFinite_reduction
#print axioms exists_safe_occurrence_dichotomy_total

end Erdos599.ColouredSafeReverseReachability
