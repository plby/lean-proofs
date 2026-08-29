/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeDichotomy
import ErdosProblems.Erdos599.ColouredSafeFiniteSaturation

/-!
# Actual residual roots for finite Hall counting

For a fixed forward/reference pair, absence of a safe infinite occurrence
forces each exposed source into the reverse-reachable set used by the
single-source construction.  Unfolding that set supplies an actual safe
terminal in the source's fixed row together with a literal residual-port
path from the terminal to the source.

The finite-family form records that all such paths are rooted in the union
of the fixed safe rows.  It does not assert a packing or a Hall inequality;
that remaining step is a genuine multi-source residual exchange theorem.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating
open ColouredResidualPortContinuation

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- If the fixed-forward infinite alternative is absent, the source belongs
to its actual reverse-reachable set. -/
theorem mem_reverseReachable_of_no_safeInfinite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y)
    (hno : ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) :
    s ∈ reverseReachable W Y s := by
  by_contra hsC
  obtain ⟨Q, hQ, hfirst, _U, _hU, _hUfin, _hUE, _hUI, _hUinitial,
      _hUterminal⟩ :=
    exists_safeInfinite_of_source_not_reverseReachable hW hY hWfin hYfin
      hsource hterminal hs hsOff hsC
  exact hno ⟨Q, hQ, hfirst⟩

/-- The no-infinite hypothesis therefore gives a safe terminal in the
fixed row and a literal residual-port route from it to the source. -/
theorem exists_safeTerminal_residualPath_of_no_safeInfinite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y)
    (hno : ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) :
    ∃ t ∈ safelyReachable W Y s,
      Relation.ReflTransGen (ResidualStep W Y) (.inr t) (.inl s) := by
  exact mem_reverseReachable_of_no_safeInfinite hW hY hWfin hYfin
    hsource hterminal hs hsOff hno

/-- The union of all fixed safe rows indexed by `J`. -/
def safeTerminalUnion
    (J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)) : Set V :=
  ⋃ s ∈ J, safelyReachable W Y s.1

theorem mem_safeTerminalUnion_of_mem_safelyReachable
    {J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)}
    {s : FiniteColouredOccurrenceWord.ExposedInitial W Y} (hs : s ∈ J)
    {t : V} (ht : t ∈ safelyReachable W Y s.1) :
    t ∈ safeTerminalUnion J := by
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, ht⟩⟩

/-- For a finite no-infinite source family, the set of residual roots is
itself finite.  This uses the proved one-row compactness theorem, not a Hall
assumption. -/
theorem safeTerminalUnion_finite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)}
    (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    (safeTerminalUnion J).Finite := by
  exact hJ.biUnion fun s hs ↦
    FiniteColouredOccurrenceWord.safelyReachable_finite_of_no_safeInfinite
      hW hY hWfin hYfin s.property.1 s.property.2 (hno s hs)

/-- Every member of a no-infinite source family is reached in the residual
port graph from a root in the union of its actual fixed safe rows. -/
theorem exists_residualPath_from_safeTerminalUnion
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)}
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1)
    {s : FiniteColouredOccurrenceWord.ExposedInitial W Y} (hs : s ∈ J) :
    ∃ t ∈ safeTerminalUnion J,
      Relation.ReflTransGen (ResidualStep W Y) (.inr t) (.inl s.1) := by
  obtain ⟨t, ht, hroute⟩ :=
    exists_safeTerminal_residualPath_of_no_safeInfinite hW hY hWfin hYfin
      hsource hterminal s.property.1 s.property.2 (hno s hs)
  exact ⟨t, mem_safeTerminalUnion_of_mem_safelyReachable hs ht, hroute⟩

#print axioms mem_reverseReachable_of_no_safeInfinite
#print axioms exists_safeTerminal_residualPath_of_no_safeInfinite
#print axioms safeTerminalUnion_finite
#print axioms exists_residualPath_from_safeTerminalUnion

end Erdos599.ColouredSafeReverseReachability
