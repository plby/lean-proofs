/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPointwiseSwitch

/-!
# Whole-family boundary accounting for the grounding switch

A single reducing switch deletes one old terminal and one old initial.  The
equal-index repair needs the simultaneous version: a compatible family of
decoded routes is realized by one warp, and all of their boundary changes are
made at once.

This file separates the global path-construction problem from its boundary
calculation.  Once the realized warp has the expected summed edge-balance
formula, the initial set and finite terminal frontier are exactly the old ones
with the selected endpoint sets removed.  The proof permits rays in both
warps; it uses the arbitrary-warp edge-balance characterizations from
`GroundingPointwiseSwitch`.
-/

noncomputable section

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Simultaneous reducing boundary accounting.

`terminalStarts` consists of old finite terminals at which the reducing
routes start, and `initialEnds` consists of old initials at which they end.
The displayed balance identity is the net effect of all compatible switches:
one outgoing unit is inserted at each reducing start, and one outgoing unit
is removed at each reducing end.  Disjointness excludes cancellation at a
vertex.  The non-isolation assumptions are automatic for nontrivial reducing
routes, but are stated explicitly here because they belong to the geometric
construction, not to integer accounting. -/
theorem frontiers_of_simultaneous_reducing_balance
    {Y W : Set Gamma.DPath} (hY : Gamma.IsWarp Y) (hW : Gamma.IsWarp W)
    (terminalStarts initialEnds : Set V)
    (hstarts : terminalStarts ⊆ Gamma.terminalFrontier Y)
    (hends : initialEnds ⊆ Gamma.initialSet Y)
    (hdisjoint : Disjoint terminalStarts initialEnds)
    (hstartsNotIsolated : Disjoint terminalStarts (isolatedVertices Y))
    (hendsNotIsolated : Disjoint initialEnds (isolatedVertices Y))
    (hisolated : isolatedVertices W = isolatedVertices Y)
    (hbalance : ∀ z,
      edgeBalance (familyEdges W) z =
        edgeBalance (familyEdges Y) z +
          propInt (z ∈ terminalStarts) - propInt (z ∈ initialEnds)) :
    Gamma.initialSet W = Gamma.initialSet Y \ initialEnds ∧
      Gamma.terminalFrontier W =
        Gamma.terminalFrontier Y \ terminalStarts := by
  have hstartBalance : ∀ {z}, z ∈ terminalStarts →
      edgeBalance (familyEdges Y) z = -1 := by
    intro z hz
    exact ((mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
      hY).1 (hstarts hz)).resolve_left
        (fun hzIso ↦ Set.disjoint_left.1 hstartsNotIsolated hz hzIso)
  have hendBalance : ∀ {z}, z ∈ initialEnds →
      edgeBalance (familyEdges Y) z = 1 := by
    intro z hz
    exact ((mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hY).1
      (hends hz)).resolve_left
        (fun hzIso ↦ Set.disjoint_left.1 hendsNotIsolated hz hzIso)
  have hstartNotEnd : ∀ {z}, z ∈ terminalStarts → z ∉ initialEnds := by
    intro z hzStart hzEnd
    exact Set.disjoint_left.1 hdisjoint hzStart hzEnd
  have hendNotStart : ∀ {z}, z ∈ initialEnds → z ∉ terminalStarts := by
    intro z hzEnd hzStart
    exact Set.disjoint_left.1 hdisjoint hzStart hzEnd
  constructor
  · ext z
    simp only [Set.mem_sdiff]
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hW,
      mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hY,
      hisolated, hbalance]
    by_cases hzStart : z ∈ terminalStarts
    · have hzEnd : z ∉ initialEnds := hstartNotEnd hzStart
      have hzNotIso : z ∉ isolatedVertices Y :=
        fun hzIso ↦ Set.disjoint_left.1 hstartsNotIsolated hzStart hzIso
      have hzBal : edgeBalance (familyEdges Y) z = -1 :=
        hstartBalance hzStart
      simp [propInt, hzStart, hzEnd, hzNotIso, hzBal]
    · by_cases hzEnd : z ∈ initialEnds
      · have hzNotIso : z ∉ isolatedVertices Y :=
          fun hzIso ↦ Set.disjoint_left.1 hendsNotIsolated hzEnd hzIso
        have hzBal : edgeBalance (familyEdges Y) z = 1 :=
          hendBalance hzEnd
        simp [propInt, hzStart, hzEnd, hzNotIso, hzBal]
      · simp [propInt, hzStart, hzEnd]
  · ext z
    simp only [Set.mem_sdiff]
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        hW,
      mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        hY,
      hisolated, hbalance]
    by_cases hzStart : z ∈ terminalStarts
    · have hzEnd : z ∉ initialEnds := hstartNotEnd hzStart
      have hzNotIso : z ∉ isolatedVertices Y :=
        fun hzIso ↦ Set.disjoint_left.1 hstartsNotIsolated hzStart hzIso
      have hzBal : edgeBalance (familyEdges Y) z = -1 :=
        hstartBalance hzStart
      simp [propInt, hzStart, hzEnd, hzNotIso, hzBal]
    · by_cases hzEnd : z ∈ initialEnds
      · have hzNotIso : z ∉ isolatedVertices Y :=
          fun hzIso ↦ Set.disjoint_left.1 hendsNotIsolated hzEnd hzIso
        have hzBal : edgeBalance (familyEdges Y) z = 1 :=
          hendBalance hzEnd
        simp [propInt, hzStart, hzEnd, hzNotIso, hzBal]
      · simp [propInt, hzStart, hzEnd]

end Alternating
end Erdos599
