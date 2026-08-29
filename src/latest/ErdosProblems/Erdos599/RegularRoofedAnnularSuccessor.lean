/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularRoofSuffixCompatibility
import ErdosProblems.Erdos599.SliceSplice

/-!
# Roofed completed rows and weak annular successors

Whole-row right-tightness is not preserved by the persistent target track.
Whole-row containment in the roof of the current ladder frontier is
preserved, and is exactly enough for completed/pending compatibility.

The old pending terminal frontier can be a proper subset of the old ladder
frontier.  Consequently source-purity of a `CleanTargetSlice` alone does not
prove ownership at every old-frontier contact.  The full source-exact
annular comparison supplies the missing argument: its component rooted at a
contact is forced by warpness to be the installed component itself.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularRoofedAnnularSuccessor

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A subfamily of a source-exact comparison warp is owned at every source
contact by its own initial coordinate.  If the subfamily starts on the old
pending terminal frontier, those contacts lie on the old pending carrier.

This is stronger than the source-purity argument for a `CleanTargetSlice`:
`C` may properly contain `terminalFrontier (pendingPart old)`. -/
theorem frontierOwner_of_subfamily_of_sourceExactWarp
    (G : DWeb V) {old full used : Set G.DPath} {C : Set V}
    (hfull : G.IsWarp full)
    (hfullInitial : G.initialSet full = C)
    (hused : used ⊆ full)
    (husedInitial : G.initialSet used ⊆
      G.terminalFrontier (pendingPart G old)) :
    G.vertexSet used ∩ C ⊆ G.vertexSet (pendingPart G old) := by
  rintro x ⟨⟨q, hqUsed, hxq⟩, hxC⟩
  have hxFullInitial : x ∈ G.initialSet full := by
    rw [hfullInitial]
    exact hxC
  obtain ⟨t, htFull, htInitial⟩ := hxFullInitial
  have hqFull : q ∈ full := hused hqUsed
  have hqt : q = t := by
    by_contra hne
    exact Set.disjoint_left.1 (hfull hqFull htFull hne)
      hxq (htInitial ▸ t.initial_mem_support)
  have hqInitial : q.initial = x := by
    rw [hqt, htInitial]
  obtain ⟨p, hpPending, hpTerminal⟩ :=
    husedInitial ⟨q, hqUsed, hqInitial⟩
  refine ⟨p, hpPending, ?_⟩
  exact G.terminal_mem_support hpTerminal

/-- Whole-roof containment is preserved when completed components are
frozen and only the pending row is starred. -/
theorem freezeCompletedStar_vertexSet_subset_roof
    (G : DWeb V) {old used : Set G.DPath} {C R : Set V}
    (hcompat : G.StarCompatible (pendingPart G old) used)
    (hchron : C ⊆ G.roof R)
    (holdRoof : G.vertexSet old ⊆ G.roof C)
    (husedRoof : G.vertexSet used ⊆ G.roof R) :
    G.vertexSet
        (RegularCompletedPendingSplice.freezeCompletedStar
          G old used hcompat) ⊆
      G.roof R := by
  rintro x ⟨p, hpResult, hxp⟩
  rcases hpResult with hpCompleted | hpStar
  · exact G.roof_cut hchron (holdRoof ⟨p, hpCompleted.1, hxp⟩)
  · exact vertexSet_star_subset_roof hcompat hchron
      (fun _ hx ↦ holdRoof ⟨hx.choose, hx.choose_spec.1.1,
        hx.choose_spec.2⟩)
      husedRoof ⟨p, hpStar, hxp⟩

/-- Specialized whole-roof preservation for an installed subfamily of a
weak annular comparison.  No right-tightness of the comparison or target
track is used. -/
theorem freezeCompletedStar_vertexSet_subset_roof_of_annular
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {old comparison used : Set G.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hab : alpha < beta)
    (holdRoof : G.vertexSet old ⊆ G.roof (L.frontier alpha))
    (hcomparison : SliceSplice.IsAnnularSlice
      G L comparison alpha beta U)
    (hused : used ⊆ comparison)
    (hcompat : G.StarCompatible (pendingPart G old) used) :
    G.vertexSet
        (RegularCompletedPendingSplice.freezeCompletedStar
          G old used hcompat) ⊆
      G.roof (L.frontier beta) := by
  apply freezeCompletedStar_vertexSet_subset_roof G hcompat
    (hL.frontierChronology hab) holdRoof
  rintro x ⟨p, hpUsed, hxp⟩
  exact (hcomparison.2 ⟨p, hused hpUsed, hxp⟩).2

/-- A roofed old row and a weak source-exact annular comparison give the
exact clean-step predicate for any installed `CleanTargetSlice` contained
in that comparison. -/
theorem cleanTargetStep_of_roofedAnnular
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {old comparison : Set G.DPath}
    {alpha beta : Ladder.Stage kappa} {U selected : Set V}
    (holdWarp : G.IsWarp old)
    (holdRoof : G.vertexSet old ⊆ G.roof (L.frontier alpha))
    (hcomparison : SliceSplice.IsAnnularSlice
      G L comparison alpha beta U)
    (S : RegularCompletedPendingSplice.CleanTargetSlice G
      (G.terminalFrontier (pendingPart G old))
      (L.frontier beta) selected)
    (hinstalled : S.target ∪ S.clean ⊆ comparison)
    (hcompat : G.StarCompatible (pendingPart G old)
      (S.target ∪ S.clean)) :
    RegularCompletedPendingSplice.IsCleanTargetStep G old
      (S.target ∪ S.clean) hcompat := by
  apply RegularRoofSuffixCompatibility.cleanTargetStep_of_roofedCompleted
    G holdWarp (hL.frontiersEssential alpha)
  · rintro x ⟨p, hpCompleted, hxp⟩
    exact holdRoof ⟨p, hpCompleted.1, hxp⟩
  · exact S.union_warp
  · rintro x ⟨p, hpInstalled, hxp⟩
    exact (hcomparison.2 ⟨p, hinstalled hpInstalled, hxp⟩).1
  · apply frontierOwner_of_subfamily_of_sourceExactWarp G
      hcomparison.1.1.isWarp hcomparison.1.1.initialSet_eq
      hinstalled
    rw [S.initialSet_union]

/-- The two source-specific conclusions needed by the canonical successor:
clean compatibility and preservation of whole-row roof containment. -/
theorem cleanTargetStep_and_result_below_roof_of_annular
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {old comparison : Set G.DPath}
    {alpha beta : Ladder.Stage kappa} {U selected : Set V}
    (hab : alpha < beta)
    (holdWarp : G.IsWarp old)
    (holdRoof : G.vertexSet old ⊆ G.roof (L.frontier alpha))
    (hcomparison : SliceSplice.IsAnnularSlice
      G L comparison alpha beta U)
    (S : RegularCompletedPendingSplice.CleanTargetSlice G
      (G.terminalFrontier (pendingPart G old))
      (L.frontier beta) selected)
    (hinstalled : S.target ∪ S.clean ⊆ comparison)
    (hcompat : G.StarCompatible (pendingPart G old)
      (S.target ∪ S.clean)) :
    RegularCompletedPendingSplice.IsCleanTargetStep G old
        (S.target ∪ S.clean) hcompat ∧
      G.vertexSet
          (RegularCompletedPendingSplice.freezeCompletedStar G old
            (S.target ∪ S.clean) hcompat) ⊆
        G.roof (L.frontier beta) := by
  exact ⟨cleanTargetStep_of_roofedAnnular hL holdWarp holdRoof
      hcomparison S hinstalled hcompat,
    freezeCompletedStar_vertexSet_subset_roof_of_annular hL hab holdRoof
      hcomparison hinstalled hcompat⟩

end RegularRoofedAnnularSuccessor
end CardinalInduction
end Erdos599
