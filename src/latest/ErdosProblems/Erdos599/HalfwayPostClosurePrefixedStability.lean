/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosurePrefixedBounds

/-!
# Stability from the actual terminal seed and carrier accounting

Only old terminals on the old frontier must be seeded. Any surviving
terminal on the captured frontier is either already in the small closed set
or an old terminal, and strict frontier chronology puts that old terminal on
the old frontier. Stable capture then applies in both cases.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed currentClosed : Set V}

namespace LimitMoving931GlobalClosure

theorem oldRoof_inter_capturedFrontier_subset_currentSlice
    (R : LimitMoving931GlobalClosure C globalZ seed) :
    Gamma.roof C.newSlice ∩ R.capturedGeometry.newSlice ⊆ C.newSlice := by
  rintro x ⟨hxRoof, hxNew⟩
  by_contra hxOld
  have hxStrict : x ∈ Gamma.strictRoof (C.ladder.frontier C.newStage) := by
    refine ⟨hxRoof, ?_⟩
    rw [C.legal.frontiersEssential C.newStage]
    exact hxOld
  exact Set.disjoint_left.1 (C.legal.strictFrontierChronology R.later.current_lt)
    hxStrict hxNew

theorem prefixed_stable_of_seeded_terminals
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hold : current.edgeSet ⊆ U.edgeSet)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ R.closedSet)
    (hseed : current.terminalSet ∩ C.newSlice ⊆ seed) :
    U.Stable R.capturedGeometry.newSlice C.persistent := by
  rintro x ⟨hxTerm, hxNew⟩
  have hxU : x ∈ U.vertexSet := by
    obtain ⟨p, hp, hpx⟩ := hxTerm
    exact ⟨p, hp, (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support hpx⟩
  have hxClosed : x ∈ R.closedSet := by
    rcases hcarrier hxU with hxOld | hxClosed
    · have hxOldTerm : x ∈ current.terminalSet := by
        change x ∈ (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminalFrontier
          current.paths
        rw [isWarp_terminalFrontier_eq_noOutgoing current.isWarp]
        refine ⟨hxOld, ?_⟩
        rintro ⟨y, hxy⟩
        exact isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
          U.isWarp hxTerm ⟨y, hold hxy⟩
      have hxSlice : x ∈ C.newSlice :=
        R.oldRoof_inter_capturedFrontier_subset_currentSlice
          ⟨hcurrent.vertices_roofed hxOld, hxNew⟩
      exact R.seed_subset (hseed ⟨hxOldTerm, hxSlice⟩)
    · exact hxClosed
  have hxCapture : x ∈ R.closedSet ∩ C.ladder.frontier R.later.stage :=
    ⟨hxClosed, hxNew⟩
  rw [R.frontier_inter] at hxCapture
  exact hxCapture.2

#print axioms oldRoof_inter_capturedFrontier_subset_currentSlice
#print axioms prefixed_stable_of_seeded_terminals

end LimitMoving931GlobalClosure
end Erdos599.Blueprint.LinkageBlueprint
