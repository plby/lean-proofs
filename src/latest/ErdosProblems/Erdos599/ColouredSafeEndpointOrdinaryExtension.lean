/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointTargetLedger

/-!
# Actual closure-to-target ordinary endpoint extension

Starting with a captured deletion-safe path, close its carrier together with
the old blueprint before constructing the interval row and its assignment.
The result is a stable, source-covered later blueprint reaching the true target.
Captured safe-path production and the fair-history terminal ledger remain
separate obligations, not implicit assumptions of the public Erdős theorem.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}

theorem safePath_card_vertices {z : V} (P : SafeCurrentStageTargetPath C z) :
    #(Gamma.vertexSet P.ambientFamily) ≤ kappa := by
  have hz : z ∈ Gamma.initialSet P.ambientFamily :=
    P.ambient_linkage.initialSet_eq.symm ▸ Set.mem_singleton z
  obtain ⟨q, hq, hqz⟩ := hz
  obtain ⟨p, rfl⟩ := P.ambient_linkage.finiteCharacter hq
  have hV : Gamma.vertexSet P.ambientFamily = p.support := by
    ext x
    constructor
    · rintro ⟨q, hq', hxq⟩
      have hqz' : q.initial = z := by
        have hqi : q.initial ∈ Gamma.initialSet P.ambientFamily := ⟨q, hq', rfl⟩
        rw [P.ambient_linkage.initialSet_eq] at hqi
        exact Set.mem_singleton_iff.mp hqi
      have hEq : q = Sum.inl p := DWeb.IsWarp.eq_of_mem_support
        P.ambient_linkage.isWarp hq' hq q.initial_mem_support
          ((hqz'.trans hqz.symm).symm ▸ p.start_mem_support)
      rw [hEq] at hxq
      exact hxq
    · intro hxp
      exact ⟨.inl p, hq, hxp⟩
  rw [hV]
  exact p.support_countable.le_aleph0.trans C.capacity_infinite

/-- The moving closing set, interval row and endpoint assignment are all
constructed here. The only path input is the genuine captured safe choice. -/
theorem IsBlueprint.exists_ordinaryExtension_of_capturedPath
    {W : Set (web C).DPath} (hW : IsBlueprint C C.newStage W)
    {z : V} (hzFrontier : z ∈ C.newSlice) (hz : z ∈ (web C).terminalFrontier W)
    (P : SafeCurrentStageTargetPath C z)
    (hP : Gamma.vertexSet P.ambientFamily ⊆ C.ladder.limitRoof)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph) :
    ∃ (b : Stage (succ kappa)) (Q : Set (web C).DPath),
      b ∈ C.club ∧ C.newStage < b ∧ IsBlueprint C b Q ∧
      (web C).vertexSet W ⊆ (web C).vertexSet Q ∧
      familyEdges W ⊆ familyEdges Q ∧
      (web C).initialSet W ⊆ (web C).initialSet Q ∧
      (web C).terminalFrontier Q ⊆ popular C ∧
      (web C).terminalFrontier Q ∩ C.ladder.frontier b ⊆ C.persistent ∧
      RealReaches Gamma (web C) Q z Gamma.target ∧
      (∀ x, x ∈ (web C).terminalFrontier W → x ≠ z →
        (x ∉ C.newSlice ∨ x ∈ C.persistent) → x ∈ (web C).terminalFrontier Q) ∧
      (∀ {x y}, y ∈ (web C).vertexSet W → (x, y) ∈ familyEdges Q →
        (x, y) ∈ familyEdges W) := by
  let seed := (web C).vertexSet W ∪ Gamma.vertexSet P.ambientFamily
  have hcard : #seed ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      hW.card_vertices (safePath_card_vertices P))
  have hroof : seed ⊆ C.ladder.limitRoof := Set.union_subset hW.vertices_working hP
  obtain ⟨R, T, F, ⟨A⟩⟩ := exists_endpointClosedIntervalAssignment C P
    (show Gamma.vertexSet P.ambientFamily ⊆ seed from Set.subset_union_right)
    hcard hroof hzFrontier hext hsub
  obtain ⟨Q, hQ, hE, _hV, _hI, hkeepV, hkeepE, hkeepI, _hQX, hPop,
      hStable, hReach, hFresh⟩ := A.exists_targetBlueprint hW
        (show (web C).vertexSet W ⊆ seed from Set.subset_union_left) R.endpoint_closed hz
  exact ⟨R.later.stage, Q, R.later.mem_club, R.later.current_lt,
    hQ, hkeepV, hkeepE, hkeepI, hPop, hStable, hReach,
    fun _ hx hxz hb ↦ A.old_terminal_retained hW
      (Set.subset_union_left.trans R.seed_subset) hQ.isWarp hkeepV hE hx hxz hb,
    hFresh⟩

#print axioms safePath_card_vertices
#print axioms IsBlueprint.exists_ordinaryExtension_of_capturedPath

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
