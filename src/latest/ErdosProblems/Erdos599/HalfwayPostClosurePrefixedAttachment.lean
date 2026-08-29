/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureReferencePrefixSeed
import ErdosProblems.Erdos599.HalfwayPostClosureOldPriorityAttachment
import ErdosProblems.Erdos599.HalfwayPostClosureSourceCoverage

/-!
# Source-covered old-priority post-closure attachment

This is the concrete source half of the Assertion 9.31 assembler.  First add
the finite source prefixes of limiting-reference members activated by the
closed carrier.  Then attach the actual inside-plus-shortcut relation with
old outgoing edges taking priority.  Root-reachable restriction removes
orphan and rootless fresh components without losing the current blueprint or
the activated prefixes.

The result has the exact source-cover condition at the captured frontier.
Terminal accounting and the strong-edge condition remain independent.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Concrete source-covered output of the prefixed old-priority relation.
The edge set is recorded exactly as a root-reachable restriction because
unattached fresh components are intentionally discarded. -/
theorem exists_sourceCoveredOldPriorityBlueprint
    (M : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    ∃ A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa,
      current.OrdinaryExtends A ∧ A.OrdinaryExtends U ∧
      A.edgeSet = referencePrefixSeedEdges current Rlimit.closedSet ∧
      A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
        (activatedReferencePrefixes C current Rlimit.closedSet) ∧
      A.initialSet = referencePrefixSeedRoots current Rlimit.closedSet ∧
      U.edgeSet = RootReachableRelation.edges
        (M.oldPriorityAttachedEdges A) A.initialSet ∧
      U.vertexSet = RootReachableRelation.carrier
        (M.oldPriorityAttachedEdges A) A.initialSet ∧
      U.initialSet = A.initialSet ∧
      U.vertexSet ⊆ current.vertexSet ∪ Rlimit.closedSet ∧
      Gamma.source ⊆ U.initialSet ∪
        U.retainedReferenceInitials Rlimit.capturedGeometry.newSlice := by
  obtain ⟨A, hcurrentA, hAE, hAV, hAI⟩ :=
    referencePrefixSeed.exists_blueprint_exact
      (C := C) (current := current) (X := Rlimit.closedSet)
  have hAroof : A.vertexSet ⊆ Gamma.roof C.newSlice :=
    referencePrefixSeed.blueprint_vertices_roofed hcurrent hAV
  obtain ⟨U, hAU, hUE, hUV, hUI, _hUT⟩ :=
    exists_rootReachableBlueprint_extending A
      (M.oldPriorityAttachedEdges A) A.initialSet
      (M.oldPriorityAttachedEdges_subset_imaginaryGraph A)
      (M.oldPriorityAttachedEdges_biUnique_of_vertices_roofed A hAroof)
      (fun x hx ↦
        M.currentInitial_noIncoming_oldPriorityAttachedEdges_of_vertices_roofed
          A hAroof hx)
      (M.current_edgeSet_subset_oldPriorityAttachedEdges A)
      Set.Subset.rfl
  have hAcarrier : A.vertexSet ⊆
      current.vertexSet ∪ Rlimit.closedSet := by
    rw [hAV]
    exact Set.union_subset Set.subset_union_left
      (activatedReferencePrefixes.vertexSet_subset Rlimit.reference_closed
        |>.trans Set.subset_union_right)
  have hRootCarrier : A.initialSet ⊆
      current.vertexSet ∪ Rlimit.closedSet := by
    intro x hx
    exact hAcarrier (by
      obtain ⟨p, hp, hpInitial⟩ := hx
      exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩)
  have hEdgeCarrier : ∀ e ∈ M.oldPriorityAttachedEdges A,
      e.1 ∈ current.vertexSet ∪ Rlimit.closedSet ∧
        e.2 ∈ current.vertexSet ∪ Rlimit.closedSet := by
    intro e he
    rcases he with hold | hfresh
    · change e ∈ familyEdges
        (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths at hold
      have hend := familyEdges_subset_vertexSet_prod
        (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths hold
      exact ⟨hAcarrier hend.1, hAcarrier hend.2⟩
    · have hend := M.toPostClosureCompressorAssignment
        |>.actualPostClosureClosedEdges_endpoints_closed hfresh.1
      exact ⟨Or.inr hend.1, Or.inr hend.2⟩
  have hUcarrier : U.vertexSet ⊆
      current.vertexSet ∪ Rlimit.closedSet := by
    rw [hUV]
    exact RootReachableRelation.carrier_subset
      (M.oldPriorityAttachedEdges A) A.initialSet
      hRootCarrier hEdgeCarrier
  have holdInitial : current.initialSet ⊆ U.initialSet := by
    rw [hUI, hAI]
    exact Set.subset_union_left
  have hprefix : Gamma.initialSet
      (sourcePrefixOwners current C.newSlice Rlimit.closedSet) ∩
        Gamma.source ⊆ U.initialSet := by
    rintro x ⟨⟨p, hpOwner, hpInitial⟩, hxSource⟩
    have hpRemainder : p ∈ current.referenceRemainder C.newSlice :=
      ⟨hpOwner.1.1, hpOwner.2⟩
    have hpMeet : (p.support ∩ Rlimit.closedSet).Nonempty :=
      hpOwner.1.2.2
    have hxActivated : x ∈ Gamma.initialSet
        (activatedReferencePrefixes C current Rlimit.closedSet) :=
      activatedReferencePrefixes.initial_mem_of_referenceRemainder_meets
        Rlimit.reference_closed hpRemainder hpInitial hxSource hpMeet
    rw [hUI, hAI]
    exact Or.inr hxActivated
  have hsource := Rlimit.covers_source_of_prefix_initials
    current U hcurrent holdInitial hUcarrier hprefix
  exact ⟨A, U, hcurrentA, hAU, hAE, hAV, hAI,
    hUE, hUV, hUI, hUcarrier, hsource⟩

#print axioms exists_sourceCoveredOldPriorityBlueprint

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

