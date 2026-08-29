/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularBetaSelection
import ErdosProblems.Erdos599.RegularCompletedPendingSplice

/-!
# Splitting a regular half-way row into completed and clean tracks

The half-way row used in Assertion 9.10 need not meet its stop-over only at
its terminal: a requested source can already belong to the stop-over.  It is
therefore unsound to use the same row both as the target-linking row and as
the clean input to the restricted-web construction.

This file performs the source-exact split.  Components whose initial vertex
is requested are retained verbatim as the target track.  Every other
component is cut at its first visit to the stop-over and becomes the clean
track.  The two tracks are still jointly a warp because their parent
components belonged to the original linkage.  No avoidance assumption on
the requested sources is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularHalfwaySplit

open DirectedPath
open SliceSpliceSource

universe u

variable {V : Type u}

/-- Target links witnessed by a full-source linkage remain witnessed after
restricting the linkage to the components rooted in the designated source
set. -/
theorem linksToTarget_initialRestriction
    {Q : DWeb V} {C U : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q W U) :
    LinksToTarget Q (initialRestriction Q W U) U := by
  intro a haU
  obtain ⟨p, hpW, f, hpf, hpure, hsuffix⟩ := hlinks a haU
  have haSupport : a ∈ f.support := by
    have haInter : a ∈ f.support ∩ U := by
      rw [hpure]
      exact Set.mem_singleton a
    exact haInter.1
  obtain ⟨g, hpg, _hends, hgSource⟩ := hW.endpointPure p hpW
  have hgf : g = f := by
    apply Sum.inl.inj
    exact hpg.symm.trans hpf
  subst g
  have haStart : a = f.start := by
    have haSource : a ∈ f.support ∩ Q.source :=
      ⟨haSupport, hUsource haU⟩
    rw [hgSource] at haSource
    exact Set.mem_singleton_iff.mp haSource
  refine ⟨p, ⟨hpW, ?_⟩, f, hpf, hpure, hsuffix⟩
  rw [hpf]
  change f.start ∈ U
  simpa only [haStart] using haU

/-- The target and clean first-hit tracks are cross-disjoint.  Clean paths
are prefixes of unrequested parent components, while target paths are the
distinct requested parent components. -/
theorem disjoint_target_cleanFirstHit
    {Q : DWeb V} {C U : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W) :
    Disjoint
      (Q.vertexSet (initialRestriction Q W U))
      (Q.vertexSet
        (RegularBetaSelection.targetFirstHitFamily
          (isLinkageBetween_initialRestriction
            (A' := Q.source \ U) hW Set.sdiff_subset))) := by
  let P := initialRestriction Q W (Q.source \ U)
  let hP : IsLinkageBetween Q (Q.source \ U) C P :=
    isLinkageBetween_initialRestriction hW Set.sdiff_subset
  let F := RegularBetaSelection.targetFirstHitFamily hP
  have hforward : Q.ForwardExtension F P :=
    RegularBetaSelection.targetFirstHitFamily_forwardExtension hP
  apply Set.disjoint_left.2
  intro x hxTarget hxClean
  obtain ⟨p, hpTarget, hxp⟩ := hxTarget
  obtain ⟨q, hqClean, hxq⟩ := hxClean
  obtain ⟨r, hrP, hqr⟩ := hforward.1 q hqClean
  have hpr : p ≠ r := by
    intro hpr
    subst r
    exact hrP.2.2 hpTarget.2
  exact Set.disjoint_left.1
    (hW.isWarp hpTarget.1 hrP.1 hpr) hxp
      (Q.support_mono_of_extends hqr hxq)

/-- Every selected component has already reached the ambient target.  The
target link for its initial vertex must use that same component, by
disjointness of the original linkage. -/
theorem initialRestriction_subset_completedPart
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    {C U : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q W U) :
    initialRestriction Q W U ⊆ SingularExtension.completedPart Q W := by
  intro p hp
  let a := p.initial
  have haU : a ∈ U := hp.2
  obtain ⟨q, hqW, f, hqf, hpure, hsuffix⟩ := hlinks a haU
  have haSupport : a ∈ f.support := by
    have haInter : a ∈ f.support ∩ U := by
      rw [hpure]
      exact Set.mem_singleton a
    exact haInter.1
  have hfStart : f.start = a := by
    exact (hNorm.eq_initial_of_mem_path (Sum.inl f) haSupport
      (hUsource haU)).symm
  have hpq : p = (Sum.inl f : Q.DPath) := by
    have hsameInitial : p.initial =
        DirectedPath.Path.initial (Sum.inl f : Q.DPath) := by
      change a = f.start
      exact hfStart.symm
    exact DWeb.IsWarp.eq_of_initial_eq Q hW.isWarp hp.1
      (hqf ▸ hqW) hsameInitial
  obtain ⟨before, after, hsupport, b, hbTarget, hbAfter⟩ := hsuffix
  have hbSupport : b ∈ f.support := by
    change b ∈ f.walk.support
    rw [hsupport]
    exact List.mem_append_right before hbAfter
  have hterminal : Q.terminal? (Sum.inl f : Q.DPath) = some b :=
    hNorm.terminal?_eq_of_mem_path (Sum.inl f) hbSupport hbTarget
  exact ⟨hp.1, b, hbTarget, hpq.symm ▸ hterminal⟩

/-- The exact source split consumed by a completed/pending regular splice.
The target track is allowed to revisit `C`; the clean track is not. -/
theorem exists_cleanTargetSlice_of_halfway
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    {C U : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q W U) :
    ∃ S : RegularCompletedPendingSplice.CleanTargetSlice
        Q Q.source C U,
      S.target = initialRestriction Q W U ∧
      S.clean = RegularBetaSelection.targetFirstHitFamily
        (isLinkageBetween_initialRestriction
          (A' := Q.source \ U) hW Set.sdiff_subset) ∧
      #(S.target) ≤ #U ∧
      S.target ⊆ SingularExtension.completedPart Q W := by
  let T := initialRestriction Q W U
  let P := initialRestriction Q W (Q.source \ U)
  let hT : IsLinkageBetween Q U C T :=
    isLinkageBetween_initialRestriction hW hUsource
  let hP : IsLinkageBetween Q (Q.source \ U) C P :=
    isLinkageBetween_initialRestriction hW Set.sdiff_subset
  let F := RegularBetaSelection.targetFirstHitFamily hP
  have hF : IsLinkageBetween Q (Q.source \ U) C F :=
    RegularBetaSelection.targetFirstHitFamily_isLinkageBetween hP
  have hTF : Disjoint (Q.vertexSet T) (Q.vertexSet F) := by
    exact disjoint_target_cleanFirstHit hW
  have hUnionWarp : Q.IsWarp (T ∪ F) := by
    apply SingularContinuation.isWarp_union_of_disjoint_vertexSet Q
    · exact hT.isWarp
    · exact hF.isWarp
    · exact hTF
  have hUnionFinite : Q.HasFiniteCharacter (T ∪ F) := by
    exact SingularContinuation.finiteCharacter_union Q
      hT.finiteCharacter hF.finiteCharacter
  have hSourcePure : ∀ p ∈ T ∪ F,
      p.support ∩ Q.source = {p.initial} := by
    intro p hp
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxSource⟩
      exact Set.mem_singleton_iff.mpr
        (hNorm.eq_initial_of_mem_path p hxp hxSource)
    · intro x hx
      have hxInitial : x = p.initial := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨p.initial_mem_support, ?_⟩
      rcases hp with hpT | hpF
      · exact hUsource <| by
          rw [← hT.initialSet_eq]
          exact ⟨p, hpT, rfl⟩
      · exact Set.sdiff_subset <| by
          rw [← hF.initialSet_eq]
          exact ⟨p, hpF, rfl⟩
  let S : RegularCompletedPendingSplice.CleanTargetSlice
      Q Q.source C U :=
    { target := T
      clean := F
      union_warp := hUnionWarp
      finiteCharacter := hUnionFinite
      target_initial := hT.initialSet_eq
      clean_initial := hF.initialSet_eq
      initial_cover := hUsource
      target_links := linksToTarget_initialRestriction hW hUsource hlinks
      clean_terminal := hF.terminalFrontier_subset
      clean_terminal_only :=
        RegularBetaSelection.targetFirstHitFamily_meetsOnlyAtTerminal hP
      source_pure := hSourcePure }
  refine ⟨S, rfl, rfl, ?_, ?_⟩
  · apply FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
    · exact hT.isWarp
    · intro p hp
      have hpInitial : p.initial ∈ U := by
        rw [← hT.initialSet_eq]
        exact ⟨p, hp, rfl⟩
      exact ⟨p.initial, hpInitial, p.initial_mem_support⟩
  · exact initialRestriction_subset_completedPart
      hNorm hW hUsource hlinks

end RegularHalfwaySplit
end CardinalInduction
end Erdos599
