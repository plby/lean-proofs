/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularHalfwaySplit
import ErdosProblems.Erdos599.RegularJointSafeReplacement

/-!
# Restoring a full-source safe residual batch

`ProtectedBatch` is convenient when a reserve is known before the lower
half-way construction, but its altitude parameter makes finite current
request sets awkward.  `FullSourceSafeBatch` is the sound common output for
both the half-way and the small-source extension branches.  Since its row
covers the whole residual source, a reserve can be selected afterwards.

This file restricts such a full row back to the exact current request
coordinates before ambient restoration.  Consequently the restored family
is source-star compatible with the old pending row, while the quotient of
the *full* residual row remains the iterable next state.  No comparison of
deletion and quotient is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularFullSourceSafeReplacement

open SingularContinuation SingularExtension SingularPendingDecomposition
  SingularPendingReentry SingularProtectedRestoration SingularSafeBatch
  SingularProtectedBatchTransport SingularTargetRowMachine SliceSpliceSource

universe u

variable {V : Type u}

/-- The sound ambient restoration of a full-source safe residual batch.
Only the current-coordinate restriction is installed in the ambient row;
the entire batch supplies the next unhindered residual quotient and the
lossless reserve-frontier coordinate change. -/
structure FullSourceSafeReplacement
    (G : DWeb V) {row : Set G.DPath}
    (F : RegularJointSafeReplacement.ProtectedRestorationFrame G row)
    (B : FullSourceSafeBatch F.state.web F.state.requests)
    (reserve : Set V) where
  paths : Set G.DPath
  continuedPaths : Set G.DPath
  paths_eq : paths = F.frozen ∪ continuedPaths
  frozen_preserved : F.frozen ⊆ paths
  pendingForward : G.ForwardExtension
    (pendingPart G F.selectedRow) continuedPaths
  isWarp : G.IsWarp paths
  finiteCharacter : G.HasFiniteCharacter paths
  forward : G.ForwardExtension row paths
  initialSet : G.initialSet paths = G.initialSet row
  cross_disjoint : Disjoint (G.vertexSet F.frozen)
    (G.vertexSet continuedPaths)
  selected_completed : LinksToTarget G (completedPart G paths)
    (G.initialSet (pendingPart G F.selectedRow))
  terminalFrontier : G.terminalFrontier paths ⊆
    G.terminalFrontier row ∪ B.boundary
  nextState : RegularJointSafeReplacement.ProtectedResidualState V :=
    { web := F.state.web.quotient B.boundary
      requests := B.reserveFrontier reserve
      requests_source := B.reserveFrontier_subset_quotientSource reserve
      unhindered := B.quotient_unhindered }
  nextRequests_card : #nextState.requests = #reserve

/-- Restrict a full-source safe residual row to the current coordinates,
transport it through the genuine deletion--quotient frame, and source-star
it onto the old pending row.  This is the finite-request-safe counterpart of
`ProtectedRestorationFrame.extend`. -/
theorem exists_fullSourceSafeReplacement
    {G : DWeb V} (hNorm : G.IsNormalized) {row : Set G.DPath}
    (F : RegularJointSafeReplacement.ProtectedRestorationFrame G row)
    (B : FullSourceSafeBatch F.state.web F.state.requests)
    {reserve : Set V} (hreserve : reserve ⊆ F.state.web.source) :
    Nonempty (FullSourceSafeReplacement G F B reserve) := by
  let P := pendingPart G F.selectedRow
  let U := initialRestriction F.state.web B.paths F.state.requests
  let R := deletedQuotientFamily G F.split.boundary F.protectedSet U
  have hPtrivial : ∀ p ∈ boundaryPendingPart G F.selectedRow
      F.split.boundary, p = G.trivialPath p.initial := by
    exact boundaryPendingPart_trivial_mono G F.selected_subset
      F.split.boundary_pending_trivial
  have hrequestFront : F.state.requests = G.terminalFrontier P := by
    exact pendingRequests_eq_terminalFrontier_pendingPart_of_trivial_selected
      F.selected_source hPtrivial
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact F.row_warp (F.selected_subset hp.1)
      (F.selected_subset hq.1) hpq
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact F.row_finite (F.selected_subset hp.1)
  have hFwarp : G.IsWarp F.frozen := by
    intro p hp q hq hpq
    exact F.row_warp (F.frozen_subset hp) (F.frozen_subset hq) hpq
  have hFfinite : G.HasFiniteCharacter F.frozen := by
    intro p hp
    exact F.row_finite (F.frozen_subset hp)
  have hProof : G.vertexSet P ⊆ G.roof F.split.boundary :=
    pendingPart_selected_vertexSet_subset_roof_of_split F.split
      F.selected_subset F.selected_source
        F.split.boundary_pending_trivial
  have hFPvertex : Disjoint (G.vertexSet F.frozen) (G.vertexSet P) := by
    apply Set.disjoint_left.2
    intro x hxF hxP
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqP, hxq⟩ := hxP
    have hpq : p ≠ q := by
      intro heq
      subst q
      exact Set.disjoint_left.1 F.family_disjoint hpF hqP
    exact Set.disjoint_left.1
      (F.row_warp (F.frozen_subset hpF)
        (F.selected_subset hqP.1) hpq) hxp hxq
  have hB : IsLinkageBetween F.state.web F.state.web.source
      B.boundary B.paths := B.separating.linkage
  have hU : IsLinkageBetween F.state.web F.state.requests B.boundary U :=
    isLinkageBetween_initialRestriction hB F.state.requests_source
  have hUlinks : LinksToTarget F.state.web U F.state.requests :=
    RegularHalfwaySplit.linksToTarget_initialRestriction hB
      F.state.requests_source B.links
  have hRwarp : (G.quotient F.split.boundary).IsWarp R :=
    deletedQuotientFamily_isWarp hU.isWarp
  have hRfinite : (G.quotient F.split.boundary).HasFiniteCharacter R :=
    deletedQuotientFamily_hasFiniteCharacter hU.finiteCharacter
  have hRinitialRequest :
      (G.quotient F.split.boundary).initialSet R = F.state.requests := by
    exact (deletedQuotientFamily_initialSet G F.split.boundary
      F.protectedSet U).trans hU.initialSet_eq
  have hRlinksRequest : LinksToTarget (G.quotient F.split.boundary) R
      F.state.requests :=
    linksToTarget_deletedQuotientFamily hUlinks
  have hRinitial : (G.quotient F.split.boundary).initialSet R =
      G.terminalFrontier P := hRinitialRequest.trans hrequestFront
  have hRlinks : LinksToTarget (G.quotient F.split.boundary) R
      (G.terminalFrontier P) := by
    simpa only [hrequestFront] using hRlinksRequest
  have hUstart : F.state.web.initialSet U ⊆ F.state.web.source := by
    rw [hU.initialSet_eq]
    exact F.state.requests_source
  have hcross : Disjoint (G.vertexSet F.frozen)
      (G.vertexSet (frontierContinuation G hPwarp hProof F.split.minimal
        R hRinitial.le)) := by
    exact disjoint_frozen_frontierContinuation_deletedQuotientFamily
      G hFPvertex F.frozen_protected hPwarp hProof F.split.minimal
        hUstart hRinitial.le
  let T := frozenFrontierContinuation G F.frozen hPwarp hProof
    F.split.minimal R hRinitial.le
  let L := frontierContinuation G hPwarp hProof F.split.minimal
    R hRinitial.le
  have hstruct := frozenFrontierContinuation_structural G
    hFwarp hPwarp hFfinite hPfinite hProof F.split.minimal
      hRwarp hRfinite hRinitial hcross
  have hPsource : G.initialSet P ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact F.selected_source ⟨p, hp.1, hpx⟩
  have hRambientLinks : LinksToTarget G
      (frontierContinuation G hPwarp hProof F.split.minimal
        R hRinitial.le) (G.initialSet P) :=
    linksToTarget_frontierContinuation hNorm hPwarp hPfinite hProof
      F.split.minimal hRwarp hRfinite hRinitial Set.Subset.rfl
        hPsource (routesTerminals_initialSet_terminalFrontier hPfinite)
          hRlinks
  have hTlinks : LinksToTarget G T (G.initialSet P) := by
    intro b hb
    obtain ⟨p, hp, hrest⟩ := hRambientLinks b hb
    exact ⟨p, Or.inr hp, hrest⟩
  have hTcompleted : LinksToTarget G (completedPart G T)
      (G.initialSet P) := linksToTarget_completedPart hNorm hTlinks
  have hRterminal : (G.quotient F.split.boundary).terminalFrontier R ⊆
      B.boundary := by
    exact (deletedQuotientFamily_terminalFrontier G F.split.boundary
      F.protectedSet U).le.trans hU.terminalFrontier_subset
  have hTterminal : G.terminalFrontier T ⊆
      G.terminalFrontier row ∪ B.boundary := by
    intro x hx
    have hx' := terminalFrontier_frozenFrontierContinuation_subset
      G hPwarp hPfinite hProof F.split.minimal hRinitial.le
        hRinitial.ge hx
    rcases hx' with hxF | hxR
    · exact Or.inl ⟨hxF.choose, F.frozen_subset hxF.choose_spec.1,
        hxF.choose_spec.2⟩
    · exact Or.inr (hRterminal hxR)
  let nextState : RegularJointSafeReplacement.ProtectedResidualState V :=
    { web := F.state.web.quotient B.boundary
      requests := B.reserveFrontier reserve
      requests_source := B.reserveFrontier_subset_quotientSource reserve
      unhindered := B.quotient_unhindered }
  refine ⟨
    { paths := T
      continuedPaths := L
      paths_eq := rfl
      frozen_preserved := Set.subset_union_left
      pendingForward := forwardExtension_frontierContinuation G hPwarp
        hProof F.split.minimal R hRinitial.le
      isWarp := hstruct.1
      finiteCharacter := hstruct.2.1
      forward := ?_
      initialSet := ?_
      cross_disjoint := hcross
      selected_completed := hTcompleted
      terminalFrontier := hTterminal
      nextState := nextState
      nextRequests_card := ?_ }⟩
  · rw [← F.decomposition]
    exact hstruct.2.2.1
  · rw [hstruct.2.2.2, F.decomposition]
  · exact B.mk_reserveFrontier_eq hreserve

/-- Unconditional lower-cardinal constructor for a framed successor.  The
scale `max (#requests) aleph0` handles finite request sets, and the
full-source safe-batch dichotomy handles the case in which the residual
source itself is smaller than that scale.  The reserve is selected only
after the full residual row has been built. -/
theorem exists_fullSourceSafeReplacement_of_lower
    {kappa : Cardinal.{u}} (G : DWeb V) (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) {row : Set G.DPath}
    (F : RegularJointSafeReplacement.ProtectedRestorationFrame G row)
    (hrequestsSmall : #(F.state.requests) < kappa)
    {reserve : Set V} (hreserve : reserve ⊆ F.state.web.source) :
    ∃ B : FullSourceSafeBatch F.state.web F.state.requests,
      Nonempty (FullSourceSafeReplacement G F B reserve) := by
  let rho : Cardinal.{u} := max (#(F.state.requests)) aleph0
  have hrhoKappa : rho < kappa :=
    max_lt_iff.mpr ⟨hrequestsSmall, hkappa⟩
  have hrhoInfinite : aleph0 ≤ rho := le_max_right _ _
  have hrequestCard : #(F.state.requests) ≤ rho := le_max_left _ _
  have hNoEnterG : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hNoEnterState : F.state.web.NoEdgeEnters F.state.web.source := by
    exact DWeb.NoEdgeEnters.quotient (G.delete F.protectedSet)
      hNoEnterG.delete
  obtain ⟨B⟩ := exists_fullSourceSafeBatch_of_lower hlower
    hrhoKappa hrhoInfinite F.state.web F.state.unhindered
      hNoEnterState F.state.requests_source hrequestCard
  exact ⟨B, exists_fullSourceSafeReplacement hNorm F B hreserve⟩

/-- Extend the presently available (structural) restoration-tower fields
using a full-source safe batch.  Old completed components remain literal,
all current pending coordinates become completed, and the arbitrary reserve
is carried losslessly into an honest next residual state.

This theorem deliberately does **not** construct a new ambient
`ProtectedRestorationFrame` for that residual.  In particular it is not, by
itself, an iterable provider: the current `ProtectedRestorationTower` API
does not contain a path-transport map from its stored residual web back to
`G`.  A caller must supply that additional compositional restoration datum
before applying another ambient step. -/
theorem exists_towerExtension_of_lower
    {kappa : Cardinal.{u}} {G : DWeb V} (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa)
    {baseRow row : Set G.DPath} {completed : Set V}
    (F : RegularJointSafeReplacement.ProtectedRestorationFrame G row)
    (T : RegularJointSafeReplacement.ProtectedRestorationTower G
      baseRow F.state row completed)
    (hrequestsSmall : #(F.state.requests) < kappa)
    {reserve : Set V} (hreserve : reserve ⊆ F.state.web.source) :
    ∃ (B : FullSourceSafeBatch F.state.web F.state.requests)
        (J : FullSourceSafeReplacement G F B reserve),
      RegularJointSafeReplacement.ProtectedRestorationTower G baseRow
        J.nextState J.paths
        (completed ∪ G.initialSet (pendingPart G F.selectedRow)) := by
  obtain ⟨B, ⟨J⟩⟩ := exists_fullSourceSafeReplacement_of_lower
    G hNorm hlower hkappa F hrequestsSmall hreserve
  have hOld : LinksToTarget G (completedPart G J.paths) completed := by
    intro a ha
    obtain ⟨p, hpOld, q, hpq, hpure, hsuffix⟩ :=
      T.completed_links a ha
    have hpFrozen : p ∈ F.frozen := F.completed_frozen hpOld
    have hpNew : p ∈ J.paths := J.frozen_preserved hpFrozen
    exact ⟨p, ⟨hpNew, hpOld.2⟩, q, hpq, hpure, hsuffix⟩
  have hSelectedSource : G.initialSet (pendingPart G F.selectedRow) ⊆
      G.source := by
    rintro a ⟨p, hp, rfl⟩
    apply F.selected_source
    exact ⟨p, hp.1, rfl⟩
  have hAll : LinksToTarget G (completedPart G J.paths)
      (completed ∪ G.initialSet (pendingPart G F.selectedRow)) := by
    exact SingularSelectedFreeze.linksToTarget_union_of_normalized hNorm
      T.completed_source hSelectedSource hOld J.selected_completed
  refine ⟨B, J, ?_⟩
  exact
    { row_warp := J.isWarp
      row_finite := J.finiteCharacter
      initialSet_eq := J.initialSet.trans T.initialSet_eq
      forward := G.forwardExtension_trans T.forward J.forward
      completed_source := Set.union_subset T.completed_source hSelectedSource
      completed_links := hAll }

end RegularFullSourceSafeReplacement
end CardinalInduction
end Erdos599
