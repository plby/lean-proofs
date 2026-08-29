/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedBatchTransport

/-!
# Restoring a protected singular batch around a frozen carrier

An arbitrary family completed in a deleted quotient does not preserve
unhinderedness after its carrier is added to the deleted set.  The iterable
replacement is a protected batch: the same lower-cardinal invocation carries
the requests completed now and a reserve for the following invocation.

This file proves the restoration part of that construction.  The current
members of a protected batch are restricted by their initial coordinate,
transported from `(G - Q) / C` to `G / C`, and source-starred onto the old
pending family.  The frozen family is restored verbatim.  At the same time,
the protected batch retains the separating stop-over, unhindered quotient,
and exact reserve-frontier cardinal used by the next transition.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProtectedRestoration

open SingularContinuation SingularExtension SingularPendingDecomposition
  SingularPendingReentry SingularSafeBatch SingularProtectedBatchTransport
  SingularTargetRowMachine SliceSpliceSource

universe u

variable {V : Type u}

/-- The members of a protected batch whose initial coordinate is current. -/
def currentPart
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) : Set H.DPath :=
  initialRestriction H (forgetProtectedBatchFamily B) current

@[simp] theorem mem_currentPart
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    {B : ProtectedBatch H current reserve mu} {p : H.DPath} :
    p ∈ currentPart B ↔
      p ∈ forgetProtectedBatchFamily B ∧ p.initial ∈ current :=
  Iff.rfl

/-- Forgetting the protected distinguished source turns its stop-over
linkage into a linkage with the explicit source set `current ∪ reserve` in
the underlying web. -/
theorem protectedBatch_isLinkageBetween
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) :
    IsLinkageBetween H (current ∪ reserve) B.boundary
      (forgetProtectedBatchFamily B) :=
  B.separating.linkage

/-- Restriction to the current initial coordinates retains a genuine
linkage, hence in particular warpness, finite character, and the exact
current initial set. -/
theorem currentPart_isLinkageBetween
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) :
    IsLinkageBetween H current B.boundary (currentPart B) := by
  exact isLinkageBetween_initialRestriction
    (protectedBatch_isLinkageBetween B) Set.subset_union_left

/-- Target links for the current requests belong to the current-coordinate
restriction.  The only point requiring proof is membership: endpoint purity
of the full protected linkage forces any member containing a current source
to start at that source. -/
theorem currentPart_linksToTarget
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) :
    LinksToTarget H (currentPart B) current := by
  intro a ha
  obtain ⟨p, hpB, q, rfl, hqCurrent, hsuffix⟩ := B.links_current a ha
  have haSupport : a ∈ q.support := by
    have haInter : a ∈ q.support ∩ current := by
      rw [hqCurrent]
      exact Set.mem_singleton a
    exact haInter.1
  have hpEnds := (protectedBatch_isLinkageBetween B).2.2.2.2
    (Sum.inl q) hpB
  obtain ⟨q', hqq', _hends, hsource⟩ := hpEnds
  have hq'eq : q' = q := by
    exact Sum.inl.inj hqq'.symm
  subst q'
  have haUnion : a ∈ current ∪ reserve := Or.inl ha
  have haStart : a = q.start := by
    have haInter : a ∈ q.support ∩ (current ∪ reserve) :=
      ⟨haSupport, haUnion⟩
    have haSingleton : a ∈ ({q.start} : Set V) :=
      (Set.ext_iff.mp hsource a).mp haInter
    exact Set.mem_singleton_iff.mp haSingleton
  have hqInitialCurrent :
      DirectedPath.Path.initial (Sum.inl q : H.DPath) ∈ current := by
    change q.start ∈ current
    exact haStart ▸ ha
  refine ⟨Sum.inl q, ⟨hpB, hqInitialCurrent⟩, q, rfl,
    hqCurrent, hsuffix⟩

/-- Transporting the current-coordinate part of a deleted protected batch
to the ordinary quotient preserves exactly the data consumed by the
frontier source-star.  Its ambient lift still avoids the frozen carrier. -/
theorem currentPart_deletedQuotientPayload
    {G : DWeb V} {C Q current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch ((G.delete Q).quotient C) current reserve mu)
    (hcurrent : current ⊆ ((G.delete Q).quotient C).source) :
    let U := currentPart B
    let R := deletedQuotientFamily G C Q U
    (G.quotient C).IsWarp R ∧
      (G.quotient C).HasFiniteCharacter R ∧
      (G.quotient C).initialSet R = current ∧
      LinksToTarget (G.quotient C) R current ∧
      Disjoint (G.vertexSet (liftedQuotientFamily G C R)) Q := by
  dsimp only
  have hU := currentPart_isLinkageBetween B
  have hstart : ((G.delete Q).quotient C).initialSet (currentPart B) ⊆
      ((G.delete Q).quotient C).source := by
    rw [hU.initialSet_eq]
    exact hcurrent
  refine ⟨deletedQuotientFamily_isWarp hU.isWarp,
    deletedQuotientFamily_hasFiniteCharacter hU.finiteCharacter,
    ?_, linksToTarget_deletedQuotientFamily (currentPart_linksToTarget B),
    lift_deletedQuotientFamily_vertexSet_disjoint hstart⟩
  rw [deletedQuotientFamily_initialSet]
  exact hU.initialSet_eq

/-- Structure-valued output of one protected deletion/restoration step.
The first six fields are the restored ambient row.  The final three fields
are the non-circular next-state invariant: a separating protected stop-over,
its unhindered quotient, and the exact reserve-frontier cardinal. -/
structure RestoredProtectedStep
    (G : DWeb V) (old frozen pending : Set G.DPath) (linked : Set V)
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) where
  paths : Set G.DPath
  continuedPaths : Set G.DPath
  paths_eq : paths = frozen ∪ continuedPaths
  frozen_preserved : frozen ⊆ paths
  pendingForward : G.ForwardExtension pending continuedPaths
  isWarp : G.IsWarp paths
  finiteCharacter : G.HasFiniteCharacter paths
  forward : G.ForwardExtension old paths
  initialSet : G.initialSet paths = G.initialSet old
  links : LinksToTarget G paths linked
  terminalFrontier : G.terminalFrontier paths ⊆
    G.terminalFrontier old ∪ B.boundary
  protectedSeparating : IsSeparatingHalfwayStopover
    (protectedRequestWeb H current reserve) B.paths B.boundary :=
    B.separating
  nextResidualUnhindered :
    ((protectedRequestWeb H current reserve).quotient
      B.boundary).IsUnhindered := B.quotient_unhindered
  nextRequests : Set V := B.reserveFrontier
  nextRequests_source : nextRequests ⊆
    ((protectedRequestWeb H current reserve).quotient
      B.boundary).source := by
    simpa only [nextRequests] using B.reserveFrontier_subset_quotientSource
  nextRequests_card : #nextRequests = #reserve := by
    simpa only [nextRequests] using B.mk_reserveFrontier_eq

/-- Restore the current part of a protected residual batch around the frozen
family.  This is the positive two-track restoration theorem: `old` advances
in the ambient web, while `B.reserveFrontier` advances in the protected
residual quotient.  No claim is made that deleting the newly completed
ambient paths preserves unhinderedness; the protected quotient field is the
iterable replacement for that false implication. -/
theorem restoreProtectedCurrent
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (pendingPart G W₁))
    (hWwarp : G.IsWarp W₂)
    (hWfinite : G.HasFiniteCharacter W₂)
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q reserve : Set V} {mu : Cardinal.{u}}
    (hFQ : G.vertexSet F ⊆ Q)
    (hcurrent : pendingRequests G W₁ S.boundary ⊆
      ((G.delete Q).quotient S.boundary).source)
    (B : ProtectedBatch ((G.delete Q).quotient S.boundary)
      (pendingRequests G W₁ S.boundary) reserve mu) :
    Nonempty (RestoredProtectedStep G W₂ F (pendingPart G W₁)
      (G.initialSet (pendingPart G W₁)) B) := by
  let P := pendingPart G W₁
  let U := currentPart B
  let R := deletedQuotientFamily G S.boundary Q U
  have hPtrivial : ∀ p ∈ boundaryPendingPart G W₁ S.boundary,
      p = G.trivialPath p.initial :=
    boundaryPendingPart_trivial_mono G hsub S.boundary_pending_trivial
  have hrequestFront : pendingRequests G W₁ S.boundary =
      G.terminalFrontier P :=
    pendingRequests_eq_terminalFrontier_pendingPart_of_trivial_selected
      hsource hPtrivial
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact hWwarp (hsub hp.1) (hsub hq.1) hpq
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hWfinite (hsub hp.1)
  have hFwarp : G.IsWarp F := by
    intro p hp q hq hpq
    exact hWwarp (hFsub hp) (hFsub hq) hpq
  have hFfinite : G.HasFiniteCharacter F := by
    intro p hp
    exact hWfinite (hFsub hp)
  have hProof : G.vertexSet P ⊆ G.roof S.boundary :=
    pendingPart_selected_vertexSet_subset_roof_of_split
      S hsub hsource S.boundary_pending_trivial
  have hFPvertex : Disjoint (G.vertexSet F) (G.vertexSet P) := by
    apply Set.disjoint_left.2
    intro x hxF hxP
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqP, hxq⟩ := hxP
    have hpq : p ≠ q := by
      intro heq
      subst q
      exact Set.disjoint_left.1 hfamilyDisjoint hpF hqP
    exact Set.disjoint_left.1
      (hWwarp (hFsub hpF) (hsub hqP.1) hpq) hxp hxq
  obtain ⟨hRwarp, hRfinite, hRinitialRequest, hRlinksRequest, _hRQ⟩ :=
    currentPart_deletedQuotientPayload B hcurrent
  have hRinitial : (G.quotient S.boundary).initialSet R =
      G.terminalFrontier P := hRinitialRequest.trans hrequestFront
  have hRlinks : LinksToTarget (G.quotient S.boundary) R
      (G.terminalFrontier P) := by
    simpa only [hrequestFront] using hRlinksRequest
  have hUinitial : ((G.delete Q).quotient S.boundary).initialSet U =
      pendingRequests G W₁ S.boundary := by
    exact (currentPart_isLinkageBetween B).initialSet_eq
  have hUstart : ((G.delete Q).quotient S.boundary).initialSet U ⊆
      ((G.delete Q).quotient S.boundary).source := by
    rw [hUinitial]
    exact hcurrent
  have hcross : Disjoint (G.vertexSet F)
      (G.vertexSet (frontierContinuation G hPwarp hProof S.minimal
        R hRinitial.le)) :=
    disjoint_frozen_frontierContinuation_deletedQuotientFamily
      G hFPvertex hFQ hPwarp hProof S.minimal hUstart hRinitial.le
  let T := frozenFrontierContinuation G F hPwarp hProof S.minimal
    R hRinitial.le
  let L := frontierContinuation G hPwarp hProof S.minimal R hRinitial.le
  have hstruct := frozenFrontierContinuation_structural G
    hFwarp hPwarp hFfinite hPfinite hProof S.minimal
      hRwarp hRfinite hRinitial hcross
  have hPsource : G.initialSet P ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact hsource ⟨p, hp.1, hpx⟩
  have hRambientLinks : LinksToTarget G
      (frontierContinuation G hPwarp hProof S.minimal R hRinitial.le)
      (G.initialSet P) :=
    linksToTarget_frontierContinuation hNorm hPwarp hPfinite hProof
      S.minimal hRwarp hRfinite hRinitial Set.Subset.rfl hPsource
      (routesTerminals_initialSet_terminalFrontier hPfinite) hRlinks
  have hTlinks : LinksToTarget G T (G.initialSet P) := by
    intro b hb
    obtain ⟨p, hp, hrest⟩ := hRambientLinks b hb
    exact ⟨p, Or.inr hp, hrest⟩
  have hRterminal : (G.quotient S.boundary).terminalFrontier R ⊆
      B.boundary := by
    rw [deletedQuotientFamily_terminalFrontier]
    exact (currentPart_isLinkageBetween B).terminalFrontier_subset
  have hTterminal : G.terminalFrontier T ⊆
      G.terminalFrontier W₂ ∪ B.boundary := by
    intro x hx
    have hx' := terminalFrontier_frozenFrontierContinuation_subset
      G hPwarp hPfinite hProof S.minimal hRinitial.le hRinitial.ge hx
    rcases hx' with hxF | hxR
    · exact Or.inl ⟨hxF.choose, hFsub hxF.choose_spec.1,
        hxF.choose_spec.2⟩
    · exact Or.inr (hRterminal hxR)
  refine ⟨
    { paths := T
      continuedPaths := L
      paths_eq := rfl
      frozen_preserved := Set.subset_union_left
      pendingForward := forwardExtension_frontierContinuation G hPwarp
        hProof S.minimal R hRinitial.le
      isWarp := hstruct.1
      finiteCharacter := hstruct.2.1
      forward := ?_
      initialSet := ?_
      links := hTlinks
      terminalFrontier := hTterminal
      protectedSeparating := B.separating
      nextResidualUnhindered := B.quotient_unhindered
      nextRequests := B.reserveFrontier
      nextRequests_source := B.reserveFrontier_subset_quotientSource
      nextRequests_card := B.mk_reserveFrontier_eq }⟩
  · rw [← hdecomp]
    exact hstruct.2.2.1
  · rw [hstruct.2.2.2, hdecomp]


end SingularProtectedRestoration
end CardinalInduction
end Erdos599
