/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedRestoration
import ErdosProblems.Erdos599.SingularRoofedFrozenAvoidance

/-!
# Protected restoration with only completed boundary-start deletion

The generic protected restoration theorem puts the carrier of every frozen
component into the deleted set.  For a genuine full-source linkage to the
old separating boundary this is stronger than necessary.  A frozen component
whose initial vertex is outside the boundary is wholly roofed there, and a
lifted quotient continuation can meet the old roof only at its initial
vertex.  Warp disjointness then protects that component automatically.

This file assembles that observation with the protected lower-cardinal batch.
Only the carrier of *completed* frozen components whose initial vertex
already lies on the old boundary is required to be contained in the deleted
set.  Pending boundary-starting components are trivial and therefore roofed.
The result is the same concrete `RestoredProtectedStep` used by the row
machinery: the old row is forward-extended, the frozen family is retained
literally, the selected pending coordinates reach the target, and the
protected quotient is retained as the next unhindered residual.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularBoundaryProtectedRestoration

open SingularContinuation SingularExtension SingularPendingDecomposition
  SingularPendingReentry SingularProtectedRestoration SingularSafeBatch
  SingularProtectedBatchTransport SingularTargetRowMachine SliceSpliceSource
  SingularRoofedFrozenAvoidance

universe u

variable {V : Type u}

/-- Restore a protected residual batch while deleting only the frozen
completed components which start on the old boundary.  Boundary-starting
pending components are trivial and therefore roofed; the full-source linkage
field makes the outside-starting components automatically roofed as well. -/
theorem restoreProtectedCurrent_protect_boundaryStarts
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hWlink : IsLinkageBetween G G.source S.boundary W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (pendingPart G W₁))
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q reserve : Set V} {mu : Cardinal.{u}}
    (hBoundaryQ :
      G.vertexSet (completedPart G
          (initialRestriction G F (G.source ∩ S.boundary))) ⊆ Q)
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
    exact hWlink.isWarp (hsub hp.1) (hsub hq.1) hpq
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hWlink.finiteCharacter (hsub hp.1)
  have hFwarp : G.IsWarp F := by
    intro p hp q hq hpq
    exact hWlink.isWarp (hFsub hp) (hFsub hq) hpq
  have hFfinite : G.HasFiniteCharacter F := by
    intro p hp
    exact hWlink.finiteCharacter (hFsub hp)
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
      (hWlink.isWarp (hFsub hpF) (hsub hqP.1) hpq) hxp hxq
  obtain ⟨hRwarp, hRfinite, hRinitialRequest, hRlinksRequest, _hRQ⟩ :=
    currentPart_deletedQuotientPayload B hcurrent
  have hRinitial : (G.quotient S.boundary).initialSet R =
      G.terminalFrontier P := hRinitialRequest.trans hrequestFront
  have hRlinks : LinksToTarget (G.quotient S.boundary) R
      (G.terminalFrontier P) := by
    simpa only [hrequestFront] using hRlinksRequest
  have hUinitial : ((G.delete Q).quotient S.boundary).initialSet U =
      pendingRequests G W₁ S.boundary :=
    (currentPart_isLinkageBetween B).initialSet_eq
  have hUstart : ((G.delete Q).quotient S.boundary).initialSet U ⊆
      ((G.delete Q).quotient S.boundary).source := by
    rw [hUinitial]
    exact hcurrent
  let T := frozenFrontierContinuation G F hPwarp hProof S.minimal
    R hRinitial.le
  let L := frontierContinuation G hPwarp hProof S.minimal R hRinitial.le
  have hstruct :=
    frozenFrontierContinuation_structural_protect_completedBoundaryStarts
      G hWlink S.separator hFsub hFwarp hPwarp hFfinite hPfinite
        hFPvertex S.boundary_pending_trivial hBoundaryQ hProof S.minimal
        (currentPart_isLinkageBetween B).isWarp
        (currentPart_isLinkageBetween B).finiteCharacter hUstart
        hRinitial
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

/-! ## The exact request-subweb successor

The protected-batch constructor above is convenient when a whole deleted
quotient is known to be unhindered.  The actual continuation only uses the
source subweb on the pending requests.  The next theorem combines that
sharper `DeletedPendingSafety` invariant with the completed-boundary
protection lemma.  Thus neither the entire frozen carrier nor the entire
deleted quotient occurs in its safety premise.
-/

/-- Restore a frozen/pending row from the exact future-safe request subweb,
protecting only completed frozen components whose initial vertex lies on the
old boundary. -/
theorem exists_frozenSelectedPendingContinuation_of_safety_protect_completedBoundaryStarts
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hWlink : IsLinkageBetween G G.source S.boundary W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (pendingPart G W₁))
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q : Set V}
    (hBoundaryQ :
      G.vertexSet (completedPart G
          (initialRestriction G F (G.source ∩ S.boundary))) ⊆ Q)
    (hsafe : DeletedPendingSafety G W₁ S.boundary Q mu) :
    ∃ (U : Set (deletedPendingAuxiliaryWeb
        G W₁ S.boundary Q).DPath) (T : Set G.DPath),
      IsHalfwayLinkageOfAltitude
          (deletedPendingAuxiliaryWeb G W₁ S.boundary Q)
          (pendingRequests G W₁ S.boundary)
          (altitude (deletedPendingAuxiliaryWeb G W₁ S.boundary Q) U) U ∧
      G.IsWarp T ∧
      G.HasFiniteCharacter T ∧
      G.ForwardExtension W₂ T ∧
      G.initialSet T = G.initialSet W₂ ∧
      LinksToTarget G T (G.initialSet (pendingPart G W₁)) ∧
      G.terminalFrontier T ⊆
        G.terminalFrontier F ∪
          (G.quotient S.boundary).terminalFrontier
            (deletedQuotientFamily G S.boundary Q
              (forgetDeletedPendingAuxiliaryFamily
                G W₁ S.boundary Q U)) := by
  obtain ⟨U, hU⟩ :=
    hsafe.exists_halfway_of_lower_extension hlower hmu
  let P := pendingPart G W₁
  let U₀ := forgetDeletedPendingAuxiliaryFamily G W₁ S.boundary Q U
  let R := deletedQuotientFamily G S.boundary Q U₀
  have hPtrivial : ∀ p ∈ boundaryPendingPart G W₁ S.boundary,
      p = G.trivialPath p.initial :=
    boundaryPendingPart_trivial_mono G hsub S.boundary_pending_trivial
  have hrequestFront : pendingRequests G W₁ S.boundary =
      G.terminalFrontier P :=
    pendingRequests_eq_terminalFrontier_pendingPart_of_trivial_selected
      hsource hPtrivial
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact hWlink.isWarp (hsub hp.1) (hsub hq.1) hpq
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hWlink.finiteCharacter (hsub hp.1)
  have hFwarp : G.IsWarp F := by
    intro p hp q hq hpq
    exact hWlink.isWarp (hFsub hp) (hFsub hq) hpq
  have hFfinite : G.HasFiniteCharacter F := by
    intro p hp
    exact hWlink.finiteCharacter (hFsub hp)
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
      (hWlink.isWarp (hFsub hpF) (hsub hqP.1) hpq) hxp hxq
  obtain ⟨hRwarp, hRfinite, hRinitialRequest, hRlinksRequest, _hRQ⟩ :=
    deletedPendingAuxiliaryHalfway_quotientPayload
      hsafe.requests_source hU
  have hRinitial : (G.quotient S.boundary).initialSet R =
      G.terminalFrontier P := hRinitialRequest.trans hrequestFront
  have hRlinks : LinksToTarget (G.quotient S.boundary) R
      (G.terminalFrontier P) := by
    simpa only [hrequestFront] using hRlinksRequest
  have hU₀initial : ((G.delete Q).quotient S.boundary).initialSet U₀ =
      pendingRequests G W₁ S.boundary := by
    rw [← deletedQuotientFamily_initialSet]
    exact hRinitialRequest
  have hU₀start : ((G.delete Q).quotient S.boundary).initialSet U₀ ⊆
      ((G.delete Q).quotient S.boundary).source := by
    rw [hU₀initial]
    exact hsafe.requests_source
  obtain ⟨E, hE⟩ := hU.1
  have hU₀warp : ((G.delete Q).quotient S.boundary).IsWarp U₀ := by
    change (deletedPendingAuxiliaryWeb G W₁ S.boundary Q).IsWarp U
    exact hE.linkage.isWarp
  have hU₀finite :
      ((G.delete Q).quotient S.boundary).HasFiniteCharacter U₀ := by
    change (deletedPendingAuxiliaryWeb G W₁ S.boundary Q).HasFiniteCharacter U
    exact hE.linkage.finiteCharacter
  let T := frozenFrontierContinuation G F hPwarp hProof S.minimal
    R hRinitial.le
  have hstruct :=
    frozenFrontierContinuation_structural_protect_completedBoundaryStarts
      G hWlink S.separator hFsub hFwarp hPwarp hFfinite hPfinite
        hFPvertex S.boundary_pending_trivial hBoundaryQ hProof S.minimal
        hU₀warp hU₀finite hU₀start hRinitial
  have hPsource : G.initialSet P ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact hsource ⟨p, hp.1, hpx⟩
  have hRambientLinks : LinksToTarget G
      (frontierContinuation G hPwarp hProof S.minimal R hRinitial.le)
      (G.initialSet P) :=
    linksToTarget_frontierContinuation hNorm hPwarp hPfinite hProof
      S.minimal hRwarp hRfinite hRinitial Set.Subset.rfl hPsource
      (routesTerminals_initialSet_terminalFrontier hPfinite) hRlinks
  refine ⟨U, T, hU, hstruct.1, hstruct.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← hdecomp]
    exact hstruct.2.2.1
  · rw [hstruct.2.2.2, hdecomp]
  · intro b hb
    obtain ⟨p, hp, hrest⟩ := hRambientLinks b hb
    exact ⟨p, Or.inr hp, hrest⟩
  · exact terminalFrontier_frozenFrontierContinuation_subset
      G hPwarp hPfinite hProof S.minimal hRinitial.le hRinitial.ge

/-- Lower-cardinal constructor for the boundary-protected restoration step.
The reserve is fixed together with the current request set, so the lower
half-way clause is applied once to their protected union.  This supplies the
batch and its next unhindered quotient; the ambient restoration then uses
only the completed boundary-starting part of the frozen carrier as its
deletion set. -/
theorem exists_restoreProtectedCurrent_protect_boundaryStarts_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hWlink : IsLinkageBetween G G.source S.boundary W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (pendingPart G W₁))
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q reserve : Set V}
    (hBoundaryQ :
      G.vertexSet (completedPart G
          (initialRestriction G F (G.source ∩ S.boundary))) ⊆ Q)
    (hbase : ((G.delete Q).quotient S.boundary).IsUnhindered)
    (hcurrent : pendingRequests G W₁ S.boundary ⊆
      ((G.delete Q).quotient S.boundary).source)
    (hreserve : reserve ⊆
      ((G.delete Q).quotient S.boundary).source)
    (hcard : #(pendingRequests G W₁ S.boundary) = mu) :
    ∃ B : ProtectedBatch ((G.delete Q).quotient S.boundary)
        (pendingRequests G W₁ S.boundary) reserve mu,
      Nonempty (RestoredProtectedStep G W₂ F (pendingPart G W₁)
        (G.initialSet (pendingPart G W₁)) B) := by
  let H := (G.delete Q).quotient S.boundary
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hNoEnterH : H.NoEdgeEnters H.source :=
    DWeb.NoEdgeEnters.quotient (G.delete Q) hNoEnter.delete
  obtain ⟨B⟩ := exists_protectedBatch_of_lower
    hlower hmu hmuInfinite H hbase hNoEnterH hcurrent hreserve hcard
  exact ⟨B,
    restoreProtectedCurrent_protect_boundaryStarts hNorm S hWlink
      hFsub hsub hdecomp hfamilyDisjoint hsource hBoundaryQ hcurrent B⟩

/-- Exact joint-exchange form of the boundary-protected successor.  The
lower construction does not need the whole deleted quotient to be
unhindered: it is applied directly in the protected source subweb carrying
the current requests together with the look-ahead reserve. -/
theorem exists_restoreProtectedCurrent_protect_boundaryStarts_of_protectedRequestWeb
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hWlink : IsLinkageBetween G G.source S.boundary W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (pendingPart G W₁))
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q reserve : Set V}
    (hBoundaryQ :
      G.vertexSet (completedPart G
          (initialRestriction G F (G.source ∩ S.boundary))) ⊆ Q)
    (hcurrent : pendingRequests G W₁ S.boundary ⊆
      ((G.delete Q).quotient S.boundary).source)
    (hreserve : reserve ⊆
      ((G.delete Q).quotient S.boundary).source)
    (hprotected :
      (protectedRequestWeb ((G.delete Q).quotient S.boundary)
        (pendingRequests G W₁ S.boundary) reserve).IsUnhindered)
    (hcard : #(pendingRequests G W₁ S.boundary) = mu) :
    ∃ B : ProtectedBatch ((G.delete Q).quotient S.boundary)
        (pendingRequests G W₁ S.boundary) reserve mu,
      Nonempty (RestoredProtectedStep G W₂ F (pendingPart G W₁)
        (G.initialSet (pendingPart G W₁)) B) := by
  let H := (G.delete Q).quotient S.boundary
  let current := pendingRequests G W₁ S.boundary
  let K := protectedRequestWeb H current reserve
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hNoEnterH : H.NoEdgeEnters H.source :=
    DWeb.NoEdgeEnters.quotient (G.delete Q) hNoEnter.delete
  have hNoEnterK : K.NoEdgeEnters K.source :=
    noEdgeEnters_protectedRequestWeb hNoEnterH hcurrent hreserve
  have hcurrentK : current ⊆ K.source := Set.subset_union_left
  obtain ⟨U, hU⟩ :=
    (hlower mu hmu K hprotected).halfway
      hmuInfinite current hcurrentK hcard
  obtain ⟨C, hC, hheightC⟩ := hU.exists_stopover
  obtain ⟨D, hD, hheightD, _hDsub⟩ :=
    SingularQuotientReentry.exists_separatingStopover_of_stopover
      hNoEnterK hC hheightC
  let B : ProtectedBatch H current reserve mu :=
    { paths := U
      boundary := D
      halfway := hU
      separating := hD
      height := hheightD }
  exact ⟨B,
    restoreProtectedCurrent_protect_boundaryStarts hNorm S hWlink
      hFsub hsub hdecomp hfamilyDisjoint hsource hBoundaryQ hcurrent B⟩

#print axioms restoreProtectedCurrent_protect_boundaryStarts
#print axioms exists_frozenSelectedPendingContinuation_of_safety_protect_completedBoundaryStarts
#print axioms exists_restoreProtectedCurrent_protect_boundaryStarts_of_lower
#print axioms exists_restoreProtectedCurrent_protect_boundaryStarts_of_protectedRequestWeb

end SingularBoundaryProtectedRestoration
end CardinalInduction
end Erdos599
