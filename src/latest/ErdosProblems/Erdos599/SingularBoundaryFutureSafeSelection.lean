/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularBoundaryProtectedRestoration
import ErdosProblems.Erdos599.SingularFutureSafeBatch

/-!
# Joint future safety with boundary-start protection

`SingularBoundaryProtectedRestoration` shows that a frozen/pending
continuation does not have to delete the carrier of every completed
component.  It is enough to delete the completed components whose initial
vertices already lie on the old separating boundary.  This file gives that
sharper deleted set its construction-facing joint-selection interface.

The reserve is still allowed to depend on the selected full-source batch.
Consequently the definition does not assert a false safety property of an
arbitrary half-way row.  Once a jointly safe batch is available, however,
it supplies exactly `DeletedPendingSafety` and hence feeds the concrete
boundary-protected restoration theorem without any whole-frozen-carrier or
whole-deleted-quotient premise.

The lower induction hypothesis constructs this joint selector whenever the
whole residual source is below the induction cardinal, or whenever a
complementary target linkage is available.  In both cases it produces a full
source--target linkage, so every prospective reserve coordinate is already
completed and the next request subweb has empty source.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularBoundaryFutureSafeSelection

open SingularBoundaryProtectedRestoration SingularExtension
  SingularFutureSafeBatch SingularPendingDecomposition
  SingularPendingReentry SingularSafeBatch SingularTargetRowMachine
  SliceSpliceSource

universe u

variable {V : Type u}

/-! ## The minimal boundary-start deleted set -/

/-- The completed members of a full-source batch whose initial vertices
already lie on its separating boundary. -/
def completedBoundaryPart
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) : Set H.DPath :=
  completedPart H
    (initialRestriction H B.paths (H.source ∩ B.boundary))

/-- Only the carrier of completed boundary-starting components needs to be
protected by the deleted pending auxiliary web. -/
def completedBoundaryCarrier
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) : Set V :=
  H.vertexSet (completedBoundaryPart B)

/-- The next request web after deleting only completed boundary starts. -/
def boundaryNextRequestWeb
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) (reserve : Set V) : DWeb V :=
  ((H.delete (completedBoundaryCarrier B)).quotient B.boundary).sourceSubweb
    (nextRequests B reserve)

/-- The exact post-choice safety invariant consumed by boundary-protected
restoration.  Unlike `FutureSafeFor`, the deleted carrier is only the
completed boundary-start part of the chosen batch. -/
structure BoundaryFutureSafeFor
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) (reserve : Set V) : Prop where
  reserve_source : reserve ⊆ H.source
  requests_source : nextRequests B reserve ⊆
    ((H.delete (completedBoundaryCarrier B)).quotient B.boundary).source
  residual_unhindered : (boundaryNextRequestWeb B reserve).IsUnhindered

namespace BoundaryFutureSafeFor

variable {H : DWeb V} {current reserve : Set V}

/-- If every reserve coordinate is already completed, boundary future
safety is automatic: the distinguished source of the next request web is
empty, independently of the boundary-start carrier being deleted. -/
theorem of_pendingReserve_eq_empty
    (B : FullSourceSafeBatch H current)
    (hreserve : reserve ⊆ H.source)
    (hpending : pendingReserve B reserve = ∅) :
    BoundaryFutureSafeFor B reserve := by
  have hrequests : nextRequests B reserve = ∅ :=
    FullSourceSafeBatch.nextRequests_eq_empty_of_pendingReserve_eq_empty
      B hpending
  refine ⟨hreserve, ?_, ?_⟩
  · rw [hrequests]
    exact Set.empty_subset _
  · apply isUnhindered_of_source_eq_empty
    unfold boundaryNextRequestWeb
    rw [hrequests]
    exact DWeb.sourceSubweb_source _ _

/-- Boundary future safety is preserved when the post-choice reserve is
shrunk.  This is the useful direction for a global construction: a batch may
be selected against a provisional closed envelope, after which the final
competitor reserve may be any subset of that envelope. -/
theorem mono
    (hNoEnter : H.NoEdgeEnters H.source)
    (B : FullSourceSafeBatch H current)
    {reserve₁ reserve₂ : Set V}
    (hsafe : BoundaryFutureSafeFor B reserve₂)
    (hreserve : reserve₁ ⊆ reserve₂) :
    BoundaryFutureSafeFor B reserve₁ := by
  let K := (H.delete (completedBoundaryCarrier B)).quotient B.boundary
  have hrequests : nextRequests B reserve₁ ⊆ nextRequests B reserve₂ :=
    FullSourceSafeBatch.nextRequests_mono B hreserve
  have hrequestsSource : nextRequests B reserve₁ ⊆ K.source :=
    hrequests.trans hsafe.requests_source
  refine ⟨hreserve.trans hsafe.reserve_source, hrequestsSource, ?_⟩
  have hKNoEnter : K.NoEdgeEnters K.source :=
    DWeb.NoEdgeEnters.quotient (H.delete (completedBoundaryCarrier B))
      hNoEnter.delete
  have hSubNoEnter :
      (K.sourceSubweb (nextRequests B reserve₂)).NoEdgeEnters
        (K.sourceSubweb (nextRequests B reserve₂)).source := by
    intro x y hxy hy
    exact hKNoEnter hxy (hsafe.requests_source hy)
  exact hsafe.residual_unhindered.sourceSubweb
    (K.sourceSubweb (nextRequests B reserve₂)) hSubNoEnter hrequests

/-- The boundary-start invariant is already the precise
`DeletedPendingSafety` certificate once the displayed row's requests are
identified with the post-choice reserve coordinates. -/
theorem deletedPendingSafety
    (B : FullSourceSafeBatch H current)
    (hsafe : BoundaryFutureSafeFor B reserve)
    {W : Set H.DPath}
    (hrequests : pendingRequests H W B.boundary =
      nextRequests B reserve) :
    DeletedPendingSafety H W B.boundary
      (completedBoundaryCarrier B) #(pendingReserve B reserve) where
  requests_source := by
    rw [hrequests]
    exact hsafe.requests_source
  residual_unhindered := by
    unfold deletedPendingAuxiliaryWeb
    rw [hrequests]
    change (boundaryNextRequestWeb B reserve).IsUnhindered
    exact hsafe.residual_unhindered
  requests_card := by
    rw [hrequests]
    exact FullSourceSafeBatch.mk_nextRequests_eq B hsafe.reserve_source

end BoundaryFutureSafeFor

/-! ## Joint post-choice selection -/

/-- A batch and the safety certificate for the reserve computed from that
very batch.  This is the minimal non-circular selector for the sharpened
boundary-start restoration theorem. -/
structure JointBoundaryFutureSafeSelection
    (H : DWeb V) (current : Set V)
    (reserveAfter : FullSourceSafeBatch H current → Set V) where
  batch : FullSourceSafeBatch H current
  futureSafe : BoundaryFutureSafeFor batch (reserveAfter batch)

namespace JointBoundaryFutureSafeSelection

variable {H : DWeb V} {current : Set V}
variable {reserveAfter : FullSourceSafeBatch H current → Set V}

/-- Pointwise shrinking of a batch-dependent reserve rule preserves a
jointly selected boundary-safe batch. -/
def mono_reserveAfter
    (hNoEnter : H.NoEdgeEnters H.source)
    {reserveAfter₁ reserveAfter₂ :
      FullSourceSafeBatch H current → Set V}
    (J : JointBoundaryFutureSafeSelection H current reserveAfter₂)
    (hreserve : ∀ B, reserveAfter₁ B ⊆ reserveAfter₂ B) :
    JointBoundaryFutureSafeSelection H current reserveAfter₁ where
  batch := J.batch
  futureSafe := BoundaryFutureSafeFor.mono hNoEnter J.batch J.futureSafe
    (hreserve J.batch)

/-- Direct conversion of a joint boundary-safe choice to the exact safety
record used by the deleted pending continuation. -/
theorem deletedPendingSafety
    (J : JointBoundaryFutureSafeSelection H current reserveAfter)
    {W : Set H.DPath}
    (hrequests : pendingRequests H W J.batch.boundary =
      nextRequests J.batch (reserveAfter J.batch)) :
    DeletedPendingSafety H W J.batch.boundary
      (completedBoundaryCarrier J.batch)
      #(pendingReserve J.batch (reserveAfter J.batch)) :=
  BoundaryFutureSafeFor.deletedPendingSafety
    J.batch J.futureSafe hrequests

end JointBoundaryFutureSafeSelection

/-! ## Unconditional lower-cardinal branches -/

/-- A full source--target linkage is boundary-future-safe for every reserve:
all reserve coordinates are completed by the linkage. -/
theorem fullLinkageSafeBatch_boundaryFutureSafeFor
    {H : DWeb V} {current reserve : Set V} {P : Set H.DPath}
    (hP : IsLinkageBetween H H.source H.target P)
    (hcurrent : current ⊆ H.source) (hreserve : reserve ⊆ H.source) :
    BoundaryFutureSafeFor (fullLinkageSafeBatch hP hcurrent) reserve := by
  apply BoundaryFutureSafeFor.of_pendingReserve_eq_empty
    (fullLinkageSafeBatch hP hcurrent) hreserve
  exact fullLinkageSafeBatch_pendingReserve hP hcurrent hreserve

/-- If the residual source is below `kappa`, lower-cardinal extension gives
a full linkage and hence a joint boundary-safe choice for an arbitrary
post-choice reserve function. -/
theorem exists_jointBoundaryFutureSafeSelection_of_source_below
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    (hsource : #H.source < kappa)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (reserveAfter : FullSourceSafeBatch H current → Set V)
    (hreserve : ∀ B, reserveAfter B ⊆ H.source) :
    Nonempty
      (JointBoundaryFutureSafeSelection H current reserveAfter) := by
  have hext : ExtensionClauseAt H #H.source :=
    (hlower #H.source hsource H hH).extension
  obtain ⟨P, hP⟩ := linkable_of_extension_at_source_card H hext
  let B := fullLinkageSafeBatch hP hcurrent
  exact ⟨⟨B, fullLinkageSafeBatch_boundaryFutureSafeFor
    hP hcurrent (hreserve B)⟩⟩

/-- If the sources outside the current request already have a target
linkage, lower-cardinal extension again upgrades to a full linkage and
produces the joint boundary-safe selection. -/
theorem exists_jointBoundaryFutureSafeSelection_of_complement_linkable
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrhoKappa : rho < kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (hcurrentCard : #current = rho)
    (hcomplement : ∃ F : Set H.DPath,
      IsLinkageBetween H (H.source \ current) H.target F)
    (reserveAfter : FullSourceSafeBatch H current → Set V)
    (hreserve : ∀ B, reserveAfter B ⊆ H.source) :
    Nonempty
      (JointBoundaryFutureSafeSelection H current reserveAfter) := by
  have hext : ExtensionClauseAt H rho :=
    (hlower rho hrhoKappa H hH).extension
  obtain ⟨P, hP⟩ : IsLinkable H :=
    hext current hcurrent hcurrentCard hcomplement
  let B := fullLinkageSafeBatch hP hcurrent
  exact ⟨⟨B, fullLinkageSafeBatch_boundaryFutureSafeFor
    hP hcurrent (hreserve B)⟩⟩

/-- Structural-row adapter for the complementary-linkage branch. -/
theorem exists_jointBoundaryFutureSafeSelection_of_structural_complement_links
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrhoKappa : rho < kappa)
    {H : DWeb V} (hH : H.IsUnhindered) (hNorm : H.IsNormalized)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (hcurrentCard : #current = rho)
    {W : Set H.DPath} (hwarp : H.IsWarp W)
    (hfinite : H.HasFiniteCharacter W)
    (hinitial : H.initialSet W = H.source)
    (hcomplementLinks : LinksToTarget H W (H.source \ current))
    (reserveAfter : FullSourceSafeBatch H current → Set V)
    (hreserve : ∀ B, reserveAfter B ⊆ H.source) :
    Nonempty
      (JointBoundaryFutureSafeSelection H current reserveAfter) := by
  apply exists_jointBoundaryFutureSafeSelection_of_complement_linkable
    hlower hrhoKappa hH hcurrent hcurrentCard
  · exact ⟨initialRestriction H W (H.source \ current),
      SingularFutureSafeBatch.isLinkageBetween_initialRestriction_of_structural_links
        hNorm hwarp hfinite hinitial Set.sdiff_subset hcomplementLinks⟩
  · exact hreserve

/-- Below the strict-large branch, the lower induction hypothesis already
constructs the joint boundary-safe selector. -/
theorem jointBoundaryFutureSafeSelection_or_scale_lt_source
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrhoKappa : rho < kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (reserveAfter : FullSourceSafeBatch H current → Set V)
    (hreserve : ∀ B, reserveAfter B ⊆ H.source) :
    Nonempty (JointBoundaryFutureSafeSelection H current reserveAfter) ∨
      rho < #H.source := by
  by_cases hlarge : rho < #H.source
  · exact Or.inr hlarge
  · apply Or.inl
    apply exists_jointBoundaryFutureSafeSelection_of_source_below
      hlower hH ((le_of_not_gt hlarge).trans_lt hrhoKappa)
      hcurrent reserveAfter hreserve

/-! ## Direct boundary-restoration consumer -/

/-- Feed a jointly boundary-safe selection into the precise frozen/pending
continuation.  The equality hypotheses identify the chosen batch boundary
and its post-choice reserve coordinates with the row being restored; the
only protected carrier premise is the completed boundary-start subfamily.
-/
theorem exists_frozenSelectedPendingContinuation_of_jointBoundarySelection
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hWlink : IsLinkageBetween G G.source S.boundary W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (pendingPart G W₁))
    (hsource : G.initialSet W₁ ⊆ G.source)
    {current : Set V}
    {reserveAfter : FullSourceSafeBatch G current → Set V}
    (J : JointBoundaryFutureSafeSelection G current reserveAfter)
    (hboundary : J.batch.boundary = S.boundary)
    (hBoundaryCarrier :
      G.vertexSet (completedPart G
          (initialRestriction G F (G.source ∩ S.boundary))) ⊆
        completedBoundaryCarrier J.batch)
    (hrequests : pendingRequests G W₁ J.batch.boundary =
      nextRequests J.batch (reserveAfter J.batch))
    (hmu : #(pendingReserve J.batch (reserveAfter J.batch)) < kappa) :
    ∃ (U : Set (deletedPendingAuxiliaryWeb G W₁ S.boundary
          (completedBoundaryCarrier J.batch)).DPath)
        (T : Set G.DPath),
      IsHalfwayLinkageOfAltitude
          (deletedPendingAuxiliaryWeb G W₁ S.boundary
            (completedBoundaryCarrier J.batch))
          (pendingRequests G W₁ S.boundary)
          (altitude (deletedPendingAuxiliaryWeb G W₁ S.boundary
            (completedBoundaryCarrier J.batch)) U) U ∧
      G.IsWarp T ∧
      G.HasFiniteCharacter T ∧
      G.ForwardExtension W₂ T ∧
      G.initialSet T = G.initialSet W₂ ∧
      LinksToTarget G T (G.initialSet (pendingPart G W₁)) ∧
      G.terminalFrontier T ⊆
        G.terminalFrontier F ∪
          (G.quotient S.boundary).terminalFrontier
            (deletedQuotientFamily G S.boundary
              (completedBoundaryCarrier J.batch)
              (forgetDeletedPendingAuxiliaryFamily G W₁ S.boundary
                (completedBoundaryCarrier J.batch) U)) := by
  have hsafeJ := J.deletedPendingSafety hrequests
  have hsafe : DeletedPendingSafety G W₁ S.boundary
      (completedBoundaryCarrier J.batch)
      #(pendingReserve J.batch (reserveAfter J.batch)) := by
    simpa only [hboundary] using hsafeJ
  exact
    exists_frozenSelectedPendingContinuation_of_safety_protect_completedBoundaryStarts
      hlower hmu
      hNorm S hWlink hFsub hsub hdecomp hfamilyDisjoint hsource
      hBoundaryCarrier hsafe

#print axioms BoundaryFutureSafeFor.deletedPendingSafety
#print axioms BoundaryFutureSafeFor.mono
#print axioms fullLinkageSafeBatch_boundaryFutureSafeFor
#print axioms exists_jointBoundaryFutureSafeSelection_of_source_below
#print axioms exists_jointBoundaryFutureSafeSelection_of_complement_linkable
#print axioms exists_jointBoundaryFutureSafeSelection_of_structural_complement_links
#print axioms jointBoundaryFutureSafeSelection_or_scale_lt_source
#print axioms exists_frozenSelectedPendingContinuation_of_jointBoundarySelection

end SingularBoundaryFutureSafeSelection
end CardinalInduction
end Erdos599
