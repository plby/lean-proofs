/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeBatch

/-!
# Jointly future-safe full-source batches

`SingularSafeBatch.FullSourceBatch` deliberately allows the next reserve to
be named after the half-way family has been chosen.  Full source coverage
alone does not say that the components completed by that family may safely
be deleted: a later reserve path may need a vertex of one of those completed
components.

This module records the missing joint selection invariant.  It is phrased
for `FullSourceSafeBatch`, the common geometric interface of the half-way
and small-source branches, and specializes directly to `FullSourceBatch`.
The reserve is passed as a function of the chosen batch, so the definition
does not reintroduce the circular preselection of a `ProtectedBatch`.

The main composition theorem turns the joint invariant into the exact
`DeletedPendingSafety` certificate consumed by the singular restoration
step.  The small-source branch is constructed unconditionally: the lower
extension clause links the whole residual source, so every reserve has empty
pending remainder.  The genuinely new large-source obligation is now
isolated to selecting a half-way batch satisfying `FutureSafeFor`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFutureSafeBatch

open SingularExtension SingularPendingDecomposition SingularPendingReentry
  SingularSafeBatch SingularTargetRowMachine SliceSpliceSource

universe u

variable {V : Type u}

/-! ## The post-choice safety invariant -/

/-- Forget only the altitude field of a `FullSourceBatch`. -/
def toSafeBatch
    {H : DWeb V} {current : Set V} {mu : Cardinal.{u}}
    (B : FullSourceBatch H current mu) :
    FullSourceSafeBatch H current where
  paths := B.paths
  boundary := B.boundary
  separating := B.separating
  links := B.links_current

@[simp] theorem toSafeBatch_paths
    {H : DWeb V} {current : Set V} {mu : Cardinal.{u}}
    (B : FullSourceBatch H current mu) :
    (toSafeBatch B).paths = B.paths := rfl

@[simp] theorem toSafeBatch_boundary
    {H : DWeb V} {current : Set V} {mu : Cardinal.{u}}
    (B : FullSourceBatch H current mu) :
    (toSafeBatch B).boundary = B.boundary := rfl

/-- The carrier which will be frozen after the batch has reached the target
on some of its components. -/
def completedCarrier
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) : Set V :=
  H.vertexSet (completedPart H B.paths)

/-- The source coordinates whose batch components have already completed. -/
def completedInitials
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) : Set V :=
  H.initialSet (completedPart H B.paths)

/-- A reserve is still pending precisely when its source coordinate was not
completed by the chosen batch. -/
def pendingReserve
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) (reserve : Set V) : Set V :=
  reserve \ completedInitials B

/-- Terminal coordinates of the post-choice reserve components which remain
pending. -/
def nextRequests
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) (reserve : Set V) : Set V :=
  B.reserveFrontier (pendingReserve B reserve)

/-- The exact next request web after completed batch components are frozen. -/
def nextRequestWeb
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) (reserve : Set V) : DWeb V :=
  ((H.delete (completedCarrier B)).quotient B.boundary).sourceSubweb
    (nextRequests B reserve)

/-- The minimal joint invariant missing from an arbitrary full-source
half-way batch.  Both fields after `reserve_source` concern the batch chosen
*before* `reserve` was computed: the surviving terminal coordinates really
are sources after completed-carrier deletion, and their exact request web is
unhindered. -/
structure FutureSafeFor
    {H : DWeb V} {current : Set V}
    (B : FullSourceSafeBatch H current) (reserve : Set V) : Prop where
  reserve_source : reserve ⊆ H.source
  requests_source : nextRequests B reserve ⊆
    ((H.delete (completedCarrier B)).quotient B.boundary).source
  residual_unhindered : (nextRequestWeb B reserve).IsUnhindered

namespace FullSourceSafeBatch

variable {H : DWeb V} {current reserve : Set V}

theorem pendingReserve_subset (B : FullSourceSafeBatch H current) :
    pendingReserve B reserve ⊆ reserve :=
  Set.sdiff_subset

theorem pendingReserve_subset_source
    (B : FullSourceSafeBatch H current)
    (hreserve : reserve ⊆ H.source) :
    pendingReserve B reserve ⊆ H.source :=
  (pendingReserve_subset B).trans hreserve

/-- Removing post-choice reserve coordinates can only remove pending
coordinates. -/
theorem pendingReserve_mono
    (B : FullSourceSafeBatch H current) {reserve₁ reserve₂ : Set V}
    (hreserve : reserve₁ ⊆ reserve₂) :
    pendingReserve B reserve₁ ⊆ pendingReserve B reserve₂ := by
  intro a ha
  exact ⟨hreserve ha.1, ha.2⟩

/-- The terminal-coordinate change is monotone in the reserve. -/
theorem nextRequests_mono
    (B : FullSourceSafeBatch H current) {reserve₁ reserve₂ : Set V}
    (hreserve : reserve₁ ⊆ reserve₂) :
    nextRequests B reserve₁ ⊆ nextRequests B reserve₂ := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, ⟨hp.1, pendingReserve_mono B hreserve hp.2⟩, hpx⟩

/-- The post-choice coordinate change loses no pending reserve cardinal. -/
theorem mk_nextRequests_eq
    (B : FullSourceSafeBatch H current)
    (hreserve : reserve ⊆ H.source) :
    #(nextRequests B reserve) = #(pendingReserve B reserve) := by
  exact B.mk_reserveFrontier_eq (pendingReserve_subset_source B hreserve)

theorem nextRequests_eq_empty_of_pendingReserve_eq_empty
    (B : FullSourceSafeBatch H current)
    (hpending : pendingReserve B reserve = ∅) :
    nextRequests B reserve = ∅ := by
  unfold nextRequests
  rw [hpending]
  unfold FullSourceSafeBatch.reserveFrontier
  unfold SingularBoundarySplit.requestedFrontier
  have hrestrict : initialRestriction H B.paths ∅ = ∅ := by
    ext p
    simp only [mem_initialRestriction, Set.mem_empty_iff_false, and_false]
  rw [hrestrict]
  ext x
  constructor <;> intro hx
  · exact hx.choose_spec.1.elim
  · exact hx.elim

/-- If the whole quotient after completed-carrier deletion is unhindered,
the minimal request-subweb invariant follows by source restriction. -/
theorem FutureSafeFor.of_deletedQuotient
    (hNorm : H.IsNormalized)
    (B : FullSourceSafeBatch H current)
    (hreserve : reserve ⊆ H.source)
    (hbase : ((H.delete (completedCarrier B)).quotient
      B.boundary).IsUnhindered)
    (hrequest : nextRequests B reserve ⊆
      ((H.delete (completedCarrier B)).quotient B.boundary).source) :
    FutureSafeFor B reserve := by
  refine ⟨hreserve, hrequest, ?_⟩
  have hNoEnter : H.NoEdgeEnters H.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  unfold nextRequestWeb
  exact hbase.sourceSubweb
    ((H.delete (completedCarrier B)).quotient B.boundary)
    (DWeb.NoEdgeEnters.quotient (H.delete (completedCarrier B))
      hNoEnter.delete)
    hrequest

/-- A batch which leaves no pending reserve is future-safe independently of
the graph left after its completed carrier is frozen. -/
theorem FutureSafeFor.of_pendingReserve_eq_empty
    (B : FullSourceSafeBatch H current)
    (hreserve : reserve ⊆ H.source)
    (hpending : pendingReserve B reserve = ∅) :
    FutureSafeFor B reserve := by
  have hrequests : nextRequests B reserve = ∅ :=
    nextRequests_eq_empty_of_pendingReserve_eq_empty B hpending
  refine ⟨hreserve, ?_, ?_⟩
  · rw [hrequests]
    exact Set.empty_subset _
  · apply isUnhindered_of_source_eq_empty
    unfold nextRequestWeb
    rw [hrequests]
    exact DWeb.sourceSubweb_source _ _

/-- Future safety is preserved when a later consumer asks for fewer reserve
coordinates.  This is the fixed-point preservation law used when a closed
row replaces a provisional reserve by a smaller final one. -/
theorem FutureSafeFor.mono
    (hNoEnter : H.NoEdgeEnters H.source)
    (B : FullSourceSafeBatch H current)
    {reserve₁ reserve₂ : Set V}
    (hsafe : FutureSafeFor B reserve₂)
    (hreserve : reserve₁ ⊆ reserve₂) :
    FutureSafeFor B reserve₁ := by
  let K := (H.delete (completedCarrier B)).quotient B.boundary
  have hrequests : nextRequests B reserve₁ ⊆ nextRequests B reserve₂ :=
    nextRequests_mono B hreserve
  have hrequestsSource : nextRequests B reserve₁ ⊆ K.source :=
    hrequests.trans hsafe.requests_source
  refine ⟨hreserve.trans hsafe.reserve_source, hrequestsSource, ?_⟩
  have hKNoEnter : K.NoEdgeEnters K.source :=
    DWeb.NoEdgeEnters.quotient (H.delete (completedCarrier B))
      hNoEnter.delete
  have hSubNoEnter :
      (K.sourceSubweb (nextRequests B reserve₂)).NoEdgeEnters
        (K.sourceSubweb (nextRequests B reserve₂)).source := by
    intro x y hxy hy
    exact hKNoEnter hxy (hsafe.requests_source hy)
  have hsub := hsafe.residual_unhindered.sourceSubweb
    (K.sourceSubweb (nextRequests B reserve₂)) hSubNoEnter hrequests
  exact hsub

/-- Current requests are among the completed coordinates in a normalized
web.  This is not a safety statement; it only identifies which reserve
coordinates no longer need another target link. -/
theorem current_subset_completedInitials
    (hNorm : H.IsNormalized) (hcurrent : current ⊆ H.source)
    (B : FullSourceSafeBatch H current) :
    current ⊆ completedInitials B := by
  intro a ha
  obtain ⟨p, hp, q, hpq, hpure, hsuffix⟩ :=
    linksToTarget_completedPart hNorm B.links a ha
  subst p
  have haSupport : a ∈ q.support := by
    have haInter : a ∈ q.support ∩ current := by
      rw [hpure]
      exact Set.mem_singleton a
    exact haInter.1
  have hstart : q.start = a :=
    (hNorm.eq_initial_of_mem_path (.inl q) haSupport (hcurrent ha)).symm
  exact ⟨Sum.inl q, hp, hstart⟩

/-- Composition into the exact certificate consumed by
`SingularPendingReentry`: once the restored displayed row identifies its
pending requests with the post-choice reserve frontier, no further safety
assumption or protected batch is needed. -/
theorem FutureSafeFor.deletedPendingSafety
    (B : FullSourceSafeBatch H current)
    (hsafe : FutureSafeFor B reserve)
    {W : Set H.DPath}
    (hrequests : pendingRequests H W B.boundary = nextRequests B reserve) :
    DeletedPendingSafety H W B.boundary (completedCarrier B)
      #(pendingReserve B reserve) where
  requests_source := by
    rw [hrequests]
    exact hsafe.requests_source
  residual_unhindered := by
    unfold deletedPendingAuxiliaryWeb
    rw [hrequests]
    exact hsafe.residual_unhindered
  requests_card := by
    rw [hrequests]
    exact mk_nextRequests_eq B hsafe.reserve_source

end FullSourceSafeBatch

/-! ## A genuinely post-choice selector -/

/-- Future safety specialized to the altitude-bearing batch returned by the
lower half-way clause. -/
def FullSourceBatchFutureSafeFor
    {H : DWeb V} {current : Set V} {mu : Cardinal.{u}}
    (B : FullSourceBatch H current mu) (reserve : Set V) : Prop :=
  FutureSafeFor (toSafeBatch B) reserve

/-- The exact large-source fixed point: the reserve may inspect the chosen
`FullSourceBatch`, but that batch must already be safe for its computed
reserve.  Proving this structure nonempty is the remaining joint-selection
theorem; bare `exists_fullSourceBatch_of_lower` is intentionally not enough. -/
structure JointFullSourceBatchSelection
    (H : DWeb V) (current : Set V) (mu : Cardinal.{u})
    (reserveAfter : FullSourceBatch H current mu → Set V) where
  batch : FullSourceBatch H current mu
  futureSafe : FullSourceBatchFutureSafeFor batch (reserveAfter batch)

namespace JointFullSourceBatchSelection

variable {H : DWeb V} {current : Set V} {mu : Cardinal.{u}}
variable {reserveAfter : FullSourceBatch H current mu → Set V}

/-- Once a full-source fixed point has been selected, replacing its reserve
rule by a pointwise smaller rule preserves the same selected batch. -/
def mono_reserveAfter
    (hNoEnter : H.NoEdgeEnters H.source)
    {reserveAfter₁ reserveAfter₂ :
      FullSourceBatch H current mu → Set V}
    (J : JointFullSourceBatchSelection H current mu reserveAfter₂)
    (hreserve : ∀ B, reserveAfter₁ B ⊆ reserveAfter₂ B) :
    JointFullSourceBatchSelection H current mu reserveAfter₁ where
  batch := J.batch
  futureSafe := FullSourceSafeBatch.FutureSafeFor.mono hNoEnter
    (toSafeBatch J.batch) J.futureSafe (hreserve J.batch)

/-- The altitude-bearing fixed point feeds the same pending-restoration
interface without a `ProtectedBatch` conversion. -/
theorem deletedPendingSafety
    (J : JointFullSourceBatchSelection H current mu reserveAfter)
    {W : Set H.DPath}
    (hrequests : pendingRequests H W J.batch.boundary =
      nextRequests (toSafeBatch J.batch) (reserveAfter J.batch)) :
    DeletedPendingSafety H W J.batch.boundary
      (completedCarrier (toSafeBatch J.batch))
      #(pendingReserve (toSafeBatch J.batch) (reserveAfter J.batch)) :=
  FullSourceSafeBatch.FutureSafeFor.deletedPendingSafety
    (toSafeBatch J.batch) J.futureSafe hrequests

end JointFullSourceBatchSelection

/-- A reserve-selection function may inspect the chosen batch.  A value of
this structure is the non-circular fixed point needed by the row machine:
the selected batch is safe for the reserve computed from that very batch. -/
structure JointFutureSafeSelection
    (H : DWeb V) (current : Set V)
    (reserveAfter : FullSourceSafeBatch H current → Set V) where
  batch : FullSourceSafeBatch H current
  futureSafe : FutureSafeFor batch (reserveAfter batch)

namespace JointFutureSafeSelection

variable {H : DWeb V} {current : Set V}
variable {reserveAfter : FullSourceSafeBatch H current → Set V}

/-- Pointwise reserve shrinking preserves a jointly future-safe selection. -/
def mono_reserveAfter
    (hNoEnter : H.NoEdgeEnters H.source)
    {reserveAfter₁ reserveAfter₂ :
      FullSourceSafeBatch H current → Set V}
    (J : JointFutureSafeSelection H current reserveAfter₂)
    (hreserve : ∀ B, reserveAfter₁ B ⊆ reserveAfter₂ B) :
    JointFutureSafeSelection H current reserveAfter₁ where
  batch := J.batch
  futureSafe := FullSourceSafeBatch.FutureSafeFor.mono hNoEnter
    J.batch J.futureSafe (hreserve J.batch)

/-- Direct row-machine consumer for a jointly selected batch. -/
theorem deletedPendingSafety
    (J : JointFutureSafeSelection H current reserveAfter)
    {W : Set H.DPath}
    (hrequests : pendingRequests H W J.batch.boundary =
      nextRequests J.batch (reserveAfter J.batch)) :
    DeletedPendingSafety H W J.batch.boundary (completedCarrier J.batch)
      #(pendingReserve J.batch (reserveAfter J.batch)) :=
  FullSourceSafeBatch.FutureSafeFor.deletedPendingSafety
    J.batch J.futureSafe hrequests

end JointFutureSafeSelection

/-! ## Unconditional small-source selection -/

/-- Every member of a full source--target linkage is completed. -/
theorem completedPart_eq_of_fullLinkage
    {H : DWeb V} {P : Set H.DPath}
    (hP : IsLinkageBetween H H.source H.target P) :
    completedPart H P = P := by
  apply Set.Subset.antisymm
  · exact fun _ hp ↦ hp.1
  · intro p hpP
    obtain ⟨q, rfl⟩ := hP.finiteCharacter hpP
    have hfinish : q.finish ∈ H.target := by
      apply hP.terminalFrontier_subset
      exact ⟨Sum.inl q, hpP, rfl⟩
    exact ⟨hpP, q.finish, hfinish, rfl⟩

/-- A full source--target linkage, viewed as a full-source batch at the
target stop-over. -/
def fullLinkageSafeBatch
    {H : DWeb V} {current : Set V} {P : Set H.DPath}
    (hP : IsLinkageBetween H H.source H.target P)
    (hcurrent : current ⊆ H.source) :
    FullSourceSafeBatch H current where
  paths := P
  boundary := H.target
  separating := by
    refine ⟨⟨hP, ?_, target_subset_isTrimmedSeparator Set.Subset.rfl,
      quotient_target_isUnhindered H⟩, ?_⟩
    · intro a _ha
      rw [roof_target]
      exact Set.mem_univ a
    intro a _ha
    rw [roof_target]
    exact Set.mem_univ a
  links := fullLinkage_linksToTarget hP hcurrent

@[simp] theorem fullLinkageSafeBatch_completedInitials
    {H : DWeb V} {current : Set V} {P : Set H.DPath}
    (hP : IsLinkageBetween H H.source H.target P)
    (hcurrent : current ⊆ H.source) :
    completedInitials (fullLinkageSafeBatch hP hcurrent) = H.source := by
  unfold completedInitials fullLinkageSafeBatch
  rw [completedPart_eq_of_fullLinkage hP, hP.initialSet_eq]

@[simp] theorem fullLinkageSafeBatch_pendingReserve
    {H : DWeb V} {current reserve : Set V} {P : Set H.DPath}
    (hP : IsLinkageBetween H H.source H.target P)
    (hcurrent : current ⊆ H.source) (hreserve : reserve ⊆ H.source) :
    pendingReserve (fullLinkageSafeBatch hP hcurrent) reserve = ∅ := by
  unfold pendingReserve
  rw [fullLinkageSafeBatch_completedInitials hP hcurrent]
  ext x
  constructor
  · intro hx
    exact (hx.2 (hreserve hx.1)).elim
  · intro hx
    exact hx.elim

/-- In the small-source branch the full linkage is future-safe for every
reserve chosen afterward: all residual source coordinates have completed,
so the next request web has empty source. -/
theorem fullLinkageSafeBatch_futureSafeFor
    {H : DWeb V} {current reserve : Set V} {P : Set H.DPath}
    (hP : IsLinkageBetween H H.source H.target P)
    (hcurrent : current ⊆ H.source) (hreserve : reserve ⊆ H.source) :
    FutureSafeFor (fullLinkageSafeBatch hP hcurrent) reserve := by
  let B := fullLinkageSafeBatch hP hcurrent
  have hpending : pendingReserve B reserve = ∅ :=
    fullLinkageSafeBatch_pendingReserve hP hcurrent hreserve
  exact FullSourceSafeBatch.FutureSafeFor.of_pendingReserve_eq_empty
    B hreserve hpending

/-! ## Extracting a complementary linkage from a structural target row -/

/-- In a normalized web, a finite full-source warp which links a designated
set of source vertices to the target contains an ordinary linkage on exactly
those initial coordinates.  This is the adapter needed when the prospective
complementary linkage is carried by a previous target row rather than already
packaged as `IsLinkageBetween`.

The normalization hypothesis is essential here: `LinksToTarget` only says
that the selected finite component contains a target vertex after the
designated source.  Normalization identifies that target vertex with the
component's terminal vertex and prevents the component from meeting another
ambient source. -/
theorem isLinkageBetween_initialRestriction_of_structural_links
    {H : DWeb V} (hNorm : H.IsNormalized)
    {W : Set H.DPath} (hwarp : H.IsWarp W)
    (hfinite : H.HasFiniteCharacter W)
    (hinitial : H.initialSet W = H.source)
    {A : Set V} (hA : A ⊆ H.source)
    (hlinks : LinksToTarget H W A) :
    IsLinkageBetween H A H.target (initialRestriction H W A) := by
  let R := initialRestriction H W A
  have hRwarp : H.IsWarp R := by
    intro p hp q hq hpq
    exact hwarp hp.1 hq.1 hpq
  have hRfinite : H.HasFiniteCharacter R := by
    intro p hp
    exact hfinite hp.1
  have hRinitial : H.initialSet R = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hp, hpx⟩
      exact hpx ▸ hp.2
    · intro a ha
      have haInitial : a ∈ H.initialSet W := hinitial.symm ▸ hA ha
      obtain ⟨p, hpW, hpa⟩ := haInitial
      exact ⟨p, ⟨hpW, hpa ▸ ha⟩, hpa⟩
  have hRterminal : H.terminalFrontier R ⊆ H.target := by
    rintro x ⟨p, hpR, hpx⟩
    obtain ⟨q, hqW, f, hqf, hpure, before, after, hsupport,
      b, hbTarget, hbAfter⟩ := hlinks p.initial hpR.2
    have haF : p.initial ∈ f.support := by
      have haInter : p.initial ∈ f.support ∩ A := by
        rw [hpure]
        exact Set.mem_singleton p.initial
      exact haInter.1
    have haQ : p.initial ∈ q.support := by
      subst q
      exact haF
    have hpq : p = q := by
      by_contra hpq
      exact Set.disjoint_left.1 (hwarp hpR.1 hqW hpq)
        p.initial_mem_support haQ
    have hbF : b ∈ f.support := by
      change b ∈ f.walk.support
      rw [hsupport]
      exact List.mem_append_right before hbAfter
    have hterminal : H.terminal? (.inl f : H.DPath) = some b :=
      hNorm.terminal?_eq_of_mem_path (.inl f) hbF hbTarget
    have hterminalP : H.terminal? p = some b := by
      calc
        H.terminal? p = H.terminal? q := congrArg H.terminal? hpq
        _ = H.terminal? (.inl f : H.DPath) := congrArg H.terminal? hqf
        _ = some b := hterminal
    have hxb : x = b := by
      exact Option.some.inj (hpx.symm.trans hterminalP)
    exact hxb ▸ hbTarget
  refine ⟨hRwarp, hRfinite, hRinitial, hRterminal, ?_⟩
  intro p hpR
  obtain ⟨f, rfl⟩ := hRfinite hpR
  have hfStartA : f.start ∈ A := hpR.2
  have hsource : f.support ∩ A = {f.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxA⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_start_of_mem_walk f.walk hxf (hA hxA))
    · intro x hx
      have hxf : x = f.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, hfStartA⟩
  have hfFinishTarget : f.finish ∈ H.target := by
    apply hRterminal
    exact ⟨Sum.inl f, hpR, rfl⟩
  have htarget : f.support ∩ H.target = {f.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxTarget⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_finish_of_mem_walk f.walk hxf hxTarget)
    · intro x hx
      have hxf : x = f.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.finish_mem_support, hfFinishTarget⟩
  refine ⟨f, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- Positive selection theorem for every residual web whose whole source is
below the induction cardinal.  The reserve may depend arbitrarily on the
chosen batch (for example, it may include all next target competitors).
The lower extension clause completes the entire residual source, making the
post-choice request web empty and hence safely iterable. -/
theorem exists_jointFutureSafeSelection_of_source_below
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    (hsource : #H.source < kappa)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (reserveAfter : FullSourceSafeBatch H current → Set V)
    (hreserve : ∀ B, reserveAfter B ⊆ H.source) :
    Nonempty (JointFutureSafeSelection H current reserveAfter) := by
  have hext : ExtensionClauseAt H #H.source :=
    (hlower #H.source hsource H hH).extension
  obtain ⟨P, hP⟩ := linkable_of_extension_at_source_card H hext
  let B := fullLinkageSafeBatch hP hcurrent
  exact ⟨⟨B, fullLinkageSafeBatch_futureSafeFor
    hP hcurrent (hreserve B)⟩⟩

/-- A large ambient source causes no future-safety difficulty when the
sources outside the current row are already linked to the target.  The
lower extension clause at the exact cardinality of `current` then upgrades
that complementary linkage to a full source--target linkage.  Viewing the
full linkage as a batch completes every reserve coordinate, so an arbitrary
post-choice reserve rule is safe.

This is the strongest direct batch consequence available from the lower
induction hypotheses.  In particular, Theorem 6.1 alone supplies only one
safely deletable target path and does not provide the complementary linkage
required here for an uncountable current row. -/
theorem exists_jointFutureSafeSelection_of_complement_linkable
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
    Nonempty (JointFutureSafeSelection H current reserveAfter) := by
  have hext : ExtensionClauseAt H rho :=
    (hlower rho hrhoKappa H hH).extension
  have hlinkable : IsLinkable H :=
    hext current hcurrent hcurrentCard hcomplement
  obtain ⟨P, hP⟩ := hlinkable
  let B := fullLinkageSafeBatch hP hcurrent
  exact ⟨⟨B, fullLinkageSafeBatch_futureSafeFor
    hP hcurrent (hreserve B)⟩⟩

/-- Structural-row form of
`exists_jointFutureSafeSelection_of_complement_linkable`.  A previous row
closes the large-source branch whenever it already links every source outside
`current` to the target.  The theorem deliberately keeps that last premise
explicit: ordinary target rows only link their designated source set, so the
generic singular machine does not supply it for `H.source \ current`. -/
theorem exists_jointFutureSafeSelection_of_structural_complement_links
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
    Nonempty (JointFutureSafeSelection H current reserveAfter) := by
  refine exists_jointFutureSafeSelection_of_complement_linkable
    hlower hrhoKappa hH hcurrent hcurrentCard ?_ reserveAfter hreserve
  exact ⟨initialRestriction H W (H.source \ current),
    isLinkageBetween_initialRestriction_of_structural_links
      hNorm hwarp hfinite hinitial Set.sdiff_subset hcomplementLinks⟩

/-- The lower induction hypotheses reduce future-safe selection to the only
genuinely difficult case: the residual source still has at least the current
singular scale.  Below that scale, the preceding full-linkage construction
already supplies the joint post-choice fixed point. -/
theorem jointFutureSafeSelection_or_scale_le_source
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrhoKappa : rho < kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (reserveAfter : FullSourceSafeBatch H current → Set V)
    (hreserve : ∀ B, reserveAfter B ⊆ H.source) :
    Nonempty (JointFutureSafeSelection H current reserveAfter) ∨
      rho ≤ #H.source := by
  by_cases hlarge : rho ≤ #H.source
  · exact Or.inr hlarge
  · apply Or.inl
    apply exists_jointFutureSafeSelection_of_source_below
      hlower hH ((lt_of_not_ge hlarge).trans hrhoKappa)
      hcurrent reserveAfter hreserve

/-- Sharpened source-size reduction.  Equality with the scale is already a
small-source case because the scale itself is below `kappa`; consequently
the unresolved branch has *strictly* more ambient sources than the current
scale. -/
theorem jointFutureSafeSelection_or_scale_lt_source
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrhoKappa : rho < kappa)
    {H : DWeb V} (hH : H.IsUnhindered)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (reserveAfter : FullSourceSafeBatch H current → Set V)
    (hreserve : ∀ B, reserveAfter B ⊆ H.source) :
    Nonempty (JointFutureSafeSelection H current reserveAfter) ∨
      rho < #H.source := by
  by_cases hlarge : rho < #H.source
  · exact Or.inr hlarge
  · apply Or.inl
    apply exists_jointFutureSafeSelection_of_source_below
      hlower hH ((le_of_not_gt hlarge).trans_lt hrhoKappa)
      hcurrent reserveAfter hreserve

end SingularFutureSafeBatch
end CardinalInduction
end Erdos599
