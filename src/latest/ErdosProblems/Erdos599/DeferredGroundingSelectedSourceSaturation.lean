/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceOwnerRebase

/-!
# Saturating a selected route at all grounded reference owners

Successively rebasing a selected route at source-grounded owners is most
cleanly compiled by taking one final contact with their whole carrier.  The
remaining loop-erased suffix then has no forward edge on any source-grounded
member of the actual truncated reference warp.  If the final contact moves,
its projected vertex-chain length decreases strictly; otherwise the route was
already saturated.

This is the finite potential behind the source-owner part of the simultaneous
transaction.  It retains the literal owner and source prefix, rather than
postulating termination of an abstract exchange process.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

namespace ReservedStrongSelectedStartingLastContact

variable {r : Request (popularAuxiliaryInput L hL.legal) S.cut}

/-- The actual truncated-warp members whose initial vertex is an ambient
source. -/
def sourceGroundedOwners
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) : Set Gamma.DPath :=
  {Y | Y ∈ X.truncatedWarp ∧ Y.initial ∈ Gamma.source}

/-- Their whole carrier. -/
def sourceGroundedCarrier
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) : Set V :=
  Gamma.vertexSet X.sourceGroundedOwners

/-- The final contact with all source-grounded reference owners, together
with the literal owner and its ambient-source prefix. -/
structure SourceSaturation
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) where
  contact : X.remainingErasedRoute.LastContact X.sourceGroundedCarrier
  owner : Gamma.DPath
  owner_mem : owner ∈ X.truncatedWarp
  owner_source : owner.initial ∈ Gamma.source
  contact_mem_owner : contact.vertex ∈ owner.support
  ownerPrefix : FinitePath Gamma.graph
  prefix_start : ownerPrefix.start = owner.initial
  prefix_source : ownerPrefix.start ∈ Gamma.source
  prefix_finish : ownerPrefix.finish = contact.vertex
  prefix_support : ownerPrefix.support ⊆ owner.support
  prefix_edges : ownerPrefix.edgeSet ⊆ owner.edgeSet

namespace SourceSaturation

/-- If the initial vertex of a compatible finite trace lies on a forward
link, then that link must be the first one and the first direction is
forward.  A later return to the first entry is excluded by compatibility. -/
theorem firstLink_forward_of_initial_mem_forward
    (Q : FiniteTrace Gamma.graph)
    (hiForward : Q.initial ∈
      (AltPath.finite Q).directionVertices .forward) :
    Q.firstLink.direction = .forward := by
  cases hfirst : Q.firstLink.direction with
  | forward => rfl
  | backward =>
      simp only [AltPath.directionVertices, AltPath.links,
        FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hiForward
      obtain ⟨_f, ⟨j, rfl⟩, hjdir, hiJ⟩ := hiForward
      let k : Fin (Q.lastIndex + 1) :=
        ⟨0, Nat.zero_lt_succ _⟩
      have hkfirst : Q.link k = Q.firstLink := rfl
      have hkj : k < j := by
        have hkle : k.1 ≤ j.1 := Nat.zero_le _
        rcases lt_or_eq_of_le hkle with hkj | hkj
        · exact hkj
        · have hkjeq : k = j := Fin.ext hkj
          subst j
          exact (by simp [hkfirst, hfirst] at hjdir)
      have hc := Q.compatible k j hkj
      simp only [hkfirst, hfirst, hjdir, CompatibleInOrder] at hc
      have hiL : Q.initial ∈ Q.firstLink.path.support :=
        Q.firstLink.entry_mem_support
      by_cases hadj : j.1 = k.1 + 1
      · rcases hc.1 hadj hiL hiJ with hiexit | hiinterior
        · exact False.elim (Q.firstLink.entry_ne_exit hiexit)
        · exact False.elim
            (Q.firstLink.entry_not_mem_interior hiinterior.1)
      · have hiinterior := hc.2 hadj ⟨hiL, hiJ⟩
        exact False.elim
          (Q.firstLink.entry_not_mem_interior hiinterior.1)

/-- The remaining raw route after the simultaneous source-owner final
contact. -/
noncomputable def remainingSuffix
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :=
  X.remainingErasedRoute.suffixFrom D.contact.vertex
    D.contact.vertex_mem_chain

private theorem remainingSuffix_valid
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    {s : SignedEdge V} (hs : s ∈ D.remainingSuffix.steps) :
    SignedEdge.Valid (Gamma := Gamma) s := by
  exact X.remainingErasedRoute_valid
    (X.remainingErasedRoute.suffixFrom_steps_subset
      D.contact.vertex D.contact.vertex_mem_chain hs)

/-- Honest alternating compression of the saturated suffix. -/
noncomputable def normalizedSuffix
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    ErasedSignedRoute.ErasedCompression (Gamma := Gamma) D.remainingSuffix :=
  D.remainingSuffix.compressionOfValid fun {_s} hs ↦
    D.remainingSuffix_valid hs

@[simp] theorem normalizedSuffix_initial
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    D.normalizedSuffix.path.initial = D.contact.vertex :=
  D.normalizedSuffix.initial_eq

@[simp] theorem normalizedSuffix_terminal
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    D.normalizedSuffix.path.terminal? = some (requestExit r) :=
  D.normalizedSuffix.terminal_eq

/-- The saturated compression is a literal suffix of the original
own-start-normalized compression, with directions unchanged. -/
theorem normalizedSuffix_directionEdges_subset_startingSuffix
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) (d : Direction) :
    D.normalizedSuffix.path.directionEdges d ⊆
      X.normalizedSuffix.path.directionEdges d := by
  have hsubset :=
    X.remainingErasedRoute.suffixCompressionOfValid_directionEdges_subset
      D.contact.vertex D.contact.vertex_mem_chain
      (fun {_s} hs ↦ X.remainingErasedRoute_valid hs) d
  simpa only [normalizedSuffix, remainingSuffix,
    ReservedStrongSelectedStartingLastContact.normalizedSuffix,
    ErasedSignedRoute.LastContact.suffixCompressionOfValid,
    ErasedSignedRoute.suffixCompressionOfValid,
    ReservedStrongSelectedStartingLastContact.remainingErasedRoute] using
      hsubset

/-- Vertex support of the saturated compression is contained in the
original own-start-normalized compression. -/
theorem normalizedSuffix_vertexSet_subset_startingSuffix
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    D.normalizedSuffix.path.vertexSet ⊆
      X.normalizedSuffix.path.vertexSet := by
  intro v hv
  have hvRemaining : v ∈ D.remainingSuffix.vertexChain :=
    D.remainingSuffix.compressionOfValid_vertexSet_subset_vertexChain
      (fun {_s} hs ↦ D.remainingSuffix_valid hs) hv
  have hvStarting : v ∈ X.remainingErasedRoute.vertexChain :=
    X.remainingErasedRoute.suffixFrom_vertexChain_subset
      D.contact.vertex D.contact.vertex_mem_chain hvRemaining
  rw [X.normalizedSuffix_vertexSet_eq_remainingChain]
  exact hvStarting

/-- No point of the saturated suffix can return to any source-grounded
reference owner away from the final contact. -/
theorem eq_contact_of_mem_suffix_of_mem_sourceGroundedCarrier
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {v : V}
    (hvSuffix : v ∈ D.remainingSuffix.vertexChain)
    (hvGrounded : v ∈ X.sourceGroundedCarrier) :
    v = D.contact.vertex := by
  exact D.contact.eq_vertex_of_mem_suffix_vertexChain_of_mem
    hvSuffix hvGrounded

/-- The same no-return statement for the honest alternating compression. -/
theorem eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {v : V}
    (hvSuffix : v ∈ D.normalizedSuffix.path.vertexSet)
    (hvGrounded : v ∈ X.sourceGroundedCarrier) :
    v = D.contact.vertex := by
  apply D.eq_contact_of_mem_suffix_of_mem_sourceGroundedCarrier
    _ hvGrounded
  exact D.remainingSuffix.compressionOfValid_vertexSet_subset_vertexChain
    (fun {_s} hs ↦ D.remainingSuffix_valid hs) hvSuffix

/-- Saturation removes every forward reference edge on every
source-grounded owner of the actual truncated warp. -/
theorem forwardLinksOff_sourceGroundedOwners
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    ForwardLinksOff X.sourceGroundedOwners D.normalizedSuffix.path := by
  intro l hl hdir
  rw [Set.disjoint_left]
  intro e heLink heFamily
  simp only [Alternating.familyEdges, Set.mem_iUnion] at heFamily
  obtain ⟨Y, hYGrounded, heY⟩ := heFamily
  have heEndsSuffix := l.path.edgeSet_subset_support_prod heLink
  have htailSuffix : e.1 ∈ D.normalizedSuffix.path.vertexSet :=
    D.normalizedSuffix.path.link_support_subset_vertexSet
      hl heEndsSuffix.1
  have hheadSuffix : e.2 ∈ D.normalizedSuffix.path.vertexSet :=
    D.normalizedSuffix.path.link_support_subset_vertexSet
      hl heEndsSuffix.2
  have heEndsY := Y.edgeSet_subset_support_prod heY
  have htailGrounded : e.1 ∈ X.sourceGroundedCarrier := by
    exact ⟨Y, hYGrounded, heEndsY.1⟩
  have hheadGrounded : e.2 ∈ X.sourceGroundedCarrier := by
    exact ⟨Y, hYGrounded, heEndsY.2⟩
  have htail :=
    D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
      htailSuffix htailGrounded
  have hhead :=
    D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
      hheadSuffix hheadGrounded
  exact (path_edge_ne_of_mem Y heY) (htail.trans hhead.symm)

/-- The final-contact saturation is either already at the current route
initial, or strictly decreases the literal projected vertex-chain length. -/
theorem contact_eq_initial_or_suffix_vertexChain_lt
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    D.contact.vertex = X.lastContact.vertex ∨
      D.remainingSuffix.vertexChain.length <
        X.remainingErasedRoute.vertexChain.length := by
  by_cases hEq : D.contact.vertex = X.lastContact.vertex
  · exact Or.inl hEq
  · exact Or.inr
      (X.suffix_vertexChain_length_lt_of_lastContact_ne_initial
        D.contact hEq)

/-- Replace the final source-grounded owner by its retained prefix. -/
def saturatedWarp
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) : Set Gamma.DPath :=
  insert (.inl D.ownerPrefix : Gamma.DPath)
    (X.truncatedWarp \ {D.owner})

/-- The source-grounded part of the *new* saturated reference warp. -/
def saturatedSourceGroundedOwners
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) : Set Gamma.DPath :=
  {Y | Y ∈ D.saturatedWarp ∧ Y.initial ∈ Gamma.source}

/-- The source-owner prefix replacement remains a warp. -/
theorem saturatedWarp_isWarp
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    Gamma.IsWarp D.saturatedWarp := by
  apply DWeb.IsWarp.insert_finite_of_disjoint Gamma
    (DWeb.IsWarp.sdiff_singleton Gamma X.truncatedWarp_isWarp D.owner)
      D.ownerPrefix
  rw [Set.disjoint_left]
  intro x hxPrefix hxRest
  obtain ⟨p, hpRest, hxp⟩ := hxRest
  have hne : D.owner ≠ p := by
    intro hEq
    subst p
    exact hpRest.2 (Set.mem_singleton D.owner)
  exact Set.disjoint_left.mp
    (X.truncatedWarp_isWarp D.owner_mem hpRest.1 hne)
      (D.prefix_support hxPrefix) hxp

/-- Saturation changes no reference initial: the removed owner and inserted
prefix have the same ambient-source initial. -/
theorem saturatedWarp_initialSet
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    Gamma.initialSet D.saturatedWarp = Gamma.initialSet X.truncatedWarp := by
  rw [saturatedWarp, Gamma.initialSet_insert_finite,
    DWeb.IsWarp.initialSet_sdiff_singleton Gamma
      X.truncatedWarp_isWarp D.owner_mem,
    D.prefix_start]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | hx)
    · exact ⟨D.owner, D.owner_mem, rfl⟩
    · exact hx.1
  · intro hx
    by_cases hxeq : x = D.owner.initial
    · exact Or.inl hxeq
    · exact Or.inr ⟨hx, hxeq⟩

/-- The final source-grounded contact is a literal reference terminal for
the saturated route. -/
theorem normalizedSuffix_initial_mem_terminalFrontier
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    D.normalizedSuffix.path.initial ∈
      Gamma.terminalFrontier D.saturatedWarp := by
  rw [D.normalizedSuffix_initial]
  exact ⟨.inl D.ownerPrefix, Set.mem_insert _ _,
    congrArg some D.prefix_finish⟩

/-- The no-forward-reference conclusion also includes the newly inserted
source prefix.  Its support lies in the named old owner, which was already
part of the final-contact carrier. -/
theorem forwardLinksOff_saturatedSourceGroundedOwners
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    ForwardLinksOff D.saturatedSourceGroundedOwners
      D.normalizedSuffix.path := by
  intro l hl hdir
  rw [Set.disjoint_left]
  intro e heLink heFamily
  simp only [Alternating.familyEdges, Set.mem_iUnion] at heFamily
  obtain ⟨Y, hYGrounded, heY⟩ := heFamily
  have heEndsSuffix := l.path.edgeSet_subset_support_prod heLink
  have htailSuffix : e.1 ∈ D.normalizedSuffix.path.vertexSet :=
    D.normalizedSuffix.path.link_support_subset_vertexSet
      hl heEndsSuffix.1
  have hheadSuffix : e.2 ∈ D.normalizedSuffix.path.vertexSet :=
    D.normalizedSuffix.path.link_support_subset_vertexSet
      hl heEndsSuffix.2
  have heEndsY := Y.edgeSet_subset_support_prod heY
  have hYCarrier : Y.support ⊆ X.sourceGroundedCarrier := by
    intro v hv
    have hYCases : Y = (.inl D.ownerPrefix : Gamma.DPath) ∨
        Y ∈ X.truncatedWarp \ {D.owner} := by
      simpa only [saturatedSourceGroundedOwners, saturatedWarp,
        Set.mem_insert_iff] using hYGrounded.1
    rcases hYCases with hPrefix | hOld
    · subst Y
      exact ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩,
        D.prefix_support hv⟩
    · exact ⟨Y, ⟨hOld.1, hYGrounded.2⟩, hv⟩
  have htail :=
    D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
      htailSuffix (hYCarrier heEndsY.1)
  have hhead :=
    D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
      hheadSuffix (hYCarrier heEndsY.2)
  exact (path_edge_ne_of_mem Y heY) (htail.trans hhead.symm)

/-- Removing the temporary saturation contact leaves exactly the old
truncated-warp frontier with the selected source owner removed.  This is the
literal sink trade performed by the source-owner transaction. -/
theorem terminalFrontier_saturatedWarp_sdiff_contact
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    Gamma.terminalFrontier D.saturatedWarp \ {D.contact.vertex} =
      Gamma.terminalFrontier (X.truncatedWarp \ {D.owner}) := by
  let rest := X.truncatedWarp \ {D.owner}
  have hcontactNotRest : D.contact.vertex ∉
      Gamma.terminalFrontier rest := by
    rintro ⟨p, hpRest, hpTerminal⟩
    have hne : D.owner ≠ p := by
      intro hEq
      subst p
      exact hpRest.2 (Set.mem_singleton D.owner)
    exact Set.disjoint_left.mp
      (X.truncatedWarp_isWarp D.owner_mem hpRest.1 hne)
        D.contact_mem_owner (Gamma.terminal_mem_support hpTerminal)
  change Gamma.terminalFrontier
      (insert (.inl D.ownerPrefix : Gamma.DPath) rest) \
        {D.contact.vertex} = Gamma.terminalFrontier rest
  rw [Gamma.terminalFrontier_insert_finite, D.prefix_finish]
  ext x
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hxne⟩
    · exact False.elim (hxne hx)
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, fun hEq ↦ hcontactNotRest (hEq ▸ hx)⟩

/-- Every saturated backward run is still owned by the saturated reference
warp.  If it belonged to the removed source-grounded owner, both endpoints
would occur after the final contact on that owner and hence coincide. -/
theorem normalizedSuffix_backwardLinksOn_saturatedWarp
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    BackwardLinksOn D.saturatedWarp D.normalizedSuffix.path := by
  apply D.remainingSuffix.compressionOfValid_backwardLinksOn
    (fun {_s} hs ↦ D.remainingSuffix_valid hs)
    D.saturatedWarp_isWarp
  intro s hs hdir
  have heD : s.edge ∈ D.normalizedSuffix.path.directionEdges .backward := by
    apply D.remainingSuffix
      |>.directedSignedEdgeSet_subset_compressionOfValid_directionEdges
        (fun {_s} hs' ↦ D.remainingSuffix_valid hs') .backward
    exact ⟨s, hs, hdir, rfl⟩
  have heX : s.edge ∈ X.normalizedSuffix.path.directionEdges .backward :=
    D.normalizedSuffix_directionEdges_subset_startingSuffix .backward heD
  have heFamily : s.edge ∈ Alternating.familyEdges X.truncatedWarp :=
    X.normalizedSuffix_backwardLinksOn_truncatedWarp
      |>.directionEdges_subset_familyEdges heX
  simp only [Alternating.familyEdges, Set.mem_iUnion] at heFamily ⊢
  obtain ⟨Y, hY, heY⟩ := heFamily
  by_cases hEq : Y = D.owner
  · subst Y
    have heEnds := D.owner.edgeSet_subset_support_prod heY
    have hePath : s.edge ∈ D.normalizedSuffix.path.edgeSet := by
      rw [D.normalizedSuffix.path.edgeSet_eq_directionEdges_union]
      exact Or.inr heD
    have heChain := D.remainingSuffix
      |>.compressionOfValid_edge_endpoints_mem_vertexChain
        (fun {_s} hs' ↦ D.remainingSuffix_valid hs')
        hePath
    have htailCarrier : s.edge.1 ∈ X.sourceGroundedCarrier :=
      ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩, heEnds.1⟩
    have hheadCarrier : s.edge.2 ∈ X.sourceGroundedCarrier :=
      ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩, heEnds.2⟩
    have htail := D.eq_contact_of_mem_suffix_of_mem_sourceGroundedCarrier
      heChain.1 htailCarrier
    have hhead := D.eq_contact_of_mem_suffix_of_mem_sourceGroundedCarrier
      heChain.2 hheadCarrier
    exact False.elim
      ((path_edge_ne_of_mem D.owner heY) (htail.trans hhead.symm))
  · exact ⟨Y, Set.mem_insert_of_mem _ ⟨hY, by
      simpa only [Set.mem_singleton_iff] using hEq⟩, heY⟩

/-- Unless the saturated contact is already the request exit, the remaining
route is a genuine finite alternating trace with the exact endpoints. -/
theorem exists_finite_normalizedSuffix_of_contact_ne_exit
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (hne : D.contact.vertex ≠ requestExit r) :
    ∃ Q : FiniteTrace Gamma.graph,
      D.normalizedSuffix.path = .finite Q ∧
        Q.initial = D.contact.vertex ∧
        Q.terminal = requestExit r := by
  have hinitial := D.normalizedSuffix_initial
  have hterminal := D.normalizedSuffix_terminal
  cases hpath : D.normalizedSuffix.path with
  | trivial x =>
      have hxContact : x = D.contact.vertex := by
        simpa only [hpath, AltPath.initial] using hinitial
      have hxExit : x = requestExit r := by
        exact Option.some.inj (by
          simpa only [hpath, AltPath.terminal?] using hterminal)
      exact False.elim (hne (hxContact.symm.trans hxExit))
  | finite Q =>
      refine ⟨Q, rfl, ?_, ?_⟩
      · simpa only [hpath, AltPath.initial] using hinitial
      · exact Option.some.inj (by
          simpa only [hpath, AltPath.terminal?] using hterminal)
  | infinite ray =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa only [hpath, AltPath.terminal?] using hterminal
      cases hfalse

/-- After simultaneous source-owner saturation, the actual route still
enters the genuine terminal-contact trichotomy at its essential terminal
owner.  All backward-link and source-initial obligations are proved for the
new reference warp, not transported as assumptions. -/
theorem terminalContactGeometryOutcome_on_saturatedWarp
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (popularAuxiliaryInput L hL.legal).essentialLadder)
    (hexit : requestExit r = Z.initial)
    (hne : D.contact.vertex ≠ requestExit r) :
    ∃ Q : FiniteTrace Gamma.graph,
      D.normalizedSuffix.path = .finite Q ∧
        Q.initial = D.contact.vertex ∧
        Q.terminal = requestExit r ∧
        TerminalContactGeometryOutcome
          D.saturatedWarp Q (requestExit r) := by
  obtain ⟨Q, hQ, hQInitial, hQTerminal⟩ :=
    D.exists_finite_normalizedSuffix_of_contact_ne_exit hne
  have hZEssential : Z ∈ Gamma.essentialWarpPart L.limitWarp := by
    simpa only [popularAuxiliaryInput,
      PopularAuxiliary.Input.essentialLadder, limitWarp] using hZ
  have hZNe : Z ≠ (reservedStrongSelectedStartingRecord r).record := by
    intro hEq
    subst Z
    exact (reservedStrongSelectedStartingRecord r).limit_inessential.2
      hZEssential
  have hExitInitialX : requestExit r ∈
      Gamma.initialSet X.truncatedWarp := by
    rw [hexit]
    exact X.terminalOwner_initial_mem_truncatedWarp
      hZEssential.1 hZNe
  have hExitInitial : requestExit r ∈
      Gamma.initialSet D.saturatedWarp := by
    rw [D.saturatedWarp_initialSet]
    exact hExitInitialX
  have hQInitialCarrier : Q.initial ∈
      Gamma.vertexSet D.saturatedWarp := by
    rw [hQInitial]
    rw [← D.normalizedSuffix_initial]
    exact terminalFrontier_subset_vertexSet _
      D.normalizedSuffix_initial_mem_terminalFrontier
  have hback : BackwardLinksOn D.saturatedWarp (.finite Q) := by
    have h := D.normalizedSuffix_backwardLinksOn_saturatedWarp
    rw [hQ] at h
    exact h
  have hnoForward : ∀ z,
      (requestExit r, z) ∉
        (AltPath.finite Q).directionEdges .forward := by
    intro z hz
    have hno := selectedErasedCompression_noOutgoing_forward_at_requestExit
      U S K r
    apply hno
    refine ⟨z, ?_⟩
    apply X.normalizedSuffix_directionEdges_subset_selected .forward
    apply D.normalizedSuffix_directionEdges_subset_startingSuffix .forward
    rw [hQ]
    exact hz
  have hout := finiteSourceTerminalOutcome_of_geometry
    D.saturatedWarp_isWarp hback hQInitialCarrier hExitInitial
      (by simpa only [hQInitial] using hne) hQTerminal hnoForward
  exact ⟨Q, hQ, hQInitial, hQTerminal, hout⟩

/-- In the canonical deferred ladder, a forward-reference failure remaining
after source saturation cannot have a source-grounded owner.  Its literal
reference owner is therefore exactly the terminal component or an already
inessential limiting component. -/
theorem canonicalDeferredLadder_saturatedForwardReference_terminal_or_inessential
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (X : ReservedStrongSelectedStartingLastContact
      (L := canonicalDeferredLadder Gamma kappa preferred)
      (hL := hL) (S := S) r)
    (D : SourceSaturation X)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (hnot : ¬ ForwardLinksOff D.saturatedWarp D.normalizedSuffix.path) :
    ∃ e : V × V, ∃ Y : Gamma.DPath,
      e ∈ D.normalizedSuffix.path.directionEdges .forward ∧
        Y ∈ D.saturatedWarp ∧ e ∈ Y.edgeSet ∧
        (Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  simp only [ForwardLinksOff, not_forall] at hnot
  obtain ⟨l, hl, hldir, hnotDisjoint⟩ := hnot
  obtain ⟨e, hel, heFamily⟩ := Set.not_disjoint_iff.1 hnotDisjoint
  simp only [Alternating.familyEdges, Set.mem_iUnion] at heFamily
  obtain ⟨Y, hY, heY⟩ := heFamily
  have heForward : e ∈ D.normalizedSuffix.path.directionEdges .forward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hel⟩
  have hYNotSource : Y.initial ∉ Gamma.source := by
    intro hYSource
    have hYGrounded : Y ∈ D.saturatedSourceGroundedOwners :=
      ⟨hY, hYSource⟩
    have heGrounded : e ∈
        Alternating.familyEdges D.saturatedSourceGroundedOwners := by
      simp only [Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨Y, hYGrounded, heY⟩
    exact Set.disjoint_left.mp
      (D.forwardLinksOff_saturatedSourceGroundedOwners l hl hldir)
        hel heGrounded
  have hYCases : Y = (.inl D.ownerPrefix : Gamma.DPath) ∨
      Y ∈ X.truncatedWarp \ {D.owner} := by
    simpa only [saturatedWarp, Set.mem_insert_iff] using hY
  have hYOld : Y ∈ X.truncatedWarp := by
    rcases hYCases with hPrefix | hOld
    · subst Y
      exact False.elim (hYNotSource D.prefix_source)
    · exact hOld.1
  have heXForward : e ∈ X.normalizedSuffix.path.directionEdges .forward :=
    D.normalizedSuffix_directionEdges_subset_startingSuffix .forward heForward
  have heXPath : e ∈ X.normalizedSuffix.path.edgeSet := by
    rw [X.normalizedSuffix.path.edgeSet_eq_directionEdges_union]
    exact Or.inl heXForward
  have heEndsX :=
    X.normalizedSuffix.path.edgeSet_subset_vertexSet_prod heXPath
  have heEndsY := Y.edgeSet_subset_support_prod heY
  have howner :=
    canonicalDeferredLadder_truncatedOwner_grounded_or_terminal_or_inessential
      preferred hkappa huncountable hNoEnter hL S r X Z hZ hexit
        Y hYOld heEndsX.1 heEndsY.1
  refine ⟨e, Y, heForward, hY, heY, ?_⟩
  rcases howner with hYSource | hterminal | hinessential
  · exact False.elim (hYNotSource hYSource)
  · exact Or.inl hterminal
  · exact Or.inr hinessential

/-- The uncovered-forward-contact arm after source saturation has only one
source-grounded possibility: the literal new splice contact itself.  Every
other contacted owner is the terminal component or already inessential. -/
theorem canonicalDeferredLadder_saturatedUncoveredForward_contact_or_terminal_or_inessential
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (X : ReservedStrongSelectedStartingLastContact
      (L := canonicalDeferredLadder Gamma kappa preferred)
      (hL := hL) (S := S) r)
    (D : SourceSaturation X)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (hnot : ¬ ForwardVertexContactsCoveredAtTerminal
      Gamma D.saturatedWarp D.normalizedSuffix.path) :
    ∃ x : V, ∃ Y : Gamma.DPath,
      x ∈ D.normalizedSuffix.path.directionVertices .forward ∧
        Y ∈ D.saturatedWarp ∧ x ∈ Y.support ∧
        x ∉ D.normalizedSuffix.path.directionVertices .backward ∧
        D.normalizedSuffix.path.terminal? ≠ some x ∧
        (x = D.contact.vertex ∨ Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  simp only [ForwardVertexContactsCoveredAtTerminal, not_forall,
    not_or] at hnot
  obtain ⟨x, hxForward, hxWarp, hxNotBackward, hxNotTerminal⟩ := hnot
  obtain ⟨Y, hY, hxY⟩ := hxWarp
  refine ⟨x, Y, hxForward, hY, hxY, hxNotBackward, hxNotTerminal, ?_⟩
  by_cases hYSource : Y.initial ∈ Gamma.source
  · have hYCarrier : Y.support ⊆ X.sourceGroundedCarrier := by
      intro v hv
      have hYCases : Y = (.inl D.ownerPrefix : Gamma.DPath) ∨
          Y ∈ X.truncatedWarp \ {D.owner} := by
        simpa only [saturatedWarp, Set.mem_insert_iff] using hY
      rcases hYCases with hPrefix | hOld
      · subst Y
        exact ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩,
          D.prefix_support hv⟩
      · exact ⟨Y, ⟨hOld.1, hYSource⟩, hv⟩
    have hxSuffix : x ∈ D.normalizedSuffix.path.vertexSet := by
      simp only [AltPath.directionVertices, Set.mem_iUnion] at hxForward
      obtain ⟨l, hl, _hdir, hxl⟩ := hxForward
      exact D.normalizedSuffix.path.link_support_subset_vertexSet hl hxl
    exact Or.inl
      (D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
        hxSuffix (hYCarrier hxY))
  · have hYCases : Y = (.inl D.ownerPrefix : Gamma.DPath) ∨
        Y ∈ X.truncatedWarp \ {D.owner} := by
      simpa only [saturatedWarp, Set.mem_insert_iff] using hY
    have hYOld : Y ∈ X.truncatedWarp := by
      rcases hYCases with hPrefix | hOld
      · subst Y
        exact False.elim (hYSource D.prefix_source)
      · exact hOld.1
    have hxSuffixD : x ∈ D.normalizedSuffix.path.vertexSet := by
      simp only [AltPath.directionVertices, Set.mem_iUnion] at hxForward
      obtain ⟨l, hl, _hdir, hxl⟩ := hxForward
      exact D.normalizedSuffix.path.link_support_subset_vertexSet hl hxl
    have hxSuffixX : x ∈ X.normalizedSuffix.path.vertexSet :=
      D.normalizedSuffix_vertexSet_subset_startingSuffix hxSuffixD
    have howner :=
      canonicalDeferredLadder_truncatedOwner_grounded_or_terminal_or_inessential
        preferred hkappa huncountable hNoEnter hL S r X Z hZ hexit
          Y hYOld hxSuffixX hxY
    rcases howner with hsource | hterminal | hinessential
    · exact False.elim (hYSource hsource)
    · exact Or.inr (Or.inl hterminal)
    · exact Or.inr (Or.inr hinessential)

/-- In the exceptional uncovered-contact case at the saturated splice
itself, the first selected link is forward and appends literally to the
ambient-source owner prefix.  Hence the transaction makes a concrete
source-root advance to the first-link exit. -/
theorem exists_sourcePath_to_firstLinkExit_of_contact_forward
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q)
    (hcontactForward : D.contact.vertex ∈
      D.normalizedSuffix.path.directionVertices .forward) :
    ∃ p : FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧
        p.finish = Q.firstLink.exit ∧
        p.support = D.ownerPrefix.support ∪ Q.firstLink.path.support := by
  have hQInitial : Q.initial = D.contact.vertex := by
    have h := D.normalizedSuffix_initial
    rw [hQ] at h
    simpa only [AltPath.initial] using h
  have hiForward : Q.initial ∈
      (AltPath.finite Q).directionVertices .forward := by
    rw [hQ] at hcontactForward
    exact hQInitial.symm ▸ hcontactForward
  have hfirst : Q.firstLink.direction = .forward :=
    firstLink_forward_of_initial_mem_forward Q hiForward
  have hjoin : Q.firstLink.path.start = D.ownerPrefix.finish := by
    calc
      Q.firstLink.path.start = Q.firstLink.entry := by
        simp only [Link.entry, hfirst]
      _ = Q.initial := rfl
      _ = D.contact.vertex := hQInitial
      _ = D.ownerPrefix.finish := D.prefix_finish.symm
  have hinter : D.ownerPrefix.support ∩ Q.firstLink.path.support ⊆
      {D.ownerPrefix.finish} := by
    intro v hv
    have hfirstMem : Q.firstLink ∈ (AltPath.finite Q).links := by
      simp only [AltPath.links, FiniteTrace.links, Set.mem_range]
      exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
    have hvSuffix : v ∈ D.normalizedSuffix.path.vertexSet := by
      rw [hQ]
      exact (AltPath.finite Q).link_support_subset_vertexSet
        hfirstMem hv.2
    have hvCarrier : v ∈ X.sourceGroundedCarrier :=
      ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩,
        D.prefix_support hv.1⟩
    have hvEq :=
      D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
        hvSuffix hvCarrier
    rw [D.prefix_finish]
    simpa only [Set.mem_singleton_iff] using hvEq
  let p := D.ownerPrefix.appendFinite Q.firstLink.path hjoin hinter
  refine ⟨p, ?_, ?_, ?_⟩
  · change (D.ownerPrefix.appendFinite Q.firstLink.path
      hjoin hinter).start ∈ Gamma.source
    rw [FinitePath.appendFinite_start]
    exact D.prefix_source
  · change (D.ownerPrefix.appendFinite Q.firstLink.path
      hjoin hinter).finish = Q.firstLink.exit
    rw [FinitePath.appendFinite_finish]
    simp only [Link.exit, hfirst]
  · exact D.ownerPrefix.support_appendFinite_eq_union
      Q.firstLink.path hjoin hinter

/-- A successful terminal-contact switch after source saturation has the
exact initial and terminal balance needed by the finite sink transaction:
the request exit is consumed as an initial, and the only old frontier
contribution removed is that of the saturated source owner. -/
theorem exists_terminalContactSwitchWarp
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (Q : FiniteTrace Gamma.graph)
    (hQInitial : Q.initial = D.contact.vertex)
    (hswitch : IsTerminalContactSwitching
      D.saturatedWarp Q (requestExit r)) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          Gamma.initialSet X.truncatedWarp \ {requestExit r} ∧
        Gamma.terminalFrontier W =
          Gamma.terminalFrontier (X.truncatedWarp \ {D.owner}) := by
  have hcontactTerminal : D.contact.vertex ∈
      Gamma.terminalFrontier D.saturatedWarp := by
    rw [← D.normalizedSuffix_initial]
    exact D.normalizedSuffix_initial_mem_terminalFrontier
  obtain ⟨W, hW, hWInitial, hWTerminal⟩ :=
    TerminalContactSwitch.exists_terminalContactSwitch_anyWarp
      D.saturatedWarp Q (requestExit r) D.contact.vertex
        hswitch hcontactTerminal hQInitial
  refine ⟨W, hW, ?_, ?_⟩
  · rw [hWInitial, D.saturatedWarp_initialSet]
  · rw [hWTerminal, D.terminalFrontier_saturatedWarp_sdiff_contact]

/-- The saturated terminal-contact transaction leaves every old frontier
sink other than the explicitly removed source owner's own endpoint rooted
in the literal switched relation.  Thus the source-owner saturation does
not start an anonymous chain of displaced covered sinks: its only possible
trade is the named owner `D.owner`. -/
theorem terminalContactSwitch_roots_untouchedFrontier
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (Q : FiniteTrace Gamma.graph)
    (hQInitial : Q.initial = D.contact.vertex)
    (hswitch : IsTerminalContactSwitching
      D.saturatedWarp Q (requestExit r)) :
    ∀ t ∈ Gamma.terminalFrontier (X.truncatedWarp \ {D.owner}),
      ∃ a ∈ Gamma.initialSet X.truncatedWarp \ {requestExit r},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            switchedEdges D.saturatedWarp (.finite Q)) a t := by
  intro t ht
  have hcontact : D.contact.vertex ∈
      Gamma.terminalFrontier D.saturatedWarp := by
    rw [← D.normalizedSuffix_initial]
    exact D.normalizedSuffix_initial_mem_terminalFrontier
  have ht' : t ∈ Gamma.terminalFrontier D.saturatedWarp \
      {D.contact.vertex} := by
    rw [D.terminalFrontier_saturatedWarp_sdiff_contact]
    exact ht
  obtain ⟨a, ha, hreach⟩ :=
    TerminalContactSwitch.IsTerminalContactSwitching.oldTerminal_rooted
      hswitch hcontact hQInitial ht'
  refine ⟨a, ?_, hreach⟩
  rw [D.saturatedWarp_initialSet] at ha
  exact ha

/-- Complete old-frontier accounting for the saturated transaction.  Every
old sink is either rooted after switching, or is the endpoint of the one
finite source-grounded owner that saturation deliberately replaced.  In
the latter case the actual old owner is retained as a finite ambient-source
path witness, so no displaced endpoint loses its ancestry. -/
theorem terminalContactSwitch_oldFrontier_rooted_or_displacedOwner
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (Q : FiniteTrace Gamma.graph)
    (hQInitial : Q.initial = D.contact.vertex)
    (hswitch : IsTerminalContactSwitching
      D.saturatedWarp Q (requestExit r)) :
    ∀ t ∈ Gamma.terminalFrontier X.truncatedWarp,
      (∃ p : FinitePath Gamma.graph,
          D.owner = (.inl p : Gamma.DPath) ∧
            p.start ∈ Gamma.source ∧ p.finish = t) ∨
        ∃ a ∈ Gamma.initialSet X.truncatedWarp \ {requestExit r},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈
              switchedEdges D.saturatedWarp (.finite Q)) a t := by
  intro t ht
  cases howner : D.owner with
  | inl p =>
      by_cases hfinish : t = p.finish
      · left
        refine ⟨p, rfl, ?_, hfinish.symm⟩
        have hsource := D.owner_source
        rw [howner] at hsource
        exact hsource
      · right
        apply D.terminalContactSwitch_roots_untouchedFrontier
          Q hQInitial hswitch t
        have hrest : Gamma.terminalFrontier
            (X.truncatedWarp \ {D.owner}) =
            Gamma.terminalFrontier X.truncatedWarp \ {p.finish} := by
          apply DWeb.IsWarp.terminalFrontier_sdiff_singleton Gamma
            X.truncatedWarp_isWarp D.owner_mem
          rw [howner]
          rfl
        rw [hrest]
        exact ⟨ht, by simpa only [Set.mem_singleton_iff] using hfinish⟩
  | inr ray =>
      right
      apply D.terminalContactSwitch_roots_untouchedFrontier
        Q hQInitial hswitch t
      obtain ⟨Y, hYW, hYTerminal⟩ := ht
      refine ⟨Y, ⟨hYW, ?_⟩, hYTerminal⟩
      intro heq
      have hYD : Y = D.owner := Set.mem_singleton_iff.mp heq
      subst Y
      rw [howner] at hYTerminal
      cases hYTerminal

end SourceSaturation

/-- Every actual selected route admits the one-shot final contact with the
entire source-grounded part of its truncated reference warp. -/
theorem exists_sourceSaturation
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    Nonempty (SourceSaturation X) := by
  let zero : Fin X.remainingErasedRoute.vertexChain.length :=
    ⟨0, by rw [X.remainingErasedRoute.vertexChain_length]; omega⟩
  have hzero : X.remainingErasedRoute.vertexChain[zero] =
      X.lastContact.vertex := by
    change X.remainingErasedRoute.vertexChain.get zero = _
    have h := X.remainingErasedRoute.routeVertex_zero
    unfold ErasedSignedRoute.routeVertex at h
    simpa only [zero, List.getD_eq_get
      X.remainingErasedRoute.vertexChain (requestExit r) zero] using h
  have hcontactAtZero : X.remainingErasedRoute.vertexChain[zero] ∈
      X.sourceGroundedCarrier := by
    rw [hzero]
    refine ⟨(.inl X.oldPrefix : Gamma.DPath), ?_, ?_⟩
    · exact ⟨Set.mem_insert _ _, X.oldPrefix_source⟩
    · rw [← X.oldPrefix_finish]
      exact X.oldPrefix.finish_mem_support
  let C : X.remainingErasedRoute.LastContact X.sourceGroundedCarrier :=
    (X.remainingErasedRoute.exists_lastContact X.sourceGroundedCarrier
      ⟨zero, hcontactAtZero⟩).some
  obtain ⟨Y, hY, hCY⟩ := C.vertex_mem
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix Y hCY
  exact ⟨{
    contact := C
    owner := Y
    owner_mem := hY.1
    owner_source := hY.2
    contact_mem_owner := hCY
    ownerPrefix := q
    prefix_start := hqStart
    prefix_source := hqStart ▸ hY.2
    prefix_finish := hqFinish
    prefix_support := hqSupport
    prefix_edges := hqEdges }⟩

end ReservedStrongSelectedStartingLastContact

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.forwardLinksOff_sourceGroundedOwners
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.contact_eq_initial_or_suffix_vertexChain_lt
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.normalizedSuffix_backwardLinksOn_saturatedWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.terminalContactGeometryOutcome_on_saturatedWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.canonicalDeferredLadder_saturatedForwardReference_terminal_or_inessential
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.canonicalDeferredLadder_saturatedUncoveredForward_contact_or_terminal_or_inessential
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.exists_sourcePath_to_firstLinkExit_of_contact_forward
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.exists_terminalContactSwitchWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.terminalContactSwitch_roots_untouchedFrontier
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.terminalContactSwitch_oldFrontier_rooted_or_displacedOwner
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.exists_sourceSaturation
