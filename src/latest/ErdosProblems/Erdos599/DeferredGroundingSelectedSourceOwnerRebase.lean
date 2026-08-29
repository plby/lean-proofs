/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedStartingWarp

/-!
# Strict last-contact rebasing on a grounded selected-route owner

The terminal-contact normalization of a selected request can fail because a
retained forward edge or vertex still meets the reference warp.  When the
displayed owner is source-grounded and the contact is not the current route
initial, the source-faithful repair is literal: retain that owner's prefix to
its final route contact and continue with the loop-erased route suffix.

The new suffix has a strictly shorter projected vertex chain.  This is the
finite potential needed by the iterated whole-owner transaction; it is not a
mere classification of the failure.
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

/-- The raw loop-erased route left after the own-start last-contact repair. -/
noncomputable def remainingErasedRoute
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :=
  (selectedRequestTrace U S K r).erasedRoute.suffixFrom
    X.lastContact.vertex X.lastContact.vertex_mem_chain

theorem remainingErasedRoute_valid
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    {s : SignedEdge V} (hs : s ∈ X.remainingErasedRoute.steps) :
    SignedEdge.Valid (Gamma := Gamma) s := by
  let trace := selectedRequestTrace U S K r
  let erased := trace.erasedRoute
  exact trace.valid s (erased.steps_sublist.subset
    (erased.suffixFrom_steps_subset X.lastContact.vertex
      X.lastContact.vertex_mem_chain hs))

theorem normalizedSuffix_vertexSet_eq_remainingChain
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    X.normalizedSuffix.path.vertexSet =
      {v | v ∈ X.remainingErasedRoute.vertexChain} := by
  exact X.remainingErasedRoute.compressionOfValid_vertexSet_eq_vertexChain
    (fun {_s} hs ↦ X.remainingErasedRoute_valid hs)

/-- The actual grounded-owner rebase datum.  Besides the strict finite
potential it retains the literal source prefix, its owner incidence, and the
final-contact certificate used to exclude every later return. -/
structure SourceOwnerRebase
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Y : Gamma.DPath) where
  contact : X.remainingErasedRoute.LastContact Y.support
  contact_ne_initial : contact.vertex ≠ X.lastContact.vertex
  ownerPrefix : FinitePath Gamma.graph
  prefix_start : ownerPrefix.start = Y.initial
  prefix_source : ownerPrefix.start ∈ Gamma.source
  prefix_finish : ownerPrefix.finish = contact.vertex
  prefix_support : ownerPrefix.support ⊆ Y.support
  prefix_edges : ownerPrefix.edgeSet ⊆ Y.edgeSet
  suffix_vertexChain_lt :
    (X.remainingErasedRoute.suffixFrom contact.vertex
      contact.vertex_mem_chain).vertexChain.length <
      X.remainingErasedRoute.vertexChain.length

namespace SourceOwnerRebase

/-- The rebased suffix cannot return to its new source owner after the splice
point. -/
theorem suffix_meets_owner_only_at_contact
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {Y : Gamma.DPath} (D : SourceOwnerRebase X Y)
    {v : V}
    (hvSuffix : v ∈ (X.remainingErasedRoute.suffixFrom D.contact.vertex
      D.contact.vertex_mem_chain).vertexChain)
    (hvOwner : v ∈ Y.support) :
    v = D.contact.vertex := by
  exact D.contact.eq_vertex_of_mem_suffix_vertexChain_of_mem
    hvSuffix hvOwner

end SourceOwnerRebase

theorem suffix_vertexChain_length_lt_of_lastContact_ne_initial
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    {A : Set V}
    (C : X.remainingErasedRoute.LastContact A)
    (hne : C.vertex ≠ X.lastContact.vertex) :
    (X.remainingErasedRoute.suffixFrom C.vertex
      C.vertex_mem_chain).vertexChain.length <
      X.remainingErasedRoute.vertexChain.length := by
  let E := X.remainingErasedRoute
  let E' := E.suffixFrom C.vertex C.vertex_mem_chain
  have hsuffix : E'.vertexChain <:+ E.vertexChain :=
    E.suffixFrom_vertexChain_suffix C.vertex C.vertex_mem_chain
  obtain ⟨pre, hpre⟩ := hsuffix
  have hpreNe : pre ≠ [] := by
    intro hnil
    subst pre
    have hchains : E'.vertexChain = E.vertexChain := by
      simpa using hpre
    have hleft : E'.vertexChain.head? = some C.vertex := by
      simp [E', ErasedSignedRoute.vertexChain, signedVertexChain]
    have hright : E.vertexChain.head? = some X.lastContact.vertex := by
      simp [E, ErasedSignedRoute.vertexChain, signedVertexChain]
    apply hne
    exact Option.some.inj (hleft.symm.trans
      ((congrArg List.head? hchains).trans hright))
  have hprePos : 0 < pre.length := List.length_pos_iff.mpr hpreNe
  have hlen : E.vertexChain.length = pre.length + E'.vertexChain.length := by
    rw [← hpre, List.length_append]
  change E'.vertexChain.length < E.vertexChain.length
  omega

/-- A noninitial contact with a source-grounded limiting owner gives the
literal shorter rebase transaction. -/
theorem exists_sourceOwnerRebase_of_contact_ne_initial
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Y : Gamma.DPath)
    (hYSource : Y.initial ∈ Gamma.source)
    {x : V} (hxSuffix : x ∈ X.normalizedSuffix.path.vertexSet)
    (hxY : x ∈ Y.support)
    (hxne : x ≠ X.lastContact.vertex) :
    Nonempty (SourceOwnerRebase X Y) := by
  have hxChain : x ∈ X.remainingErasedRoute.vertexChain := by
    have hx := hxSuffix
    rw [X.normalizedSuffix_vertexSet_eq_remainingChain] at hx
    exact hx
  obtain ⟨i, hi⟩ := List.get_of_mem hxChain
  have hiY : X.remainingErasedRoute.vertexChain.get i ∈ Y.support := by
    rw [hi]
    exact hxY
  let C : X.remainingErasedRoute.LastContact Y.support :=
    (X.remainingErasedRoute.exists_lastContact Y.support
      ⟨i, hiY⟩).some
  have hCne : C.vertex ≠ X.lastContact.vertex := by
    intro hC
    let zero : Fin X.remainingErasedRoute.vertexChain.length :=
      ⟨0, by rw [X.remainingErasedRoute.vertexChain_length]; omega⟩
    have hzero : X.remainingErasedRoute.vertexChain[zero] =
        X.lastContact.vertex := by
      change X.remainingErasedRoute.vertexChain.get zero = _
      have h := X.remainingErasedRoute.routeVertex_zero
      unfold ErasedSignedRoute.routeVertex at h
      simpa only [zero, List.getD_eq_get
        X.remainingErasedRoute.vertexChain
        (requestExit r) zero] using h
    have hCzero : C.position = zero := by
      apply X.remainingErasedRoute.vertexChain_nodup.get_inj_iff.mp
      exact hC.trans hzero.symm
    have hine : i ≠ zero := by
      intro hiz
      apply hxne
      have hi0 := hi
      rw [hiz] at hi0
      exact hi0.symm.trans hzero
    have hiPos : 0 < i.1 := Nat.pos_of_ne_zero (by
      intro hi0
      apply hine
      exact Fin.ext hi0)
    exact C.no_mem_after i (by simpa only [hCzero] using hiPos)
      hiY
  obtain ⟨ownerPrefix, hprefixStart, hprefixFinish,
      hprefixSupport, hprefixEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix Y C.vertex_mem
  exact ⟨{
    contact := C
    contact_ne_initial := hCne
    ownerPrefix := ownerPrefix
    prefix_start := hprefixStart
    prefix_source := hprefixStart ▸ hYSource
    prefix_finish := hprefixFinish
    prefix_support := hprefixSupport
    prefix_edges := hprefixEdges
    suffix_vertexChain_lt :=
      X.suffix_vertexChain_length_lt_of_lastContact_ne_initial C hCne }⟩

private theorem walk_edge_ne_of_isPath
    {a b : V} (w : Walk Gamma.graph a b) (hw : w.IsPath)
    {e : V × V} (he : e ∈ w.edgeSet) : e.1 ≠ e.2 := by
  induction w with
  | nil => simp at he
  | @cons x y z h q ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rcases he with rfl | he
      · intro hxy
        change x = y at hxy
        unfold Walk.IsPath at hw
        simp only [Walk.support_cons, List.nodup_cons] at hw
        apply hw.1
        rw [hxy]
        exact q.start_mem_support
      · exact ih hw.tail he

/-- An edge of a concrete finite path or ray has distinct endpoints.  This
is the small path-level fact needed when two endpoints of a selected forward
edge are both forced to be the same final contact. -/
theorem path_edge_ne_of_mem (Y : Gamma.DPath)
    {e : V × V} (he : e ∈ Y.edgeSet) : e.1 ≠ e.2 := by
  rcases Y with p | ray
  · exact walk_edge_ne_of_isPath p.walk p.isPath he
  · obtain ⟨n, rfl⟩ := he
    exact fun h ↦ (Nat.ne_add_one n) (ray.injective h)

/-- A retained forward edge lying on a source-grounded reference owner
always supplies a strict rebase: one of its two distinct endpoints is a
noninitial contact. -/
theorem exists_sourceOwnerRebase_of_forwardReferenceEdge
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Y : Gamma.DPath)
    (hYSource : Y.initial ∈ Gamma.source)
    {e : V × V}
    (heForward : e ∈ X.normalizedSuffix.path.directionEdges .forward)
    (heY : e ∈ Y.edgeSet) :
    Nonempty (SourceOwnerRebase X Y) := by
  have hePath : e ∈ X.normalizedSuffix.path.edgeSet := by
    rw [X.normalizedSuffix.path.edgeSet_eq_directionEdges_union]
    exact Or.inl heForward
  have hendsSuffix := X.normalizedSuffix.path.edgeSet_subset_vertexSet_prod hePath
  have hendsY := Y.edgeSet_subset_support_prod heY
  have hene : e.1 ≠ e.2 := path_edge_ne_of_mem Y heY
  by_cases htail : e.1 = X.lastContact.vertex
  · apply X.exists_sourceOwnerRebase_of_contact_ne_initial Y hYSource
      hendsSuffix.2 hendsY.2
    exact fun hhead ↦ hene (htail.trans hhead.symm)
  · exact X.exists_sourceOwnerRebase_of_contact_ne_initial Y hYSource
      hendsSuffix.1 hendsY.1 htail

/-- An uncovered forward contact on a source-grounded owner is either the
single endpoint case at the current route initial, or it gives the same
strict rebase transaction. -/
theorem initial_or_exists_sourceOwnerRebase_of_uncoveredForwardContact
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Y : Gamma.DPath)
    (hYSource : Y.initial ∈ Gamma.source)
    {x : V} (hxForward : x ∈
      X.normalizedSuffix.path.directionVertices .forward)
    (hxY : x ∈ Y.support) :
    x = X.lastContact.vertex ∨
      Nonempty (SourceOwnerRebase X Y) := by
  by_cases hx : x = X.lastContact.vertex
  · exact Or.inl hx
  · exact Or.inr (X.exists_sourceOwnerRebase_of_contact_ne_initial
      Y hYSource (by
        simp only [AltPath.directionVertices, Set.mem_iUnion] at hxForward
        obtain ⟨l, hl, _hdir, hxl⟩ := hxForward
        exact X.normalizedSuffix.path.link_support_subset_vertexSet hl hxl)
      hxY hx)

/-- In the canonical deferred geometry, every forward-reference obstruction
to the own-start terminal-contact switch either performs a strict rebase on
a source-grounded owner, or names exactly the terminal component or an
already inessential limiting component.  Thus the source-grounded branch is
genuine finite progress, rather than a repeated owner classification. -/
theorem canonicalDeferredLadder_truncatedForwardReference_rebase_or_terminal_or_inessential
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
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (hnot : ¬ ForwardLinksOff X.truncatedWarp X.normalizedSuffix.path) :
    ∃ e : V × V, ∃ Y : Gamma.DPath,
      e ∈ X.normalizedSuffix.path.directionEdges .forward ∧
        Y ∈ X.truncatedWarp ∧ e ∈ Y.edgeSet ∧
        (Nonempty (SourceOwnerRebase X Y) ∨ Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  obtain ⟨e, Y, heForward, hY, heY, howner⟩ :=
    canonicalDeferredLadder_truncatedForwardReferenceOwner_exists
      preferred hkappa huncountable hNoEnter hL S r X Z hZ hexit hnot
  refine ⟨e, Y, heForward, hY, heY, ?_⟩
  rcases howner with hYSource | hterminal | hinessential
  · exact Or.inl
      (X.exists_sourceOwnerRebase_of_forwardReferenceEdge
        Y hYSource heForward heY)
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr hinessential)

/-- Vertex-contact companion to the forward-reference progress theorem.
The one exceptional source-grounded case is the literal current route
initial; every other source-grounded contact strictly shortens the remaining
loop-erased route. -/
theorem canonicalDeferredLadder_truncatedUncoveredForward_rebase_or_terminal_or_inessential
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
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (hnot : ¬ ForwardVertexContactsCoveredAtTerminal
      Gamma X.truncatedWarp X.normalizedSuffix.path) :
    ∃ x : V, ∃ Y : Gamma.DPath,
      x ∈ X.normalizedSuffix.path.directionVertices .forward ∧
        Y ∈ X.truncatedWarp ∧ x ∈ Y.support ∧
        x ∉ X.normalizedSuffix.path.directionVertices .backward ∧
        X.normalizedSuffix.path.terminal? ≠ some x ∧
        (x = X.lastContact.vertex ∨
          Nonempty (SourceOwnerRebase X Y) ∨ Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  obtain ⟨x, Y, hxForward, hY, hxY, hxNotBackward,
      hxNotTerminal, howner⟩ :=
    canonicalDeferredLadder_truncatedUncoveredForwardOwner_exists
      preferred hkappa huncountable hNoEnter hL S r X Z hZ hexit hnot
  refine ⟨x, Y, hxForward, hY, hxY, hxNotBackward, hxNotTerminal, ?_⟩
  rcases howner with hYSource | hterminal | hinessential
  · rcases X.initial_or_exists_sourceOwnerRebase_of_uncoveredForwardContact
        Y hYSource hxForward hxY with hinitial | hrebase
    · exact Or.inl hinitial
    · exact Or.inr (Or.inl hrebase)
  · exact Or.inr (Or.inr (Or.inl hterminal))
  · exact Or.inr (Or.inr (Or.inr hinessential))

end ReservedStrongSelectedStartingLastContact

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.exists_sourceOwnerRebase_of_forwardReferenceEdge
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.initial_or_exists_sourceOwnerRebase_of_uncoveredForwardContact
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.canonicalDeferredLadder_truncatedForwardReference_rebase_or_terminal_or_inessential
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.canonicalDeferredLadder_truncatedUncoveredForward_rebase_or_terminal_or_inessential
