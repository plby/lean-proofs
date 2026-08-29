/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeSubwarpRestriction
import ErdosProblems.Erdos599.ColouredSafeReferenceHammockTransport

/-!
# The actual reference components touched by a native switch

Restrict a native occurrence to precisely the reference owners meeting its
carrier. Every removed edge is local, and finite switched reachability from
the indexed source is preserved in both directions. If this local reference
has finite character, its actual switched warp is countably supported in
the occurrence's reference closure, with exact initial and terminal sets.

This keeps the reference-source components needed in addition to the weak
subdivision path. It does not assume those components have already been
adjoined compatibly to a global blueprint.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

open Set Cardinal Order DirectedPath Alternating Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath} {s : V}

def touchedReference (A : CurrentSafeOccurrence W Y s) : Set Gamma.DPath :=
  {p ∈ Y | (p.support ∩ A.vertexSet).Nonempty}

theorem touchedReference_subset (A : CurrentSafeOccurrence W Y s) :
    A.touchedReference ⊆ Y := fun _ hp ↦ hp.1

theorem vertexSet_touchedReference (A : CurrentSafeOccurrence W Y s) :
    Gamma.vertexSet A.touchedReference = meetingVertices Gamma Y A.vertexSet := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact ⟨p.1, p.2, hxp⟩

theorem backwardEdges_subset_touchedReference (A : CurrentSafeOccurrence W Y s) :
    A.backwardEdges ⊆ familyEdges A.touchedReference := by
  apply A.backwardEdges_subset_of_avoids_discardedReference
  apply Set.disjoint_left.mpr
  rintro x hxA ⟨p, hp, hxp⟩
  exact hp.2 ⟨hp.1, x, hxp, hxA⟩

def restrictTouchedReference (A : CurrentSafeOccurrence W Y s) :
    CurrentSafeOccurrence W A.touchedReference s :=
  A.restrictReference A.touchedReference_subset A.backwardEdges_subset_touchedReference

@[simp] theorem restrictTouchedReference_vertexSet (A : CurrentSafeOccurrence W Y s) :
    A.restrictTouchedReference.vertexSet = A.vertexSet := by
  exact A.restrictReference_vertexSet _ _

@[simp] theorem restrictTouchedReference_terminal (A : CurrentSafeOccurrence W Y s) :
    A.restrictTouchedReference.terminal? = A.terminal? := by
  exact A.restrictReference_terminal _ _

theorem familyEdge_mem_touched_of_tail_mem_referenceClosure
    (A : CurrentSafeOccurrence W Y s) (hY : Gamma.IsWarp Y)
    {x y : V} (hxy : (x, y) ∈ familyEdges Y) (hx : x ∈ A.referenceClosure) :
    (x, y) ∈ familyEdges A.touchedReference := by
  obtain ⟨p, hp, hep⟩ := Set.mem_iUnion.mp hxy |>.imp fun _ h ↦ Set.mem_iUnion.mp h
  have hxp := (p.edgeSet_subset_support_prod hep).1
  have hmeet : (p.support ∩ A.vertexSet).Nonempty := by
    rcases hx with hxA | hxOwner
    · exact ⟨x, hxp, hxA⟩
    · obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxOwner
      have hpq : p = q.1 := DWeb.IsWarp.eq_of_mem_support hY hp q.2.1 hxp hxq
      exact hpq.symm ▸ q.2.2
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨⟨hp, hmeet⟩, hep⟩⟩

theorem switchedEdge_mem_restrictTouched_of_tail_mem_referenceClosure
    (A : CurrentSafeOccurrence W Y s) (hY : Gamma.IsWarp Y)
    {x y : V} (hxy : (x, y) ∈ A.switchedEdges) (hx : x ∈ A.referenceClosure) :
    (x, y) ∈ A.restrictTouchedReference.switchedEdges := by
  rcases hxy with hreference | hforward
  · exact Or.inl ⟨A.familyEdge_mem_touched_of_tail_mem_referenceClosure hY hreference.1 hx,
      by simpa [restrictTouchedReference] using hreference.2⟩
  · exact Or.inr (by simpa [restrictTouchedReference] using hforward)

theorem restrictTouchedReference_switchedEdges_subset
    (A : CurrentSafeOccurrence W Y s) :
    A.restrictTouchedReference.switchedEdges ⊆ A.switchedEdges :=
  A.restrictReference_switchedEdges_subset _ _

/-- Restriction to touched reference owners loses no finite source path. -/
theorem hasFiniteSwitchedPathTo_restrictTouchedReference_iff
    (A : CurrentSafeOccurrence W Y s) (hY : Gamma.IsWarp Y) (t : V) :
    A.restrictTouchedReference.HasFiniteSwitchedPathTo t ↔
      A.HasFiniteSwitchedPathTo t := by
  constructor
  · rintro ⟨p, hps, hpt, hpE⟩
    exact ⟨p, hps, hpt, hpE.trans A.restrictTouchedReference_switchedEdges_subset⟩
  · rintro ⟨p, hps, hpt, hpE⟩
    have hpV := A.finitePath_support_subset_referenceClosure hY p hps hpE
    refine ⟨p, hps, hpt, fun e he ↦ ?_⟩
    exact A.switchedEdge_mem_restrictTouched_of_tail_mem_referenceClosure
      hY (hpE he) (hpV (p.edgeSet_subset_support_prod he).1)

theorem referenceClosure_countable (A : CurrentSafeOccurrence W Y s)
    (hY : Gamma.IsWarp Y) : A.referenceClosure.Countable := by
  apply Cardinal.mk_le_aleph0_iff.mp
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le le_rfl A.vertexSet_countable.le_aleph0
      (mk_meetingVertices_le Gamma Y A.vertexSet hY le_rfl A.vertexSet_countable.le_aleph0))

/-- A reference owner meeting the reference-closed carrier was already
touched by the occurrence itself. -/
theorem mem_touchedReference_of_meets_referenceClosure
    (A : CurrentSafeOccurrence W Y s) (hY : Gamma.IsWarp Y)
    {p : Gamma.DPath} (hp : p ∈ Y)
    (hmeet : (p.support ∩ A.referenceClosure).Nonempty) :
    p ∈ A.touchedReference := by
  obtain ⟨x, hxp, hx⟩ := hmeet
  refine ⟨hp, ?_⟩
  rcases hx with hxA | hxOwner
  · exact ⟨x, hxp, hxA⟩
  · obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxOwner
    have hpq : p = q.1 := DWeb.IsWarp.eq_of_mem_support hY hp q.2.1 hxp hxq
    exact hpq.symm ▸ q.2.2

#print axioms hasFiniteSwitchedPathTo_restrictTouchedReference_iff
#print axioms referenceClosure_countable

end Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace Erdos599.ColouredSafeAmbientOccurrence

open Set Cardinal Order DirectedPath Alternating Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s t : V}

/-- A finite-end native occurrence switches only its touched reference
owners. All resulting reference-source components are retained explicitly. -/
theorem Valid.exists_touchedReferenceSwitch_of_terminal
    {A : Occurrence Y s} (hA : Valid A) (hY : Gamma.IsWarp Y)
    (hfinite : Gamma.HasFiniteCharacter A.touchedReference)
    (hend : A.terminal? = some t) (hne : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = A.restrictTouchedReference.switchedEdges ∧
      Gamma.initialSet U = Gamma.initialSet A.touchedReference ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier A.touchedReference ∪ {t} ∧
      Gamma.vertexSet U ⊆ A.referenceClosure ∧ (Gamma.vertexSet U).Countable := by
  let B := A.restrictTouchedReference
  have hBvalid : Valid B := hA.restrictReference _ _
  have hBwarp : Gamma.IsWarp A.touchedReference :=
    fun _ hp _ hq hpq ↦ hY hp.1 hq.1 hpq
  have hlocalV : Gamma.vertexSet A.touchedReference ⊆ Gamma.vertexSet Y := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1, hxp⟩
  obtain ⟨U, hU, hUf, hUE, _hUiso, hUI, hUT⟩ :=
    hBvalid.exists_finiteWarp_of_terminal hBwarp hfinite
      (by simpa [B] using hend) hne (fun hx ↦ hs (hlocalV hx)) (fun hx ↦ ht (hlocalV hx))
  have hUV : Gamma.vertexSet U ⊆ A.referenceClosure := by
    rintro x ⟨q, hq, hxq⟩
    obtain ⟨p, rfl⟩ := hUf hq
    have hpStart : p.start ∈ A.referenceClosure := by
      have hstart : p.start ∈ Gamma.initialSet U := ⟨.inl p, hq, rfl⟩
      rw [hUI] at hstart
      rcases hstart with hstart | hstart
      · right
        rw [← A.vertexSet_touchedReference]
        exact initialSet_subset_vertexSet _ hstart
      · exact Or.inl (Set.mem_singleton_iff.mp hstart ▸ A.source_mem_vertexSet)
    have hpEdges : p.edgeSet ⊆ A.switchedEdges := by
      intro e he
      apply A.restrictTouchedReference_switchedEdges_subset
      rw [← hUE]
      exact Set.mem_iUnion.mpr ⟨.inl p, Set.mem_iUnion.mpr ⟨hq, he⟩⟩
    exact A.finitePath_support_subset_referenceClosure_of_start_mem hY p hpStart hpEdges hxq
  exact ⟨U, hU, hUf, hUE, hUI, hUT, hUV, (A.referenceClosure_countable hY).mono hUV⟩

#print axioms Valid.exists_touchedReferenceSwitch_of_terminal

/-- The concrete weak switch keeps every touched reference-source
component as well as its distinguished source-to-end connector. -/
structure TouchedWeakSwitch (A : Occurrence Y s) (t : V) where
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  finiteCharacter : Gamma.HasFiniteCharacter paths
  edges : familyEdges paths = A.restrictTouchedReference.switchedEdges
  initials : Gamma.initialSet paths = Gamma.initialSet A.touchedReference ∪ {s}
  terminals : Gamma.terminalFrontier paths = Gamma.terminalFrontier A.touchedReference ∪ {t}
  carrier_subset : Gamma.vertexSet paths ⊆ A.referenceClosure
  carrier_countable : (Gamma.vertexSet paths).Countable
  connector : FinitePath Gamma.graph
  connector_mem : (Sum.inl connector : Gamma.DPath) ∈ paths
  connector_start : connector.start = s
  connector_finish : connector.finish = t

theorem Valid.exists_touchedWeakSwitch
    {A : Occurrence Y s} (hA : Valid A) (hY : Gamma.IsWarp Y)
    (hfinite : Gamma.HasFiniteCharacter A.touchedReference)
    (hend : A.terminal? = some t) (hne : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hdeg : A.HasFiniteSwitchedPathTo t) : Nonempty (TouchedWeakSwitch A t) := by
  obtain ⟨U, hU, hUf, hUE, hUI, hUT, hUV, hUcount⟩ :=
    hA.exists_touchedReferenceSwitch_of_terminal hY hfinite hend hne hs ht
  obtain ⟨p, hps, hpt, hpE⟩ :=
    (A.hasFiniteSwitchedPathTo_restrictTouchedReference_iff hY t).mpr hdeg
  have hpUE : p.edgeSet ⊆ familyEdges U := by simpa only [hUE] using hpE
  obtain ⟨q, hq, hpq⟩ :=
    SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hU p
      (by simpa [hps, hpt] using hne) hpUE
  have hsq : s ∈ q.support := hps ▸ hpq.1 p.start_mem_support
  have htq : t ∈ q.support := hpt ▸ hpq.1 p.finish_mem_support
  have hUinitial : s ∈ Gamma.initialSet U := hUI.symm ▸ Or.inr (Set.mem_singleton s)
  have hUterminal : t ∈ Gamma.terminalFrontier U := hUT.symm ▸ Or.inr (Set.mem_singleton t)
  obtain ⟨r, hr, hrs⟩ := hUinitial
  have hrq : r = q := DWeb.IsWarp.eq_of_mem_support hU hr hq
    (hrs ▸ r.initial_mem_support) hsq
  have hqs : q.initial = s := hrq ▸ hrs
  obtain ⟨r, hr, hrt⟩ := hUterminal
  have hrq : r = q := DWeb.IsWarp.eq_of_mem_support hU hr hq
    (Gamma.terminal_mem_support hrt) htq
  have hqt : q.terminal? = some t := hrq ▸ hrt
  obtain ⟨f, rfl⟩ := hUf hq
  exact ⟨⟨U, hU, hUf, hUE, hUI, hUT, hUV, hUcount,
    f, hq, hqs, Option.some.inj hqt⟩⟩

namespace TouchedWeakSwitch

variable {A : Occurrence Y s}

def companions (T : TouchedWeakSwitch A t) : Set Gamma.DPath :=
  T.paths \ {Sum.inl T.connector}

theorem companions_isWarp (T : TouchedWeakSwitch A t) :
    Gamma.IsWarp T.companions := fun _ hp _ hq hpq ↦ T.isWarp hp.1 hq.1 hpq

theorem companions_finiteCharacter (T : TouchedWeakSwitch A t) :
    Gamma.HasFiniteCharacter T.companions := fun {_p} hp ↦ T.finiteCharacter hp.1

theorem companions_disjoint_connector (T : TouchedWeakSwitch A t) :
    Disjoint (Gamma.vertexSet T.companions) T.connector.support := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hxConnector
  exact Set.disjoint_left.mp
    (T.isWarp hp.1 T.connector_mem
      (fun he ↦ hp.2 (Set.mem_singleton_iff.mpr he))) hxp hxConnector

theorem companions_initialSet (T : TouchedWeakSwitch A t)
    (hs : s ∉ Gamma.vertexSet Y) :
    Gamma.initialSet T.companions = Gamma.initialSet A.touchedReference := by
  rw [companions, DWeb.IsWarp.initialSet_sdiff_singleton Gamma T.isWarp T.connector_mem,
    T.initials, show Path.initial (Sum.inl T.connector : Gamma.DPath) = s
      from T.connector_start]
  have hsLocal : s ∉ Gamma.initialSet A.touchedReference := by
    rintro ⟨p, hp, hps⟩
    exact hs ⟨p, hp.1, hps ▸ p.initial_mem_support⟩
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact hx
    · exact False.elim (hne hx)
  · intro hx
    exact ⟨Or.inl hx, fun hxs ↦ hsLocal (hxs ▸ hx)⟩

theorem companions_terminalFrontier (T : TouchedWeakSwitch A t)
    (ht : t ∉ Gamma.vertexSet Y) :
    Gamma.terminalFrontier T.companions = Gamma.terminalFrontier A.touchedReference := by
  rw [companions, DWeb.IsWarp.terminalFrontier_sdiff_singleton
    Gamma T.isWarp T.connector_mem rfl, T.terminals, T.connector_finish]
  have htLocal : t ∉ Gamma.terminalFrontier A.touchedReference := by
    rintro ⟨p, hp, hpt⟩
    exact ht ⟨p, hp.1, Gamma.terminal_mem_support hpt⟩
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact hx
    · exact False.elim (hne hx)
  · intro hx
    exact ⟨Or.inl hx, fun hxt ↦ htLocal (hxt ▸ hx)⟩

/-- Any reference owner newly met by the full local switch has its initial
represented by a real companion component. -/
theorem referenceOwner_initial_mem_companions_of_meets
    (T : TouchedWeakSwitch A t) (hY : Gamma.IsWarp Y)
    (hs : s ∉ Gamma.vertexSet Y) {p : Gamma.DPath} (hp : p ∈ Y)
    (hmeet : (p.support ∩ Gamma.vertexSet T.paths).Nonempty) :
    p.initial ∈ Gamma.initialSet T.companions := by
  rw [T.companions_initialSet hs]
  obtain ⟨x, hxp, hxT⟩ := hmeet
  exact ⟨p, A.mem_touchedReference_of_meets_referenceClosure hY hp
    ⟨x, hxp, T.carrier_subset hxT⟩, rfl⟩

/-- Although the connector is allowed to touch the old carrier at its two
ends, every companion avoids the entire protected set. -/
theorem companions_disjoint_protected (T : TouchedWeakSwitch A t)
    {X : Set V} (havoid : A.referenceClosure ∩ X ⊆ {s, t}) :
    Disjoint (Gamma.vertexSet T.companions) X := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hxX
  have hxEnds := havoid ⟨T.carrier_subset ⟨p, hp.1, hxp⟩, hxX⟩
  have hdisj : Disjoint p.support T.connector.support :=
    T.isWarp hp.1 T.connector_mem (fun he ↦ hp.2 (Set.mem_singleton_iff.mpr he))
  have hsConnector : s ∈ T.connector.support := by
    simpa only [T.connector_start] using T.connector.start_mem_support
  have htConnector : t ∈ T.connector.support := by
    simpa only [T.connector_finish] using T.connector.finish_mem_support
  rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
  · exact Set.disjoint_left.mp hdisj hxp (hxs.symm ▸ hsConnector)
  · have hxt' : x = t := Set.mem_singleton_iff.mp hxt
    exact Set.disjoint_left.mp hdisj hxp (hxt'.symm ▸ htConnector)

end TouchedWeakSwitch

#print axioms Valid.exists_touchedWeakSwitch
#print axioms TouchedWeakSwitch.companions_initialSet
#print axioms TouchedWeakSwitch.companions_terminalFrontier
#print axioms TouchedWeakSwitch.companions_disjoint_protected

end Erdos599.ColouredSafeAmbientOccurrence
