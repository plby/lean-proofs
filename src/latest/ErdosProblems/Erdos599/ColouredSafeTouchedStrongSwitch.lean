/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeTouchedReferenceSwitch

/-!
# The two concrete ports of a finite-end native strong switch

Nondegeneracy forces the component starting at the exposed source and the
component ending at the exposed terminal to be different. Both are finite
in the actual switch on the finite-character touched reference. Keeping the
other components gives the companion family needed for a genuine two-port
insertion into an augmented warp.
-/

noncomputable section

namespace Erdos599.ColouredSafeAmbientOccurrence

open Set Cardinal Order DirectedPath Alternating Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s t : V}

structure TouchedStrongSwitch (A : Occurrence Y s) (t : V) where
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  finiteCharacter : Gamma.HasFiniteCharacter paths
  edges : familyEdges paths = A.restrictTouchedReference.switchedEdges
  initials : Gamma.initialSet paths = Gamma.initialSet A.touchedReference ∪ {s}
  terminals : Gamma.terminalFrontier paths = Gamma.terminalFrontier A.touchedReference ∪ {t}
  carrier_subset : Gamma.vertexSet paths ⊆ A.referenceClosure
  carrier_countable : (Gamma.vertexSet paths).Countable
  sourcePath : FinitePath Gamma.graph
  source_mem : (Sum.inl sourcePath : Gamma.DPath) ∈ paths
  source_start : sourcePath.start = s
  source_finish : sourcePath.finish ∈ Gamma.terminalFrontier A.touchedReference
  terminalPath : FinitePath Gamma.graph
  terminal_mem : (Sum.inl terminalPath : Gamma.DPath) ∈ paths
  terminal_finish : terminalPath.finish = t
  terminal_start : terminalPath.start ∈ Gamma.initialSet A.touchedReference
  distinct : sourcePath ≠ terminalPath

theorem Valid.exists_touchedStrongSwitch
    {A : Occurrence Y s} (hA : Valid A) (hY : Gamma.IsWarp Y)
    (hfinite : Gamma.HasFiniteCharacter A.touchedReference)
    (hend : A.terminal? = some t) (hne : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hnondeg : ¬A.HasFiniteSwitchedPathTo t) : Nonempty (TouchedStrongSwitch A t) := by
  obtain ⟨U, hU, hUf, hUE, hUI, hUT, hUV, hUcount⟩ :=
    hA.exists_touchedReferenceSwitch_of_terminal hY hfinite hend hne hs ht
  have hsource : s ∈ Gamma.initialSet U := hUI.symm ▸ Or.inr (Set.mem_singleton s)
  obtain ⟨p0, hp0, hp0s⟩ := hsource
  obtain ⟨p, rfl⟩ := hUf hp0
  have hps : p.start = s := hp0s
  have hterminal : t ∈ Gamma.terminalFrontier U := hUT.symm ▸ Or.inr (Set.mem_singleton t)
  obtain ⟨q0, hq0, hq0t⟩ := hterminal
  obtain ⟨q, rfl⟩ := hUf hq0
  have hqt : q.finish = t := Option.some.inj hq0t
  have hpathEdges : ∀ f : FinitePath Gamma.graph, Sum.inl f ∈ U →
      f.edgeSet ⊆ A.switchedEdges := by
    intro f hf e he
    apply A.restrictTouchedReference_switchedEdges_subset
    rw [← hUE]
    exact Set.mem_iUnion.mpr ⟨.inl f, Set.mem_iUnion.mpr ⟨hf, he⟩⟩
  have hpt : p.finish ≠ t := fun hpt ↦ hnondeg ⟨p, hps, hpt, hpathEdges p hp0⟩
  have hqs : q.start ≠ s := fun hqs ↦ hnondeg ⟨q, hqs, hqt, hpathEdges q hq0⟩
  have hpFinish : p.finish ∈ Gamma.terminalFrontier A.touchedReference := by
    have hv : p.finish ∈ Gamma.terminalFrontier U := ⟨.inl p, hp0, rfl⟩
    rw [hUT] at hv
    exact hv.resolve_right hpt
  have hqStart : q.start ∈ Gamma.initialSet A.touchedReference := by
    have hv : q.start ∈ Gamma.initialSet U := ⟨.inl q, hq0, rfl⟩
    rw [hUI] at hv
    exact hv.resolve_right hqs
  exact ⟨{
    paths := U
    isWarp := hU
    finiteCharacter := hUf
    edges := hUE
    initials := hUI
    terminals := hUT
    carrier_subset := hUV
    carrier_countable := hUcount
    sourcePath := p
    source_mem := hp0
    source_start := hps
    source_finish := hpFinish
    terminalPath := q
    terminal_mem := hq0
    terminal_finish := hqt
    terminal_start := hqStart
    distinct := fun he ↦ hpt (he ▸ hqt) }⟩

namespace TouchedStrongSwitch

variable {A : Occurrence Y s}

def companions (T : TouchedStrongSwitch A t) : Set Gamma.DPath :=
  T.paths \ {Sum.inl T.sourcePath, Sum.inl T.terminalPath}

theorem port_supports_disjoint (T : TouchedStrongSwitch A t) :
    Disjoint T.sourcePath.support T.terminalPath.support :=
  T.isWarp T.source_mem T.terminal_mem (fun he ↦ T.distinct (Sum.inl.inj he))

theorem companions_isWarp (T : TouchedStrongSwitch A t) :
    Gamma.IsWarp T.companions := fun _ hp _ hq hne ↦ T.isWarp hp.1 hq.1 hne

theorem companions_finiteCharacter (T : TouchedStrongSwitch A t) :
    Gamma.HasFiniteCharacter T.companions := fun hp ↦ T.finiteCharacter hp.1

theorem companions_disjoint_source (T : TouchedStrongSwitch A t) :
    Disjoint (Gamma.vertexSet T.companions) T.sourcePath.support := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hxSource
  exact Set.disjoint_left.mp
    (T.isWarp hp.1 T.source_mem (fun he ↦ hp.2 (Or.inl he))) hxp hxSource

theorem companions_disjoint_terminal (T : TouchedStrongSwitch A t) :
    Disjoint (Gamma.vertexSet T.companions) T.terminalPath.support := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hxTerminal
  exact Set.disjoint_left.mp
    (T.isWarp hp.1 T.terminal_mem (fun he ↦ hp.2 (Or.inr he))) hxp hxTerminal

theorem protected_ports
    (T : TouchedStrongSwitch A t) {X : Set V}
    (havoid : A.referenceClosure ∩ X ⊆ {s, t}) :
    T.sourcePath.support ∩ X ⊆ {s} ∧
    T.terminalPath.support ∩ X ⊆ {t} ∧
    Disjoint (Gamma.vertexSet T.companions) X := by
  have hsSource : s ∈ T.sourcePath.support := by
    simpa only [T.source_start] using T.sourcePath.start_mem_support
  have htTerminal : t ∈ T.terminalPath.support := by
    simpa only [T.terminal_finish] using T.terminalPath.finish_mem_support
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxEnds := havoid ⟨T.carrier_subset ⟨.inl T.sourcePath, T.source_mem, hx.1⟩, hx.2⟩
    rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
    · exact hxs
    · exact False.elim (Set.disjoint_left.mp T.port_supports_disjoint hx.1
        (Set.mem_singleton_iff.mp hxt ▸ htTerminal))
  · intro x hx
    have hxEnds := havoid ⟨T.carrier_subset ⟨.inl T.terminalPath, T.terminal_mem, hx.1⟩, hx.2⟩
    rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
    · exact False.elim (Set.disjoint_left.mp T.port_supports_disjoint
        (hxs ▸ hsSource) hx.1)
    · exact hxt
  · apply Set.disjoint_left.mpr
    rintro x ⟨p, hp, hxp⟩ hxX
    have hxEnds := havoid ⟨T.carrier_subset ⟨p, hp.1, hxp⟩, hxX⟩
    rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
    · exact Set.disjoint_left.mp T.companions_disjoint_source ⟨p, hp, hxp⟩ (hxs ▸ hsSource)
    · exact Set.disjoint_left.mp T.companions_disjoint_terminal ⟨p, hp, hxp⟩
        (Set.mem_singleton_iff.mp hxt ▸ htTerminal)

end TouchedStrongSwitch

#print axioms Valid.exists_touchedStrongSwitch
#print axioms TouchedStrongSwitch.port_supports_disjoint
#print axioms TouchedStrongSwitch.protected_ports

end Erdos599.ColouredSafeAmbientOccurrence
