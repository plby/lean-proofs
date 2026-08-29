/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeTouchedReferenceSwitch

/-!
# A complete local switch for a native infinite occurrence

The exact finite-character switch on the touched reference has one extra
source and no extra terminal. Its actual source component is therefore a
finite path to a reference terminal. The other components are retained as
companions; none may be silently discarded from source accounting.
-/

noncomputable section

namespace Erdos599.ColouredSafeAmbientOccurrence

open Set Cardinal Order DirectedPath Alternating Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s : V}

theorem Valid.exists_touchedReferenceSwitch_of_infinite
    {A : Occurrence Y s} (hA : Valid A) (hY : Gamma.IsWarp Y)
    (hfinite : Gamma.HasFiniteCharacter A.touchedReference)
    (hend : A.terminal? = none) (hs : s ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = A.restrictTouchedReference.switchedEdges ∧
      Gamma.initialSet U = Gamma.initialSet A.touchedReference ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier A.touchedReference ∧
      Gamma.vertexSet U ⊆ A.referenceClosure ∧ (Gamma.vertexSet U).Countable := by
  let B := A.restrictTouchedReference
  have hBvalid : Valid B := hA.restrictReference _ _
  have hBwarp : Gamma.IsWarp A.touchedReference :=
    fun _ hp _ hq hne ↦ hY hp.1 hq.1 hne
  have hlocalV : Gamma.vertexSet A.touchedReference ⊆ Gamma.vertexSet Y := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1, hxp⟩
  obtain ⟨U, hU, hUf, hUE, _hUiso, hUI, hUT⟩ :=
    hBvalid.exists_finiteWarp_of_infinite hBwarp hfinite
      (by simpa [B] using hend) (fun hx ↦ hs (hlocalV hx))
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

structure TouchedInfiniteSwitch (A : Occurrence Y s) where
  paths : Set Gamma.DPath
  isWarp : Gamma.IsWarp paths
  finiteCharacter : Gamma.HasFiniteCharacter paths
  edges : familyEdges paths = A.restrictTouchedReference.switchedEdges
  initials : Gamma.initialSet paths = Gamma.initialSet A.touchedReference ∪ {s}
  terminals : Gamma.terminalFrontier paths = Gamma.terminalFrontier A.touchedReference
  carrier_subset : Gamma.vertexSet paths ⊆ A.referenceClosure
  carrier_countable : (Gamma.vertexSet paths).Countable
  sourcePath : FinitePath Gamma.graph
  source_mem : (Sum.inl sourcePath : Gamma.DPath) ∈ paths
  source_start : sourcePath.start = s
  source_finish : sourcePath.finish ∈ Gamma.terminalFrontier A.touchedReference

theorem Valid.exists_touchedInfiniteSwitch
    {A : Occurrence Y s} (hA : Valid A) (hY : Gamma.IsWarp Y)
    (hfinite : Gamma.HasFiniteCharacter A.touchedReference)
    (hend : A.terminal? = none) (hs : s ∉ Gamma.vertexSet Y) :
    Nonempty (TouchedInfiniteSwitch A) := by
  obtain ⟨U, hU, hUf, hUE, hUI, hUT, hUV, hUcount⟩ :=
    hA.exists_touchedReferenceSwitch_of_infinite hY hfinite hend hs
  have hsource : s ∈ Gamma.initialSet U := hUI.symm ▸ Or.inr (Set.mem_singleton s)
  obtain ⟨p0, hp0, hp0s⟩ := hsource
  obtain ⟨p, rfl⟩ := hUf hp0
  refine ⟨⟨U, hU, hUf, hUE, hUI, hUT, hUV, hUcount, p, hp0, hp0s, ?_⟩⟩
  exact hUT ▸ (show p.finish ∈ Gamma.terminalFrontier U from ⟨.inl p, hp0, rfl⟩)

namespace TouchedInfiniteSwitch

variable {A : Occurrence Y s}

def companions (T : TouchedInfiniteSwitch A) : Set Gamma.DPath :=
  T.paths \ {Sum.inl T.sourcePath}

theorem companions_isWarp (T : TouchedInfiniteSwitch A) :
    Gamma.IsWarp T.companions := fun _ hp _ hq hne ↦ T.isWarp hp.1 hq.1 hne

theorem companions_finiteCharacter (T : TouchedInfiniteSwitch A) :
    Gamma.HasFiniteCharacter T.companions := fun hp ↦ T.finiteCharacter hp.1

theorem companions_disjoint_source (T : TouchedInfiniteSwitch A) :
    Disjoint (Gamma.vertexSet T.companions) T.sourcePath.support := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hxSource
  exact Set.disjoint_left.mp
    (T.isWarp hp.1 T.source_mem (fun he ↦ hp.2 he)) hxp hxSource

theorem companions_disjoint_protected (T : TouchedInfiniteSwitch A)
    {X : Set V} (havoid : A.referenceClosure ∩ X ⊆ {s}) :
    Disjoint (Gamma.vertexSet T.companions) X := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hxX
  have hxs := Set.mem_singleton_iff.mp
    (havoid ⟨T.carrier_subset ⟨p, hp.1, hxp⟩, hxX⟩)
  have hsSource : s ∈ T.sourcePath.support := by
    simpa only [T.source_start] using T.sourcePath.start_mem_support
  exact Set.disjoint_left.mp T.companions_disjoint_source ⟨p, hp, hxp⟩ (hxs ▸ hsSource)

end TouchedInfiniteSwitch

#print axioms Valid.exists_touchedReferenceSwitch_of_infinite
#print axioms Valid.exists_touchedInfiniteSwitch
#print axioms TouchedInfiniteSwitch.companions_disjoint_protected

end Erdos599.ColouredSafeAmbientOccurrence
