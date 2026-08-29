/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutFracturedProjection
import ErdosProblems.Erdos599.HalfwayInsideCutCarrierCore

/-!
# Owner-indexed fragments of a post-closure finite row

In Assertion 9.31 the closing set is chosen before the later finite linkage.
Consequently the later row is not closed under the closing set: its exits and
reentries are precisely the endpoints of the literal fractured family.

This file records the finite geometry which is available with no row-closure
hypothesis.  Every projected split fragment has a unique owner in the original
row.  Its initial vertex is either the initial vertex of that owner or a
genuine edge leaving the cut, and its finite terminal is either the terminal
of that owner or a genuine edge entering the cut.  These are order statements
inside one original row member; no club-stage location is asserted here.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V}
variable {W : Set Gamma.DPath} {X : Set V}

private theorem walk_support_subset_warp_member
    (hW : Gamma.IsWarp W) {a b : V} (q : Walk Gamma.graph a b) :
    ∀ {p : Gamma.DPath}, p ∈ W → a ∈ p.support →
      q.edgeSet ⊆ familyEdges W →
      ∀ {x : V}, x ∈ q.support → x ∈ p.support := by
  induction q with
  | nil =>
      intro p hp ha _hedges x hx
      simp only [Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact ha
  | @cons a b c hab q ih =>
      intro p hp ha hedges x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · have habW : (a, b) ∈ familyEdges W := by
          apply hedges
          simp only [Walk.edgeSet_cons]
          exact Or.inl rfl
        simp only [familyEdges, Set.mem_iUnion] at habW
        obtain ⟨r, hrW, habr⟩ := habW
        have har : a ∈ r.support :=
          (r.edgeSet_subset_support_prod habr).1
        have hbr : b ∈ r.support :=
          (r.edgeSet_subset_support_prod habr).2
        have hpr : p = r :=
          DWeb.IsWarp.eq_of_mem_support hW hp hrW ha har
        have hb : b ∈ p.support := by simpa only [hpr] using hbr
        apply ih hp hb
        · intro e he
          apply hedges
          simp only [Walk.edgeSet_cons]
          exact Or.inr he
        · exact hx

/-- One literal cut fragment together with its unique original row owner. -/
structure OriginalCutFragmentOwner
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    (p : {p // p ∈ F.outside.holes.paths}) where
  owner : {q // q ∈ W}
  support_subset : p.1.support ⊆ owner.1.support
  edgeSet_subset : p.1.edgeSet ⊆ owner.1.edgeSet

namespace OutsideSplitWarp.SplitProjectedOutsideFracturedWarp

variable (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) W X)

/-- Every literal projected fragment starts on the original row. -/
theorem fragment_initial_mem_originalRow
    (p : {p // p ∈ F.outside.holes.paths}) :
    p.1.initial ∈ Gamma.vertexSet W := by
  apply FocusedInsideCut.outsideCarrier_subset_vertexSet W X
  rw [← F.outside.vertexSet_eq]
  exact ⟨p.1, p.2, p.1.initial_mem_support⟩

/-- Every edge of a literal projected fragment is an original row edge. -/
theorem fragment_edgeSet_subset_familyEdges
    (p : {p // p ∈ F.outside.holes.paths}) :
    p.1.edgeSet ⊆ familyEdges W := by
  intro e he
  apply outsideFamilyEdges_subset W X
  rw [← F.outside.familyEdges_eq]
  exact Set.mem_iUnion.2 ⟨p.1, Set.mem_iUnion.2 ⟨p.2, he⟩⟩

/-- Canonical original-row owner of one literal projected fragment. -/
noncomputable def originalOwner
    (hW : Gamma.IsWarp W)
    (p : {p // p ∈ F.outside.holes.paths}) :
    OriginalCutFragmentOwner F p := by
  let q : Gamma.DPath :=
    Classical.choose (F.fragment_initial_mem_originalRow p)
  have hqW : q ∈ W :=
    (Classical.choose_spec (F.fragment_initial_mem_originalRow p)).1
  have hstart : p.1.initial ∈ q.support :=
    (Classical.choose_spec (F.fragment_initial_mem_originalRow p)).2
  have hsupport : p.1.support ⊆ q.support := by
    obtain ⟨pf, hpf⟩ := F.outside.finiteCharacter p.2
    have hstart' : pf.start ∈ q.support := by
      rw [hpf] at hstart
      change pf.start ∈ q.support at hstart
      exact hstart
    have hedges : pf.edgeSet ⊆ familyEdges W := by
      intro e he
      apply F.fragment_edgeSet_subset_familyEdges p
      rw [hpf]
      exact he
    intro x hx
    have hx' : x ∈ pf.walk.support := by
      rw [hpf] at hx
      change x ∈ pf.walk.support at hx
      exact hx
    exact walk_support_subset_warp_member hW pf.walk hqW hstart'
      hedges hx'
  refine {
    owner := ⟨q, hqW⟩
    support_subset := hsupport
    edgeSet_subset := ?_ }
  intro e he
  have heW : e ∈ familyEdges W :=
    F.fragment_edgeSet_subset_familyEdges p he
  simp only [familyEdges, Set.mem_iUnion] at heW
  obtain ⟨r, hrW, her⟩ := heW
  have htailP : e.1 ∈ p.1.support :=
    (p.1.edgeSet_subset_support_prod he).1
  have htailQ : e.1 ∈ q.support := hsupport htailP
  have htailR : e.1 ∈ r.support :=
    (r.edgeSet_subset_support_prod her).1
  have hqr : q = r :=
    DWeb.IsWarp.eq_of_mem_support hW hqW hrW htailQ htailR
  simpa only [hqr] using her

/-- A common vertex of two literal fragments identifies their original row
owner, even when the fragments are the incoming and outgoing holes at one
cut contact. -/
theorem originalOwner_eq_of_common_vertex
    (hW : Gamma.IsWarp W)
    (p q : {p // p ∈ F.outside.holes.paths}) {x : V}
    (hxp : x ∈ p.1.support) (hxq : x ∈ q.1.support) :
    (F.originalOwner hW p).owner = (F.originalOwner hW q).owner := by
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support hW
    (F.originalOwner hW p).owner.2
    (F.originalOwner hW q).owner.2
    ((F.originalOwner hW p).support_subset hxp)
    ((F.originalOwner hW q).support_subset hxq)

/-- An initial of a literal cut fragment is either the initial of its
original owner, or the tail of a genuine retained edge leaving `X`. -/
theorem fragment_initial_eq_owner_or_exit
    (hW : Gamma.IsWarp W)
    (hfinite : Gamma.HasFiniteCharacter W)
    (p : {p // p ∈ F.outside.holes.paths}) :
    p.1.initial = (F.originalOwner hW p).owner.1.initial ∨
      ∃ y, y ∉ X ∧
        (p.1.initial, y) ∈ (F.originalOwner hW p).owner.1.edgeSet := by
  have hpInitial : p.1.initial ∈
      CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
    rw [← F.outside.initialSet_eq]
    exact ⟨p.1, p.2, rfl⟩
  rcases hpInitial with hpExit | hpOutside
  · right
    obtain ⟨hxX, y, hxy⟩ := hpExit
    have hyX : y ∉ X := by
      intro hyX
      exact hxy.2 ⟨hxX, hyX⟩
    have hxyW : (p.1.initial, y) ∈ familyEdges W := hxy.1
    simp only [familyEdges, Set.mem_iUnion] at hxyW
    obtain ⟨r, hrW, hxyr⟩ := hxyW
    have hxOwner : p.1.initial ∈
        (F.originalOwner hW p).owner.1.support :=
      (F.originalOwner hW p).support_subset p.1.initial_mem_support
    have hxR : p.1.initial ∈ r.support :=
      (r.edgeSet_subset_support_prod hxyr).1
    have howner : (F.originalOwner hW p).owner.1 = r :=
      DWeb.IsWarp.eq_of_mem_support hW
        (F.originalOwner hW p).owner.2 hrW hxOwner hxR
    exact ⟨y, hyX, by simpa only [howner] using hxyr⟩
  · left
    rcases hpOutside with ⟨_hpCarrier, hxX, hnoIncoming⟩
    let owner := (F.originalOwner hW p).owner
    obtain ⟨q, hq⟩ := hfinite owner.2
    have hxq : p.1.initial ∈ q.support := by
      have := (F.originalOwner hW p).support_subset
        p.1.initial_mem_support
      change p.1.initial ∈ owner.1.support at this
      rw [hq] at this
      change p.1.initial ∈ q.support at this
      exact this
    by_contra hne
    have hne' : p.1.initial ≠ q.start := by
      simpa only [owner, hq, Path.initial] using hne
    obtain ⟨y, hyx⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        q hxq hne'
    apply hnoIncoming
    refine ⟨y, ?_⟩
    refine ⟨?_, ?_⟩
    · exact Set.mem_iUnion.2 ⟨owner.1,
        Set.mem_iUnion.2 ⟨owner.2, by
          rw [hq]
          exact hyx⟩⟩
    · rintro ⟨_yX, hxX'⟩
      exact hxX hxX'

/-- A finite terminal of a literal cut fragment is either the terminal of
its original owner, or the head of a genuine retained edge entering `X`. -/
theorem fragment_terminal_eq_owner_or_entry
    (hW : Gamma.IsWarp W)
    (hfinite : Gamma.HasFiniteCharacter W)
    (p : {p // p ∈ F.outside.holes.paths}) {x : V}
    (hterminal : Gamma.terminal? p.1 = some x) :
    Gamma.terminal? (F.originalOwner hW p).owner.1 = some x ∨
      ∃ y, y ∉ X ∧
        (y, x) ∈ (F.originalOwner hW p).owner.1.edgeSet := by
  have hpTerminal : x ∈
      CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
    rw [← F.outside.terminalFrontier_eq]
    exact ⟨p.1, p.2, hterminal⟩
  rcases hpTerminal with hpEntry | hpOutside
  · right
    obtain ⟨hxX, y, hyx⟩ := hpEntry
    have hyX : y ∉ X := by
      intro hyX
      exact hyx.2 ⟨hyX, hxX⟩
    have hyxW : (y, x) ∈ familyEdges W := hyx.1
    simp only [familyEdges, Set.mem_iUnion] at hyxW
    obtain ⟨r, hrW, hyxr⟩ := hyxW
    have hxP : x ∈ p.1.support :=
      Gamma.terminal_mem_support hterminal
    have hxOwner : x ∈ (F.originalOwner hW p).owner.1.support :=
      (F.originalOwner hW p).support_subset hxP
    have hxR : x ∈ r.support :=
      (r.edgeSet_subset_support_prod hyxr).2
    have howner : (F.originalOwner hW p).owner.1 = r :=
      DWeb.IsWarp.eq_of_mem_support hW
        (F.originalOwner hW p).owner.2 hrW hxOwner hxR
    exact ⟨y, hyX, by simpa only [howner] using hyxr⟩
  · left
    rcases hpOutside with ⟨_hpCarrier, hxX, hnoOutgoing⟩
    let owner := (F.originalOwner hW p).owner
    obtain ⟨q, hq⟩ := hfinite owner.2
    have hxq : x ∈ q.support := by
      have hxP : x ∈ p.1.support :=
        Gamma.terminal_mem_support hterminal
      have := (F.originalOwner hW p).support_subset hxP
      change x ∈ owner.1.support at this
      rw [hq] at this
      change x ∈ q.support at this
      exact this
    have hxFinish : x = q.finish := by
      by_contra hne
      obtain ⟨y, hxy⟩ :=
        FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          q hxq hne
      apply hnoOutgoing
      refine ⟨y, ?_⟩
      refine ⟨?_, ?_⟩
      · exact Set.mem_iUnion.2 ⟨owner.1,
          Set.mem_iUnion.2 ⟨owner.2, by
            rw [hq]
            exact hxy⟩⟩
      · rintro ⟨hxX', _yX⟩
        exact hxX hxX'
    simp only [owner, hq, DWeb.terminal?, Path.terminal?, hxFinish]

end OutsideSplitWarp.SplitProjectedOutsideFracturedWarp

#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.originalOwner
#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.fragment_initial_eq_owner_or_exit
#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.fragment_terminal_eq_owner_or_entry

end LinkageBlueprint
end Blueprint
end Erdos599
