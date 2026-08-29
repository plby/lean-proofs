/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkFinalAssembly
import ErdosProblems.Erdos599.SafeLinkReducedProperties

/-!
# Corollary 6.9 for the honest quotient/deletion transport

After essential trimming, every reduced quotient path has genuine ancestry
in the common Section 6 wave.  This file records the last-exit argument in a
form whose ground wave lives in a vertex-deleted web while the reduced paths
live in a quotient of the ambient web.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace SafeLink

variable {V : Type u}

/-- Quotient-path form of Aharoni--Berger Corollary 6.9.  A path beginning
in the old source is roofed immediately by the ground wave.  A path beginning
in `X` leaves `T`, and its first boundary vertex is roofed by Assertion 6.8.
The witness is retained because `R ⊆ X ⊆ T`. -/
theorem corollary69_quotient_of_boundaryRoof
    (K : DWeb V) {X T R : Set V}
    (hXT : X ⊆ T) (hRX : R ⊆ X)
    (hSourceX : Disjoint K.source X)
    (ground : (K.delete R).Wave)
    {W : Set ((K.quotient X).DPath)}
    (hinitial : ∀ p ∈ W, p.initial ∈ K.source ∪ X)
    {Q : Set V}
    (hterminal : ∀ p ∈ W, ∃ t,
      (K.quotient X).terminal? p = some t ∧ t ∉ Q)
    (hterminalTree : ∀ p ∈ W, p.initial ∈ X → ∀ t,
      (K.quotient X).terminal? p = some t → t ∈ T → t ∈ Q)
    (hboundaryRoof : ∀ p ∈ W, p.initial ∈ X → ∀ z ∈ p.support,
      z ∈ Walk.outBoundary (K.quotient X).graph T →
        z ∈ (K.delete R).roof
          ((K.delete R).terminalFrontier ground.1)) :
    ∀ p ∈ W, ∃ u ∈ p.support, u ∉ R ∧
      u ∈ (K.delete R).roof
        ((K.delete R).terminalFrontier ground.1) := by
  intro p hp
  rcases hinitial p hp with hpSource | hpX
  · have hpNotR : p.initial ∉ R := by
      intro hpR
      exact Set.disjoint_left.1 hSourceX hpSource (hRX hpR)
    refine ⟨p.initial, p.initial_mem_support, hpNotR, ?_⟩
    exact ground.2.2.2 ⟨hpSource, hpNotR⟩
  · obtain ⟨t, hpterm, htQ⟩ := hterminal p hp
    rcases p with p | r
    · have hpfinish : p.finish = t := by
        simpa only [DWeb.terminal?_finite, Option.some.injEq] using hpterm
      have htT : t ∉ T := by
        intro ht
        apply htQ
        exact hterminalTree (.inl p) hp hpX t hpterm ht
      have hpstartT : p.start ∈ T := hXT hpX
      obtain ⟨L⟩ := Walk.exists_lastExit p.walk T
        ⟨p.start, p.walk.start_mem_support, hpstartT⟩
        (hpfinish.symm ▸ htT)
      have houtSupport : L.outside ∈ p.support :=
        L.support_suffix.subset L.suffix.start_mem_support
      have houtBoundary : L.outside ∈
          Walk.outBoundary (K.quotient X).graph T :=
        ⟨L.outside_not_mem, L.inside, L.inside_mem, L.edge⟩
      have houtNotR : L.outside ∉ R := by
        intro houtR
        exact L.outside_not_mem (hXT (hRX houtR))
      refine ⟨L.outside, houtSupport, houtNotR, ?_⟩
      exact hboundaryRoof (.inl p) hp hpX L.outside houtSupport houtBoundary
    · simp at hpterm

/-- Corollary 6.9 specialized to a reduced wave equipped with ancestry in
the common quotient wave.  This is the bridge between Assertion 6.4,
Assertion 6.8, and the retained-meeting hypothesis of Lemma 3.15. -/
theorem corollary69_of_reducedAncestry
    (G : DWeb V) {a : V} {T X R Q : Set V}
    (hT : G.IsTreeSet a T) (hXT : X ⊆ T \ {a}) (hRX : R ⊆ X)
    {M : Set (((G.delete {a}).quotient X).DPath)}
    {W : Set ((((G.delete {a}).delete Q).quotient X).DPath)}
    (hinitial : ∀ p ∈ W,
      p.initial ∈ ((G.delete {a}).delete Q).source ∪ X)
    (hancestry : ∀ p ∈ W,
      ∃ m ∈ ((G.delete {a}).quotient X).essentialWarpPart M,
        (∀ t, ((G.delete {a}).quotient X).terminal? m = some t →
          t ∉ Q) ∧
        p.support ⊆ m.support ∧
        (((G.delete {a}).delete Q).quotient X).terminal? p =
          ((G.delete {a}).quotient X).terminal? m)
    (hterminalTree :
      ((G.delete {a}).quotient X).terminalFrontier
          (((G.delete {a}).quotient X).essentialMeetingPaths M X) ∩ T ⊆ Q)
    (ground : (((G.delete {a}).delete Q).delete R).Wave)
    (hboundaryRoof : ∀ z ∈ G.outerBoundary T,
      z ∈ ((G.delete {a}).quotient X).vertexSet
          (((G.delete {a}).quotient X).essentialMeetingPaths M X) →
      z ∈ (((G.delete {a}).delete Q).delete R).roof
        ((((G.delete {a}).delete Q).delete R).terminalFrontier ground.1)) :
    ∀ p ∈ W, ∃ u ∈ p.support, u ∉ R ∧
      u ∈ (((G.delete {a}).delete Q).delete R).roof
        ((((G.delete {a}).delete Q).delete R).terminalFrontier ground.1) := by
  let base := G.delete {a}
  let K := base.delete Q
  let H := base.quotient X
  have hSourceX : Disjoint K.source X := by
    exact (tree_offRoot_disjoint_delete_source G hT hXT).mono_left
      Set.sdiff_subset
  apply corollary69_quotient_of_boundaryRoof K (fun _ hx ↦ (hXT hx).1)
    hRX hSourceX
    ground hinitial (Q := Q)
  · intro p hp
    obtain ⟨m, hm, hmAvoid, _hpm, hterminal⟩ := hancestry p hp
    obtain ⟨_hmM, t, hmt, _htEssential⟩ := hm
    exact ⟨t, hterminal.trans hmt, hmAvoid t hmt⟩
  · intro p hp hpInitial t hpt htT
    obtain ⟨m, hm, _hmAvoid, hpm, hterminal⟩ := hancestry p hp
    have hmMeet : (m.support ∩ X).Nonempty := by
      exact ⟨p.initial, hpm p.initial_mem_support, hpInitial⟩
    have hmMeeting : m ∈ H.essentialMeetingPaths M X :=
      ⟨hm, hmMeet⟩
    have hmt : H.terminal? m = some t := hterminal.symm.trans hpt
    exact hterminalTree ⟨⟨m, hmMeeting, hmt⟩, htT⟩
  · intro p hp hpInitial z hzp hzBoundary
    obtain ⟨m, hm, _hmAvoid, hpm, _hterminal⟩ := hancestry p hp
    have hmMeet : (m.support ∩ X).Nonempty := by
      exact ⟨p.initial, hpm p.initial_mem_support, hpInitial⟩
    have hmMeeting : m ∈ H.essentialMeetingPaths M X :=
      ⟨hm, hmMeet⟩
    have hzOuter : z ∈ G.outerBoundary T := by
      obtain ⟨hzT, t, htT, htz⟩ := hzBoundary
      exact ⟨hzT, t, htT, htz.1.1.1⟩
    exact hboundaryRoof z hzOuter
      ⟨m, hmMeeting, hpm hzp⟩

end SafeLink

end Erdos599
