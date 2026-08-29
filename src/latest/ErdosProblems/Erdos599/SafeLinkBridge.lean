/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.QuotientMaximal
import ErdosProblems.Erdos599.SafeTree

/-!
# Removing terminal paths before a vertex deletion

This file isolates the path transport used immediately after Assertion 6.4
in the proof of Aharoni--Berger Proposition 6.3.  If a deleted vertex can
occur on a wave only as the terminal of one of its members, then removing
the members which end in the deleted set leaves a wave in the vertex-deleted
web.  The resulting family is represented in the genuinely deleted path
type; no identification of two different quotient graphs is assumed.

The final theorem packages the exact form needed for the Section 6
essential subwarp: it is enough to know that every member which meets `Q`
also meets `X`, and to apply Assertion 6.4(ii) to the essential members
meeting `X`.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Retain the members of `U` whose finite terminal is outside `Q`.
Rays have no terminal and are retained. -/
def terminalAvoidingSubfamily (U : Set G.DPath) (Q : Set V) : Set G.DPath :=
  {p | p ∈ U ∧ ∀ q, G.terminal? p = some q → q ∉ Q}

@[simp]
theorem mem_terminalAvoidingSubfamily_iff
    (U : Set G.DPath) (Q : Set V) (p : G.DPath) :
    p ∈ G.terminalAvoidingSubfamily U Q ↔
      p ∈ U ∧ ∀ q, G.terminal? p = some q → q ∉ Q :=
  Iff.rfl

/-- Removing precisely the members ending in `Q` removes precisely the
`Q`-part of the terminal frontier. -/
@[simp]
theorem terminalFrontier_terminalAvoidingSubfamily
    (U : Set G.DPath) (Q : Set V) :
    G.terminalFrontier (G.terminalAvoidingSubfamily U Q) =
      G.terminalFrontier U \ Q := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    exact ⟨⟨p, hp.1, hpx⟩, hp.2 x hpx⟩
  · rintro ⟨⟨p, hp, hpx⟩, hxQ⟩
    exact ⟨p, ⟨hp, fun q hpq hqQ ↦
      hxQ (Option.some.inj (hpq.symm.trans hpx) ▸ hqQ)⟩, hpx⟩

/-- If every contact of `U` with `Q` is a terminal contact, then the
members not ending in `Q` avoid `Q` altogether. -/
theorem disjoint_vertexSet_terminalAvoidingSubfamily
    {U : Set G.DPath} {Q : Set V} (hU : G.IsWarp U)
    (hcontact : G.vertexSet U ∩ Q ⊆ G.terminalFrontier U) :
    Disjoint (G.vertexSet (G.terminalAvoidingSubfamily U Q)) Q := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hp, hxp⟩ hxQ
  obtain ⟨r, hrU, hrx⟩ := hcontact ⟨⟨p, hp.1, hxp⟩, hxQ⟩
  have hpr : p = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hU hp.1 hrU hne) hxp
      (G.terminal_mem_support hrx)
  subst r
  exact hp.2 x hrx hxQ

/-- The actual path family in the deleted web obtained after removing all
members ending in `Q`. -/
noncomputable def deleteTerminalSubfamily
    (U : Set G.DPath) (Q : Set V) (hU : G.IsWarp U)
    (hcontact : G.vertexSet U ∩ Q ⊆ G.terminalFrontier U) :
    Set (G.delete Q).DPath :=
  G.restrictDeleteFamily Q (G.terminalAvoidingSubfamily U Q)
    (G.disjoint_vertexSet_terminalAvoidingSubfamily hU hcontact)

@[simp]
theorem terminalFrontier_deleteTerminalSubfamily
    (U : Set G.DPath) (Q : Set V) (hU : G.IsWarp U)
    (hcontact : G.vertexSet U ∩ Q ⊆ G.terminalFrontier U) :
    (G.delete Q).terminalFrontier
        (G.deleteTerminalSubfamily U Q hU hcontact) =
      G.terminalFrontier U \ Q := by
  unfold deleteTerminalSubfamily
  rw [G.terminalFrontier_restrictDeleteFamily,
    G.terminalFrontier_terminalAvoidingSubfamily]

/-- Deleting terminal-only contacts preserves the wave property after the
paths which end at deleted vertices are removed.  This is the precise
deleted-web statement used in the proof following Assertion 6.4. -/
theorem isWave_deleteTerminalSubfamily
    {U : Set G.DPath} {Q : Set V} (hU : G.IsWave U)
    (hcontact : G.vertexSet U ∩ Q ⊆ G.terminalFrontier U) :
    (G.delete Q).IsWave
      (G.deleteTerminalSubfamily U Q hU.1 hcontact) := by
  unfold deleteTerminalSubfamily
  let U₀ := G.terminalAvoidingSubfamily U Q
  let havoid : Disjoint (G.vertexSet U₀) Q :=
    G.disjoint_vertexSet_terminalAvoidingSubfamily hU.1 hcontact
  have hU₀warp : G.IsWarp U₀ := by
    intro p hp q hq hpq
    exact hU.1 hp.1 hq.1 hpq
  refine ⟨DWeb.IsWarp.restrictDeleteFamily G hU₀warp havoid, ?_, ?_⟩
  · rw [G.initialSet_restrictDeleteFamily]
    rintro a ⟨p, hp, rfl⟩
    refine ⟨hU.2.1 ⟨p, hp.1, rfl⟩, ?_⟩
    exact Set.disjoint_left.1 havoid
      ⟨p, hp, DirectedPath.Path.initial_mem_support p⟩
  · have hroof := G.fd_delete_roof_frontier_sdiff (X := Q) hU
    simpa only [G.terminalFrontier_restrictDeleteFamily,
      G.terminalFrontier_terminalAvoidingSubfamily] using hroof

/-- The contact hypothesis for the whole essential subwarp follows from
Assertion 6.4(ii) once every essential path which touches `Q` is known to
belong to the subfamily meeting `X`. -/
theorem essentialWarpPart_contact_of_meeting_contact
    {W : Set G.DPath} {X Q : Set V}
    (hQforcesX : ∀ p ∈ G.essentialWarpPart W,
      (p.support ∩ Q).Nonempty → (p.support ∩ X).Nonempty)
    (hcontact :
      G.vertexSet (G.essentialMeetingPaths W X) ∩ Q ⊆
        G.terminalFrontier (G.essentialMeetingPaths W X)) :
    G.vertexSet (G.essentialWarpPart W) ∩ Q ⊆
      G.terminalFrontier (G.essentialWarpPart W) := by
  rintro q ⟨⟨p, hp, hqp⟩, hqQ⟩
  have hpX : (p.support ∩ X).Nonempty :=
    hQforcesX p hp ⟨q, hqp, hqQ⟩
  have hpMeeting : p ∈ G.essentialMeetingPaths W X := ⟨hp, hpX⟩
  obtain ⟨r, hr, hrq⟩ :=
    hcontact ⟨⟨p, hpMeeting, hqp⟩, hqQ⟩
  exact ⟨r, hr.1, hrq⟩

/-- Corrected contact reduction: a member already ending at the contacted
`Q`-vertex needs no meeting-`X` witness.  Only a nonterminal contact has to
be forced onto a path meeting `X`. -/
theorem essentialWarpPart_contact_of_nonterminal_meeting_contact
    {W : Set G.DPath} {X Q : Set V}
    (hQforcesX : ∀ p ∈ G.essentialWarpPart W, ∀ q ∈ p.support,
      q ∈ Q → G.terminal? p ≠ some q →
        (p.support ∩ X).Nonempty)
    (hcontact :
      G.vertexSet (G.essentialMeetingPaths W X) ∩ Q ⊆
        G.terminalFrontier (G.essentialMeetingPaths W X)) :
    G.vertexSet (G.essentialWarpPart W) ∩ Q ⊆
      G.terminalFrontier (G.essentialWarpPart W) := by
  rintro q ⟨⟨p, hp, hqp⟩, hqQ⟩
  by_cases hpq : G.terminal? p = some q
  · exact ⟨p, hp, hpq⟩
  · have hpX : (p.support ∩ X).Nonempty :=
      hQforcesX p hp q hqp hqQ hpq
    have hpMeeting : p ∈ G.essentialMeetingPaths W X := ⟨hp, hpX⟩
    obtain ⟨r, hr, hrq⟩ :=
      hcontact ⟨⟨p, hpMeeting, hqp⟩, hqQ⟩
    exact ⟨r, hr.1, hrq⟩

/-- Assertion 6.4(ii), together with the fact that all relevant `Q`
contacts occur on essential paths meeting `X`, produces a genuine wave in
the vertex-deleted web after the `Q`-ending paths are removed. -/
theorem isWave_deleteTerminalSubfamily_essentialMeeting
    {W : Set G.DPath} {X Q : Set V} (hW : G.IsWave W)
    (hQforcesX : ∀ p ∈ G.essentialWarpPart W,
      (p.support ∩ Q).Nonempty → (p.support ∩ X).Nonempty)
    (hcontact :
      G.vertexSet (G.essentialMeetingPaths W X) ∩ Q ⊆
        G.terminalFrontier (G.essentialMeetingPaths W X)) :
    (G.delete Q).IsWave
      (G.deleteTerminalSubfamily (G.essentialWarpPart W) Q
        hW.essentialWarpPart.1
        (G.essentialWarpPart_contact_of_meeting_contact
          hQforcesX hcontact)) := by
  apply G.isWave_deleteTerminalSubfamily hW.essentialWarpPart

/-- Nonterminal-contact form of the preceding bridge.  This is the form
used in Proposition 6.3: paths which already end in `Q` are precisely the
ones removed, so only internal `Q`-contacts need to be shown to meet `X`. -/
theorem isWave_deleteTerminalSubfamily_essentialMeeting_nonterminal
    {W : Set G.DPath} {X Q : Set V} (hW : G.IsWave W)
    (hQforcesX : ∀ p ∈ G.essentialWarpPart W, ∀ q ∈ p.support,
      q ∈ Q → G.terminal? p ≠ some q →
        (p.support ∩ X).Nonempty)
    (hcontact :
      G.vertexSet (G.essentialMeetingPaths W X) ∩ Q ⊆
        G.terminalFrontier (G.essentialMeetingPaths W X)) :
    (G.delete Q).IsWave
      (G.deleteTerminalSubfamily (G.essentialWarpPart W) Q
        hW.essentialWarpPart.1
        (G.essentialWarpPart_contact_of_nonterminal_meeting_contact
          hQforcesX hcontact)) := by
  apply G.isWave_deleteTerminalSubfamily hW.essentialWarpPart

/-! ## Transport from quotient-then-deletion to deletion-then-quotient -/

/-- Deleting vertices can only enlarge the roof of a fixed set. -/
theorem roof_subset_delete_roof (X Q : Set V) :
    G.roof X ⊆ (G.delete Q).roof X := by
  intro v hv p hp
  let q : DirectedPath.FinitePath G.graph :=
    p.lift (fun {_ _} e ↦ G.delete_adj_imp e)
  have hq : G.IsTargetPathFrom v q := ⟨hp.1, hp.2.1⟩
  obtain ⟨x, hxq, hxX⟩ := hv q hq
  exact ⟨x, by simpa [q] using hxq, hxX⟩

/-- A point essential after deletion was already essential before deletion.
The witnessing target path in the deleted web lifts verbatim. -/
theorem delete_essential_subset_essential (X Q : Set V) :
    (G.delete Q).essential X ⊆ G.essential X := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨p, hp, hpavoid⟩ :=
    ((G.delete Q).not_mem_roof_iff (X \ {x}) x).1 hx.2
  let q : DirectedPath.FinitePath G.graph :=
    p.lift (fun {_ _} e ↦ G.delete_adj_imp e)
  apply (G.not_mem_roof_iff (X \ {x}) x).2
  refine ⟨q, ⟨hp.1, hp.2.1⟩, ?_⟩
  apply Set.disjoint_left.2
  intro y hyq hyX
  have hyp : y ∈ p.support := by simpa [q] using hyq
  exact Set.disjoint_left.1 hpavoid hyp hyX

/-- Consequently the old strict roof is contained in the strict roof
computed after deletion. -/
theorem strictRoof_subset_delete_strictRoof (X Q : Set V) :
    G.strictRoof X ⊆ (G.delete Q).strictRoof X := by
  rintro x ⟨hxRoof, hxNotEssential⟩
  exact ⟨G.roof_subset_delete_roof X Q hxRoof,
    fun hxEssential ↦ hxNotEssential
      (G.delete_essential_subset_essential X Q hxEssential)⟩

/-- Deleting vertices preserves the no-incoming-source normalization. -/
theorem NoEdgeEnters.delete {A Q : Set V} (hA : G.NoEdgeEnters A) :
    (G.delete Q).NoEdgeEnters (A \ Q) := by
  intro u v huv hv
  exact hA huv.1 hv.1

/-- The initial vertex of a deleted-web walk is retained whenever its
terminal vertex is retained. -/
private theorem deleteWalk_start_not_mem (Q : Set V) :
    ∀ {a b : V} (p : DirectedPath.Walk (G.delete Q).graph a b),
      b ∉ Q → a ∉ Q
  | _, _, .nil, hb => hb
  | _, _, .cons e _, _ => e.2.1

/-- Every edge of `(G - Q) / X` is an edge of `(G / X) - Q`.
This is the valid direction of quotient/deletion comparison; equality is
false in general because deletion may enlarge `strictRoof X`. -/
theorem deleteQuotient_adj_imp_quotientDelete
    (X Q : Set V) {u v : V}
    (huv : ((G.delete Q).quotient X).graph.Adj u v) :
    ((G.quotient X).delete Q).graph.Adj u v := by
  refine ⟨⟨huv.1.1, ?_, ?_, huv.2.2.2⟩, huv.1.2.1, huv.1.2.2⟩
  · intro huOld
    exact huv.2.1 (G.strictRoof_subset_delete_strictRoof X Q huOld)
  · intro hvOld
    exact huv.2.2.1 (G.strictRoof_subset_delete_strictRoof X Q hvOld)

/-- Lift a path from deletion-then-quotient to quotient-then-deletion. -/
def liftDeleteQuotientPathToQuotientDelete (X Q : Set V)
    (p : ((G.delete Q).quotient X).DPath) :
    ((G.quotient X).delete Q).DPath :=
  DirectedPath.Path.lift
    (fun {_ _} e ↦ G.deleteQuotient_adj_imp_quotientDelete X Q e) p

@[simp]
theorem support_liftDeleteQuotientPathToQuotientDelete
    (X Q : Set V) (p : ((G.delete Q).quotient X).DPath) :
    (G.liftDeleteQuotientPathToQuotientDelete X Q p).support = p.support := by
  exact DirectedPath.Path.support_lift _ p

@[simp]
theorem initial_liftDeleteQuotientPathToQuotientDelete
    (X Q : Set V) (p : ((G.delete Q).quotient X).DPath) :
    (G.liftDeleteQuotientPathToQuotientDelete X Q p).initial = p.initial := by
  rcases p with p | r <;> rfl

/-- The source of deletion-then-quotient is contained in the source of
quotient-then-deletion. -/
theorem deleteQuotient_source_subset_quotientDelete_source
    (X Q : Set V) :
    ((G.delete Q).quotient X).source ⊆
      ((G.quotient X).delete Q).source := by
  intro x hx
  change x ∈ G.essential (G.source ∪ X) \ Q
  have hxNotRoof := hx.2
  obtain ⟨p, hp, hpavoid⟩ :=
    ((G.delete Q).not_mem_roof_iff
      (((G.delete Q).source ∪ X) \ {x}) x).1 hxNotRoof
  have hxNotQ : x ∉ Q :=
    hp.1 ▸ G.deleteWalk_start_not_mem Q p.walk hp.2.2
  refine ⟨⟨?_, ?_⟩, hxNotQ⟩
  · rcases hx.1 with hxA | hxX
    · exact Or.inl hxA.1
    · exact Or.inr hxX
  · let q : DirectedPath.FinitePath G.graph :=
      p.lift (fun {_ _} e ↦ G.delete_adj_imp e)
    apply (G.not_mem_roof_iff ((G.source ∪ X) \ {x}) x).2
    refine ⟨q, ⟨hp.1, hp.2.1⟩, ?_⟩
    have hqAvoidQ : Disjoint q.support Q := by
      change Disjoint (G.liftDeletePath Q (.inl p)).support Q
      apply G.liftDeletePath_avoids Q (.inl p)
      change p.start ∉ Q
      exact hp.1 ▸ hxNotQ
    apply Set.disjoint_left.2
    intro y hyq hyUnion
    have hyp : y ∈ p.support := by simpa [q] using hyq
    apply Set.disjoint_left.1 hpavoid hyp
    refine ⟨?_, hyUnion.2⟩
    rcases hyUnion.1 with hyA | hyX
    · exact Or.inl ⟨hyA,
        Set.disjoint_left.1 hqAvoidQ hyq⟩
    · exact Or.inr hyX

/-- An edge surviving both quotient and deletion is an edge of the
genuinely deleted ambient graph. -/
theorem quotientDelete_adj_imp_delete (X Q : Set V) {u v : V}
    (e : ((G.quotient X).delete Q).graph.Adj u v) :
    (G.delete Q).graph.Adj u v :=
  ⟨e.1.1, e.2.1, e.2.2⟩

/-- Forget the old quotient restriction while retaining the genuine
vertex deletion. -/
def liftQuotientDeletePathToDelete (X Q : Set V)
    (p : ((G.quotient X).delete Q).DPath) : (G.delete Q).DPath :=
  DirectedPath.Path.lift
    (fun {_ _} e ↦ G.quotientDelete_adj_imp_delete X Q e) p

@[simp]
theorem support_liftQuotientDeletePathToDelete
    (X Q : Set V) (p : ((G.quotient X).delete Q).DPath) :
    (G.liftQuotientDeletePathToDelete X Q p).support = p.support := by
  unfold liftQuotientDeletePathToDelete
  exact DirectedPath.Path.support_lift
    (fun {_ _} e ↦ G.quotientDelete_adj_imp_delete X Q e) p

@[simp]
theorem initial_liftQuotientDeletePathToDelete
    (X Q : Set V) (p : ((G.quotient X).delete Q).DPath) :
    (G.liftQuotientDeletePathToDelete X Q p).initial = p.initial := by
  rcases p with p | r <;> rfl

@[simp]
theorem terminal_liftQuotientDeletePathToDelete
    (X Q : Set V) (p : ((G.quotient X).delete Q).DPath) :
    (G.delete Q).terminal? (G.liftQuotientDeletePathToDelete X Q p) =
      ((G.quotient X).delete Q).terminal? p := by
  rcases p with p | r <;> rfl

/-- Lift an entire family from `(G / X) - Q` into the deleted base web
`G - Q`.  The subsequent `generalWaveQuotient` performs the necessary
terminal-suffix trimming against the possibly enlarged deleted-web roof. -/
def liftQuotientDeleteFamilyToDelete (X Q : Set V)
    (W : Set ((G.quotient X).delete Q).DPath) :
    Set (G.delete Q).DPath :=
  G.liftQuotientDeletePathToDelete X Q '' W

@[simp]
theorem vertexSet_liftQuotientDeleteFamilyToDelete
    (X Q : Set V) (W : Set ((G.quotient X).delete Q).DPath) :
    (G.delete Q).vertexSet (G.liftQuotientDeleteFamilyToDelete X Q W) =
      ((G.quotient X).delete Q).vertexSet W := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hxp⟩
    exact ⟨p, hp, by
      rw [G.support_liftQuotientDeletePathToDelete] at hxp
      exact hxp⟩
  · rintro ⟨p, hp, hxp⟩
    exact ⟨_, ⟨p, hp, rfl⟩, by
      rw [G.support_liftQuotientDeletePathToDelete]
      exact hxp⟩

@[simp]
theorem initialSet_liftQuotientDeleteFamilyToDelete
    (X Q : Set V) (W : Set ((G.quotient X).delete Q).DPath) :
    (G.delete Q).initialSet (G.liftQuotientDeleteFamilyToDelete X Q W) =
      ((G.quotient X).delete Q).initialSet W := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hpx⟩
    exact ⟨p, hp, by
      rw [G.initial_liftQuotientDeletePathToDelete] at hpx
      exact hpx⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨_, ⟨p, hp, rfl⟩, by
      rw [G.initial_liftQuotientDeletePathToDelete]
      exact hpx⟩

@[simp]
theorem terminalFrontier_liftQuotientDeleteFamilyToDelete
    (X Q : Set V) (W : Set ((G.quotient X).delete Q).DPath) :
    (G.delete Q).terminalFrontier
        (G.liftQuotientDeleteFamilyToDelete X Q W) =
      ((G.quotient X).delete Q).terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hpx⟩
    exact ⟨p, hp, by
      rw [G.terminal_liftQuotientDeletePathToDelete] at hpx
      exact hpx⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨_, ⟨p, hp, rfl⟩, by
      rw [G.terminal_liftQuotientDeletePathToDelete]
      exact hpx⟩

theorem isWarp_liftQuotientDeleteFamilyToDelete
    (X Q : Set V) {W : Set ((G.quotient X).delete Q).DPath}
    (hW : ((G.quotient X).delete Q).IsWarp W) :
    (G.delete Q).IsWarp (G.liftQuotientDeleteFamilyToDelete X Q W) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
  change Disjoint
    (G.liftQuotientDeletePathToDelete X Q p).support
    (G.liftQuotientDeletePathToDelete X Q q).support
  rw [G.support_liftQuotientDeletePathToDelete,
    G.support_liftQuotientDeletePathToDelete]
  apply hW hp hq
  intro h
  subst q
  exact hpq rfl

/-- A terminal suffix of a path starting in `source ∪ X` starts either
in the old source or in `X`. -/
theorem terminalRoofSuffix_start_mem_source_union
    (X : Set V) (p : DirectedPath.FinitePath G.graph)
    (hpstart : p.start ∈ G.source ∪ X)
    (hpfinish : p.finish ∉ G.strictRoof X) :
    (G.terminalRoofSuffix X p).start ∈ G.source ∪ X := by
  classical
  simp only [terminalRoofSuffix]
  split
  next hmeet =>
    have hlast := G.canonicalLastRoofHit_mem_essential_or_finish X p hmeet
    rcases hlast with hEss | hfinish
    · exact Or.inr hEss.1
    · have hs : (p.lastHit (G.roof X) hmeet).start = p.finish :=
        Set.mem_singleton_iff.1 hfinish
      have hroof : p.finish ∈ G.roof X := by
        rw [← hs]
        exact p.lastHit_start_mem _ _
      have hEss : p.finish ∈ G.essential X := by
        by_contra hnotEss
        exact hpfinish ⟨hroof, hnotEss⟩
      exact Or.inr (hs.symm ▸ hEss.1)
  next hnot =>
    rcases hpstart with hpA | hpX
    · exact Or.inl hpA
    · exact (hnot ⟨p.start, p.start_mem_support,
        G.subset_roof X hpX⟩).elim

/-- The quotient/deletion bridge family.  It first forgets the old
quotient restriction, retaining the genuine `Q` deletion, and then takes
the source-faithful quotient in `G - Q`. -/
noncomputable def transportQuotientDeleteWave (X Q : Set V)
    (W : Set ((G.quotient X).delete Q).DPath) :
    Set ((G.delete Q).quotient X).DPath :=
  (G.delete Q).generalWaveQuotient X
    (G.liftQuotientDeleteFamilyToDelete X Q W)

/-- Quotient and deletion commute at the level needed in Proposition 6.3:
every wave in `(G / X) - Q` canonically gives a wave in `(G - Q) / X`.
The construction trims terminal suffixes rather than asserting the false
equality of the two quotient graphs. -/
theorem isWave_transportQuotientDeleteWave
    {X Q : Set V} (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set ((G.quotient X).delete Q).DPath}
    (hW : ((G.quotient X).delete Q).IsWave W) :
    ((G.delete Q).quotient X).IsWave
      (G.transportQuotientDeleteWave X Q W) := by
  let K := G.delete Q
  let U := G.liftQuotientDeleteFamilyToDelete X Q W
  have hKNoEnter : K.NoEdgeEnters K.source := hNoEnter.delete
  have hUwarp : K.IsWarp U :=
    G.isWarp_liftQuotientDeleteFamilyToDelete X Q hW.1
  have hUinitial : K.initialSet U ⊆ K.source ∪ X := by
    rw [G.initialSet_liftQuotientDeleteFamilyToDelete]
    rintro x hx
    have hxSource := hW.2.1 hx
    rcases hxSource.1.1 with hxA | hxX
    · exact Or.inl ⟨hxA, hxSource.2⟩
    · exact Or.inr hxX
  have hSuffixInitial :
      K.initialSet (K.terminalSuffixFamily X U) ⊆ K.source ∪ X := by
    rintro x ⟨q, ⟨p, hpU, hpfinish, rfl⟩, hqx⟩
    have hs : (K.terminalRoofSuffix X p).start ∈ K.source ∪ X := by
      apply K.terminalRoofSuffix_start_mem_source_union X p
      · apply hUinitial
        exact ⟨.inl p, hpU, rfl⟩
      · exact hpfinish
    change (K.terminalRoofSuffix X p).start = x at hqx
    exact hqx ▸ hs
  refine ⟨K.isWarp_generalWaveQuotient hUwarp, ?_, ?_⟩
  · rw [transportQuotientDeleteWave,
      generalWaveQuotient,
      K.initialSet_admissibleWarpQuotient_source_formula,
      K.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
        hKNoEnter]
    rintro x ⟨hx, hxStrict⟩
    rcases hx with hx | hx
    · exact ⟨hSuffixInitial hx, hxStrict⟩
    · exact ⟨Or.inr hx, hxStrict⟩
  · intro a ha p hp
    have haOld : a ∈ ((G.quotient X).delete Q).source :=
      G.deleteQuotient_source_subset_quotientDelete_source X Q ha
    let q : DirectedPath.FinitePath ((G.quotient X).delete Q).graph :=
      p.lift (fun {_ _} e ↦
        G.deleteQuotient_adj_imp_quotientDelete X Q e)
    have hq : ((G.quotient X).delete Q).IsTargetPathFrom a q := by
      exact ⟨hp.1, hp.2⟩
    obtain ⟨t, htq, htW⟩ := hW.2.2 haOld q hq
    have htp : t ∈ p.support := by simpa [q] using htq
    have haNotStrict : a ∉ K.strictRoof X := by
      rw [K.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
        hKNoEnter] at ha
      exact ha.2
    have htNotStrict : t ∉ K.strictRoof X := by
      have htWalk : t ∈ p.walk.support := htp
      rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        (K.quotient X).graph.Adj p.walk).1 htWalk with htStart | htTail
      · exact htStart.trans hp.1 ▸ haNotStrict
      · exact (K.quotientWalk_tail_avoids p.walk htTail).1
    refine ⟨t, htp, ?_⟩
    rw [transportQuotientDeleteWave,
      K.terminalFrontier_generalWaveQuotient]
    have htU : t ∈ K.terminalFrontier U := by
      dsimp only [K, U]
      rw [G.terminalFrontier_liftQuotientDeleteFamilyToDelete]
      exact htW
    exact Or.inl ⟨htU, htNotStrict⟩

end DWeb

end Erdos599
