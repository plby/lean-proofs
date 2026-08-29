/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkAssembly

/-!
# Structural properties of the reduced safe-link wave

The reduction used after Assertion 6.4 passes through `generalWaveQuotient`.
This file records the finite-character and initial-vertex information that is
lost if one remembers only that the resulting family is a wave.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- `generalWaveQuotient` contains only finite terminal suffixes and isolated
finite paths, even when the input family itself contains rays. -/
theorem hasFiniteCharacter_generalWaveQuotient
    (X : Set V) (U : Set G.DPath) :
    (G.quotient X).HasFiniteCharacter (G.generalWaveQuotient X U) := by
  intro p hp
  unfold generalWaveQuotient admissibleWarpQuotient at hp
  rcases hp with hp | hp
  · obtain ⟨q, hpq⟩ := hp
    rcases q with ⟨q, hq⟩
    obtain ⟨r, _hrU, _hrfinish, hqr⟩ := hq
    subst q
    refine ⟨G.restrictFinitePathToQuotient X
      (G.terminalRoofSuffix X r)
      (G.pathQuotientAdmissible_terminalRoofSuffix X r _hrfinish).1
      (G.pathQuotientAdmissible_terminalRoofSuffix X r _hrfinish).2, ?_⟩
    exact hpq.trans rfl
  · obtain ⟨x, _hx, rfl⟩ := hp
    exact ⟨DirectedPath.FinitePath.trivial (G.quotient X).graph x, rfl⟩

/-- If the old family starts in the old source or in the commitment set,
then the quotient family has the same source-union property. -/
theorem initialSet_generalWaveQuotient_subset_source_union
    (X : Set V) (U : Set G.DPath)
    (hinitial : G.initialSet U ⊆ G.source ∪ X) :
    (G.quotient X).initialSet (G.generalWaveQuotient X U) ⊆
      G.source ∪ X := by
  rw [generalWaveQuotient, G.initialSet_admissibleWarpQuotient]
  rintro x (hx | hx)
  · obtain ⟨q, hq, hqx⟩ := hx
    obtain ⟨p, hpU, hpfinish, hqp⟩ := hq
    subst q
    have hpstart : p.start ∈ G.source ∪ X :=
      hinitial ⟨(.inl p : G.DPath), hpU, rfl⟩
    exact hqx ▸
      G.terminalRoofSuffix_start_mem_source_union X p hpstart hpfinish
  · exact Or.inr hx.1.1

/-- Exact ancestry of a member of `generalWaveQuotient`.  A member either
comes from restricting a finite terminal suffix of the input family, or is
one of the isolated essential commitment vertices inserted by the quotient
construction. -/
theorem mem_generalWaveQuotient_cases
    (X : Set V) (U : Set G.DPath)
    {p : (G.quotient X).DPath} (hp : p ∈ G.generalWaveQuotient X U) :
    (∃ q : G.DPath, ∃ hq : q ∈ G.terminalSuffixFamily X U,
      p = G.restrictPathToQuotient X q
        (G.pathQuotientAdmissible_terminalSuffixFamily X U q hq)) ∨
      ∃ e ∈ G.essential X \ G.vertexSet (G.terminalSuffixFamily X U),
        p = (G.quotient X).trivialPath e := by
  unfold generalWaveQuotient admissibleWarpQuotient at hp
  rcases hp with hp | hp
  · obtain ⟨q, hpq⟩ := hp
    exact Or.inl ⟨q.1, q.2, hpq⟩
  · obtain ⟨e, he, rfl⟩ := hp
    exact Or.inr ⟨e, he, rfl⟩

/-- A non-added quotient member has the support of a terminal suffix of a
finite input member and has the same terminal as that input member. -/
theorem mem_generalWaveQuotient_descends_or_trivial
    (X : Set V) (U : Set G.DPath)
    {p : (G.quotient X).DPath} (hp : p ∈ G.generalWaveQuotient X U) :
    (∃ r : DirectedPath.FinitePath G.graph,
      (.inl r : G.DPath) ∈ U ∧ r.finish ∉ G.strictRoof X ∧
        p.support ⊆ r.support ∧
        (G.quotient X).terminal? p = G.terminal? (.inl r : G.DPath)) ∨
      ∃ e ∈ G.essential X \ G.vertexSet (G.terminalSuffixFamily X U),
        p = (G.quotient X).trivialPath e := by
  rcases G.mem_generalWaveQuotient_cases X U hp with h | h
  · obtain ⟨q, ⟨r, hrU, hrfinish, rfl⟩, rfl⟩ := h
    refine Or.inl ⟨r, hrU, hrfinish, ?_, ?_⟩
    · rw [G.support_restrictPathToQuotient]
      exact G.terminalRoofSuffix_support_subset X r
    · rw [G.terminal_restrictPathToQuotient]
      simp only [G.terminal?_finite, G.terminalRoofSuffix_finish]
  · exact Or.inr h

/-- Deleting `Q` makes every vertex of `Q` unreachable to the remaining
target.  Consequently no deleted vertex can be essential for any set. -/
theorem disjoint_delete_essential_deleted (X Q : Set V) :
    Disjoint ((G.delete Q).essential X) Q := by
  rw [Set.disjoint_left]
  intro x hxEss hxQ
  obtain ⟨p, hpTarget, _hpAvoid⟩ :=
    ((G.delete Q).not_mem_roof_iff (X \ {x}) x).1 hxEss.2
  have hxStart : p.start ∈ Q := hpTarget.1.symm ▸ hxQ
  rcases p with ⟨start, finish, walk, isPath⟩
  cases walk with
  | nil =>
      exact hpTarget.2.2 hxStart
  | cons e walk =>
      exact e.2.1 hxStart

/-- Membership in a deleted terminal subfamily remembers the retained
ambient member, its support and its terminal. -/
theorem mem_deleteTerminalSubfamily_descends
    {U : Set G.DPath} {Q : Set V} (hU : G.IsWarp U)
    (hcontact : G.vertexSet U ∩ Q ⊆ G.terminalFrontier U)
    {p : (G.delete Q).DPath}
    (hp : p ∈ G.deleteTerminalSubfamily U Q hU hcontact) :
    ∃ q ∈ U, (∀ t, G.terminal? q = some t → t ∉ Q) ∧
      p.support = q.support ∧
      (G.delete Q).terminal? p = G.terminal? q := by
  unfold deleteTerminalSubfamily restrictDeleteFamily at hp
  obtain ⟨q, _hqUniv, hpq⟩ := hp
  subst p
  refine ⟨q.1, q.2.1, q.2.2, ?_, ?_⟩
  · exact G.support_restrictDeleteMember Q
      (G.terminalAvoidingSubfamily U Q)
      (G.disjoint_vertexSet_terminalAvoidingSubfamily hU hcontact) q
  · exact G.terminal?_restrictDeleteMember Q
      (G.terminalAvoidingSubfamily U Q)
      (G.disjoint_vertexSet_terminalAvoidingSubfamily hU hcontact) q

/-- The quotient/deletion bridge preserves support ancestry and terminals
on its non-added branch.  The other branch is displayed exactly as the
trivial essential path inserted by `generalWaveQuotient`. -/
theorem mem_transportQuotientDeleteWave_descends_or_trivial
    (X Q : Set V) (W : Set ((G.quotient X).delete Q).DPath)
    {p : ((G.delete Q).quotient X).DPath}
    (hp : p ∈ G.transportQuotientDeleteWave X Q W) :
    (∃ q ∈ W, p.support ⊆ q.support ∧
      ((G.delete Q).quotient X).terminal? p =
        ((G.quotient X).delete Q).terminal? q) ∨
      ∃ e ∈ (G.delete Q).essential X \
          (G.delete Q).vertexSet
            ((G.delete Q).terminalSuffixFamily X
              (G.liftQuotientDeleteFamilyToDelete X Q W)),
        p = ((G.delete Q).quotient X).trivialPath e := by
  rcases (G.delete Q).mem_generalWaveQuotient_descends_or_trivial X
      (G.liftQuotientDeleteFamilyToDelete X Q W) hp with h | h
  · obtain ⟨r, hr, _hrfinish, hsupport, hterminal⟩ := h
    obtain ⟨q, hqW, hqr⟩ := hr
    refine Or.inl ⟨q, hqW, ?_, ?_⟩
    · intro x hxp
      have hs := G.support_liftQuotientDeletePathToDelete X Q q
      rw [hqr] at hs
      exact hs ▸ hsupport hxp
    · calc
        ((G.delete Q).quotient X).terminal? p =
            (G.delete Q).terminal? (.inl r) := hterminal
        _ = (G.delete Q).terminal?
            (G.liftQuotientDeletePathToDelete X Q q) := by rw [hqr]
        _ = ((G.quotient X).delete Q).terminal? q :=
          G.terminal_liftQuotientDeletePathToDelete X Q q
  · exact Or.inr h

/-- Specialization of the bridge ancestry to the terminal-avoiding
subfamily used in the Assertion 6.4 reduction. -/
theorem mem_transport_deleteTerminalSubfamily_descends_or_trivial
    (X Q : Set V) (M : Set (G.quotient X).DPath)
    (hM : (G.quotient X).IsWarp M)
    (hcontact : (G.quotient X).vertexSet M ∩ Q ⊆
      (G.quotient X).terminalFrontier M)
    {p : ((G.delete Q).quotient X).DPath}
    (hp : p ∈ G.transportQuotientDeleteWave X Q
      ((G.quotient X).deleteTerminalSubfamily M Q hM hcontact)) :
    (∃ m ∈ M,
      (∀ t, (G.quotient X).terminal? m = some t → t ∉ Q) ∧
        p.support ⊆ m.support ∧
        ((G.delete Q).quotient X).terminal? p =
          (G.quotient X).terminal? m) ∨
      ∃ e ∈ (G.delete Q).essential X \
          (G.delete Q).vertexSet
            ((G.delete Q).terminalSuffixFamily X
              (G.liftQuotientDeleteFamilyToDelete X Q
                ((G.quotient X).deleteTerminalSubfamily M Q hM hcontact))),
        p = ((G.delete Q).quotient X).trivialPath e := by
  rcases G.mem_transportQuotientDeleteWave_descends_or_trivial X Q
      ((G.quotient X).deleteTerminalSubfamily M Q hM hcontact) hp with h | h
  · obtain ⟨q, hq, hsupport, hterminal⟩ := h
    obtain ⟨m, hm, hmAvoid, hqmSupport, hqmTerminal⟩ :=
      (G.quotient X).mem_deleteTerminalSubfamily_descends
        hM hcontact hq
    refine Or.inl ⟨m, hm, hmAvoid, hsupport.trans ?_, ?_⟩
    · exact fun _ hx ↦ hqmSupport ▸ hx
    · exact hterminal.trans hqmTerminal
  · exact Or.inr h

/-- An isolated path inserted by the final `generalWaveQuotient` is not in
the essential part of the transported wave.  The old deleted-quotient wave
roofs its source by a different terminal: equality with the inserted point
would put that point in the terminal-suffix family, contrary to the precise
condition under which the isolated path was added. -/
theorem trivialPath_not_mem_essentialWarpPart_transport
    (X Q : Set V) (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set ((G.quotient X).delete Q).DPath}
    (hW : ((G.quotient X).delete Q).IsWave W)
    {e : V}
    (he : e ∈ (G.delete Q).essential X \
      (G.delete Q).vertexSet
        ((G.delete Q).terminalSuffixFamily X
          (G.liftQuotientDeleteFamilyToDelete X Q W))) :
    ((G.delete Q).quotient X).trivialPath e ∉
      ((G.delete Q).quotient X).essentialWarpPart
        (G.transportQuotientDeleteWave X Q W) := by
  let K := G.delete Q
  let L := G.liftQuotientDeleteFamilyToDelete X Q W
  let Z := G.transportQuotientDeleteWave X Q W
  have hKNoEnter : K.NoEdgeEnters K.source := hNoEnter.delete
  have heSource : e ∈ (K.quotient X).source := by
    rw [K.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hKNoEnter]
    exact ⟨Or.inr he.1.1, fun hstrict ↦ hstrict.2 he.1⟩
  have heOldSource : e ∈ ((G.quotient X).delete Q).source :=
    G.deleteQuotient_source_subset_quotientDelete_source X Q heSource
  have heRoof : e ∈ (K.quotient X).roof
      ((K.quotient X).terminalFrontier Z \ {e}) := by
    intro p hp
    let q : DirectedPath.FinitePath ((G.quotient X).delete Q).graph :=
      p.lift (fun {_ _} edge ↦
        G.deleteQuotient_adj_imp_quotientDelete X Q edge)
    have hq : ((G.quotient X).delete Q).IsTargetPathFrom e q := by
      exact ⟨hp.1, hp.2⟩
    obtain ⟨t, htq, htW⟩ := hW.2.2 heOldSource q hq
    have htp : t ∈ p.support := by simpa [q] using htq
    have heNotStrict : e ∉ K.strictRoof X := fun hstrict ↦
      hstrict.2 he.1
    have htNotStrict : t ∉ K.strictRoof X := by
      have htWalk : t ∈ p.walk.support := htp
      rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        (K.quotient X).graph.Adj p.walk).1 htWalk with htStart | htTail
      · exact htStart.trans hp.1 ▸ heNotStrict
      · exact (K.quotientWalk_tail_avoids p.walk htTail).1
    have htL : t ∈ K.terminalFrontier L := by
      dsimp only [K, L]
      rw [G.terminalFrontier_liftQuotientDeleteFamilyToDelete]
      exact htW
    have htZ : t ∈ (K.quotient X).terminalFrontier Z := by
      change t ∈ (K.quotient X).terminalFrontier
        (K.generalWaveQuotient X L)
      rw [K.terminalFrontier_generalWaveQuotient]
      exact Or.inl ⟨htL, htNotStrict⟩
    have hte : t ≠ e := by
      intro hte
      have heSuffixTerminal : e ∈
          K.terminalFrontier (K.terminalSuffixFamily X L) := by
        rw [K.terminalFrontier_terminalSuffixFamily]
        exact ⟨hte ▸ htL, heNotStrict⟩
      apply he.2
      obtain ⟨r, hr, hre⟩ := heSuffixTerminal
      exact ⟨r, hr, K.terminal_mem_support hre⟩
    exact ⟨t, htp, htZ, hte⟩
  intro hpEssential
  obtain ⟨_hpZ, t, htTerminal, htEssential⟩ := hpEssential
  have hte : t = e := (Option.some.inj
    (((K.quotient X).terminal?_trivialPath e).symm.trans htTerminal)).symm
  exact (hte ▸ htEssential.2) heRoof

/-- Every essential member of the transported wave is on the descended
branch; the isolated paths inserted by `generalWaveQuotient` disappear
under `essentialWarpPart`. -/
theorem mem_essentialWarpPart_transport_descends
    (X Q : Set V) (hNoEnter : G.NoEdgeEnters G.source)
    {W : Set ((G.quotient X).delete Q).DPath}
    (hW : ((G.quotient X).delete Q).IsWave W)
    {p : ((G.delete Q).quotient X).DPath}
    (hp : p ∈ ((G.delete Q).quotient X).essentialWarpPart
      (G.transportQuotientDeleteWave X Q W)) :
    ∃ q ∈ W, p.support ⊆ q.support ∧
      ((G.delete Q).quotient X).terminal? p =
        ((G.quotient X).delete Q).terminal? q := by
  rcases G.mem_transportQuotientDeleteWave_descends_or_trivial X Q W hp.1 with
    h | h
  · exact h
  · obtain ⟨e, he, rfl⟩ := h
    exact (G.trivialPath_not_mem_essentialWarpPart_transport
      X Q hNoEnter hW he hp).elim

/-- Essential ancestry all the way through the terminal-avoiding reduction:
every surviving essential path comes from a retained member of `M`. -/
theorem mem_essentialWarpPart_transport_deleteTerminalSubfamily_descends
    (X Q : Set V) (hNoEnter : G.NoEdgeEnters G.source)
    (M : Set (G.quotient X).DPath)
    (hM : (G.quotient X).IsWarp M)
    (hcontact : (G.quotient X).vertexSet M ∩ Q ⊆
      (G.quotient X).terminalFrontier M)
    (hU : ((G.quotient X).delete Q).IsWave
      ((G.quotient X).deleteTerminalSubfamily M Q hM hcontact))
    {p : ((G.delete Q).quotient X).DPath}
    (hp : p ∈ ((G.delete Q).quotient X).essentialWarpPart
      (G.transportQuotientDeleteWave X Q
        ((G.quotient X).deleteTerminalSubfamily M Q hM hcontact))) :
    ∃ m ∈ M,
      (∀ t, (G.quotient X).terminal? m = some t → t ∉ Q) ∧
        p.support ⊆ m.support ∧
        ((G.delete Q).quotient X).terminal? p =
          (G.quotient X).terminal? m := by
  obtain ⟨q, hqU, hsupport, hterminal⟩ :=
    G.mem_essentialWarpPart_transport_descends X Q hNoEnter hU hp
  obtain ⟨m, hm, hmAvoid, hqmSupport, hqmTerminal⟩ :=
    (G.quotient X).mem_deleteTerminalSubfamily_descends
      hM hcontact hqU
  refine ⟨m, hm, hmAvoid, hsupport.trans ?_, hterminal.trans hqmTerminal⟩
  exact fun _ hx ↦ hqmSupport ▸ hx

end DWeb

namespace SafeLink

variable {V : Type u}

/-- The exact reduced wave from Assertion 6.4, retaining the structural
data needed by the subsequent ground-wave argument.  The final disjunction
is intentionally exact: `generalWaveQuotient` can insert an isolated
essential commitment vertex, so such a member must be handled separately
from members descended from the common quotient wave. -/
theorem exists_reducedQuotientWave_with_ancestry
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T X : Set V} (hT : G.IsTreeSet a T)
    (hXcount : X.Countable) (hXT : X ⊆ T \ {a})
    {W : Set (((G.delete {a}).quotient X).DPath)}
    (hW : ((G.delete {a}).quotient X).IsWave W)
    (hclosed : ((G.delete {a}).quotient X).vertexSet
      (((G.delete {a}).quotient X).essentialMeetingPaths W X) ∩ T ⊆ X)
    (hground : X \ nonBoundedTreeVertices G a T ⊆
      G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a X W))) :
    let base := G.delete {a}
    let H := base.quotient X
    let Q := nonBoundedTreeVertices G a T
    ∃ (U : Set (H.delete Q).DPath)
      (W' : Set ((base.delete Q).quotient X).DPath),
      (H.delete Q).IsWave U ∧
      W' = base.transportQuotientDeleteWave X Q U ∧
      ((base.delete Q).quotient X).IsWave W' ∧
      ((base.delete Q).quotient X).HasFiniteCharacter W' ∧
      ((base.delete Q).quotient X).initialSet W' ⊆
        (base.delete Q).source ∪ X ∧
      (∀ p ∈ W',
          (∃ m ∈ H.essentialWarpPart W,
            (∀ t, H.terminal? m = some t → t ∉ Q) ∧
              p.support ⊆ m.support ∧
              ((base.delete Q).quotient X).terminal? p = H.terminal? m) ∨
          ∃ e ∈ (base.delete Q).essential X \
              (base.delete Q).vertexSet
                ((base.delete Q).terminalSuffixFamily X
                  (base.liftQuotientDeleteFamilyToDelete X Q U)),
            p = ((base.delete Q).quotient X).trivialPath e) ∧
      ∀ p ∈ ((base.delete Q).quotient X).essentialWarpPart W',
        ∃ m ∈ H.essentialWarpPart W,
          (∀ t, H.terminal? m = some t → t ∉ Q) ∧
            p.support ⊆ m.support ∧
            ((base.delete Q).quotient X).terminal? p = H.terminal? m := by
  let base := G.delete {a}
  let H := base.quotient X
  let Q := nonBoundedTreeVertices G a T
  have h64 := assertion6_4_quotient G hG ha hT hXcount hXT
    hW hclosed hground
  have hforce : ∀ p ∈ H.essentialWarpPart W, ∀ q ∈ p.support,
      q ∈ Q → H.terminal? p ≠ some q →
        (p.support ∩ X).Nonempty := by
    exact nonterminal_nonBounded_contact_meets_commitment
      G hG ha hT hXcount hXT hW
  let hcontact :
      H.vertexSet (H.essentialMeetingPaths W X) ∩ Q ⊆
        H.terminalFrontier (H.essentialMeetingPaths W X) := h64.2
  let hwholeContact :
      H.vertexSet (H.essentialWarpPart W) ∩ Q ⊆
        H.terminalFrontier (H.essentialWarpPart W) :=
    H.essentialWarpPart_contact_of_nonterminal_meeting_contact
      hforce hcontact
  let U : Set (H.delete Q).DPath :=
    H.deleteTerminalSubfamily (H.essentialWarpPart W) Q
      hW.essentialWarpPart.1 hwholeContact
  have hU : (H.delete Q).IsWave U := by
    exact H.isWave_deleteTerminalSubfamily_essentialMeeting_nonterminal
      hW hforce hcontact
  let W' : Set ((base.delete Q).quotient X).DPath :=
    base.transportQuotientDeleteWave X Q U
  have hbaseNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  have hW' : ((base.delete Q).quotient X).IsWave W' := by
    exact base.isWave_transportQuotientDeleteWave hbaseNoEnter hU
  have hfinite : ((base.delete Q).quotient X).HasFiniteCharacter W' := by
    exact (base.delete Q).hasFiniteCharacter_generalWaveQuotient X
      (base.liftQuotientDeleteFamilyToDelete X Q U)
  have hLiftInitial : (base.delete Q).initialSet
      (base.liftQuotientDeleteFamilyToDelete X Q U) ⊆
        (base.delete Q).source ∪ X := by
    rw [base.initialSet_liftQuotientDeleteFamilyToDelete]
    intro x hx
    have hxSource : x ∈ (H.delete Q).source := hU.2.1 hx
    have hxH : x ∈ H.source := hxSource.1
    rw [base.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hbaseNoEnter] at hxH
    rcases hxH.1 with hxBase | hxX
    · exact Or.inl ⟨hxBase, hxSource.2⟩
    · exact Or.inr hxX
  have hInitial : ((base.delete Q).quotient X).initialSet W' ⊆
      (base.delete Q).source ∪ X := by
    exact (base.delete Q).initialSet_generalWaveQuotient_subset_source_union
      X (base.liftQuotientDeleteFamilyToDelete X Q U) hLiftInitial
  refine ⟨U, W', hU, rfl, hW', hfinite, hInitial, ?_, ?_⟩
  · intro p hp
    have hp' : p ∈ base.transportQuotientDeleteWave X Q
        (H.deleteTerminalSubfamily (H.essentialWarpPart W) Q
          hW.essentialWarpPart.1 hwholeContact) := by
      simpa only [W', U] using hp
    simpa only [H, U] using
      (base.mem_transport_deleteTerminalSubfamily_descends_or_trivial
        X Q (H.essentialWarpPart W) hW.essentialWarpPart.1
        hwholeContact hp')
  · intro p hp
    have hp' : p ∈ ((base.delete Q).quotient X).essentialWarpPart
        (base.transportQuotientDeleteWave X Q
          (H.deleteTerminalSubfamily (H.essentialWarpPart W) Q
            hW.essentialWarpPart.1 hwholeContact)) := by
      simpa only [W', U] using hp
    simpa only [H, U] using
      (base.mem_essentialWarpPart_transport_deleteTerminalSubfamily_descends
        X Q hbaseNoEnter (H.essentialWarpPart W)
        hW.essentialWarpPart.1 hwholeContact hU hp')

end SafeLink

end Erdos599
