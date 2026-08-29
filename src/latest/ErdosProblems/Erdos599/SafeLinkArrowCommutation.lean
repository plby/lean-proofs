/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkAccumTransport

/-!
# Commuting finite arrows with the Section 6 quotient transport

This file isolates the path geometry used by the finite-arrow ancestry
induction.  Terminal-roof trimming preserves a finite prefix as long as the
old endpoint survives in the later trimmed suffix.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

private theorem list_head_mem_prefix_of_suffix_contains_getLast
    {P Q S : List V}
    (hPne : P ≠ []) (hSne : S ≠ [])
    (hP : P <+: Q) (hS : S <:+ Q)
    (hlast : P.getLast hPne ∈ S) (hQ : Q.Nodup) :
    S.head hSne ∈ P := by
  classical
  obtain ⟨front, hfront⟩ := hS
  have hnodup : (front ++ S).Nodup := by simpa only [hfront] using hQ
  have hdis : ∀ a ∈ front, ∀ b ∈ S, a ≠ b :=
    (List.nodup_append.mp hnodup).2.2
  have hheadS : S.head hSne ∈ S := List.head_mem hSne
  have hheadNotFront : S.head hSne ∉ front := by
    intro hh
    exact hdis _ hh _ hheadS rfl
  have hlastNotFront : P.getLast hPne ∉ front := by
    intro hh
    exact hdis _ hh _ hlast rfl
  have hheadIdx : Q.idxOf (S.head hSne) = front.length := by
    rw [← hfront, List.idxOf_append_of_notMem hheadNotFront,
      List.idxOf_eq_zero_iff_head_eq hSne |>.2 rfl, Nat.add_zero]
  have hlastIdx : Q.idxOf (P.getLast hPne) =
      front.length + S.idxOf (P.getLast hPne) := by
    rw [← hfront, List.idxOf_append_of_notMem hlastNotFront]
  have hle : Q.idxOf (S.head hSne) ≤ Q.idxOf (P.getLast hPne) := by
    rw [hheadIdx, hlastIdx]
    exact Nat.le_add_right _ _
  apply (hP.mem_iff_idxOf_lt_length (S.head hSne)).2
  exact lt_of_le_of_lt hle
    ((hP.mem_iff_idxOf_lt_length (P.getLast hPne)).1
      (List.getLast_mem hPne))

/-- If a finite path is extended and its old endpoint remains in the
terminal-roof suffix of the extension, trimming both paths by the same roof
preserves the prefix relation. -/
theorem terminalRoofSuffix_isPrefixOf_of_isPrefixOf_of_finish_mem
    {R : Set V} {p q : FinitePath G.graph}
    (hpq : p.IsPrefixOf q)
    (hfinish : p.finish ∈ (G.terminalRoofSuffix R q).support) :
    (G.terminalRoofSuffix R p).IsPrefixOf
      (G.terminalRoofSuffix R q) := by
  classical
  by_cases hqMeet : q.walk.Meets (G.roof R)
  · let Lq := q.walk.lastHit (G.roof R) hqMeet
    rw [terminalRoofSuffix, dif_pos hqMeet] at hfinish
    change p.finish ∈ Lq.walk.support at hfinish
    have hLqStartP : Lq.startpoint ∈ p.support := by
      have h := list_head_mem_prefix_of_suffix_contains_getLast
        p.walk.support_ne_nil Lq.walk.support_ne_nil hpq Lq.support_suffix
        (by simpa only [p.walk.getLast_support] using hfinish) q.isPath
      change Lq.startpoint ∈ p.walk.support
      simpa only [Lq.walk.head_support] using h
    have hpMeet : p.walk.Meets (G.roof R) :=
      ⟨Lq.startpoint, hLqStartP, Lq.startpoint_mem⟩
    let Lp := p.walk.lastHit (G.roof R) hpMeet
    have lastHitOrder {r : FinitePath G.graph}
        (L : r.walk.LastHit (G.roof R)) {x : V}
        (hxr : x ∈ r.support) (hxR : x ∈ G.roof R) :
        r.walk.support.idxOf x ≤ r.walk.support.idxOf L.startpoint := by
      obtain ⟨front, hfront⟩ := L.support_suffix
      have hnodup : (front ++ L.walk.support).Nodup := by
        rw [hfront]
        exact r.isPath
      have hdis : ∀ a ∈ front, ∀ b ∈ L.walk.support, a ≠ b :=
        (List.nodup_append.mp hnodup).2.2
      have hstartL : L.startpoint ∈ L.walk.support := L.walk.start_mem_support
      have hstartNotFront : L.startpoint ∉ front := by
        intro hs
        exact hdis _ hs _ hstartL rfl
      have hstartIdx : r.walk.support.idxOf L.startpoint = front.length := by
        rw [← hfront, List.idxOf_append_of_notMem hstartNotFront]
        have hLne : L.walk.support ≠ [] := L.walk.support_ne_nil
        rw [List.idxOf_eq_zero_iff_head_eq hLne |>.2 L.walk.head_support,
          Nat.add_zero]
      change x ∈ r.walk.support at hxr
      rw [← hfront] at hxr
      rcases List.mem_append.mp hxr with hxfront | hxL
      · calc
          r.walk.support.idxOf x = front.idxOf x := by
            rw [← hfront]
            exact List.idxOf_append_of_mem hxfront
          _ ≤ front.length :=
            Nat.le_of_lt (List.idxOf_lt_length_of_mem hxfront)
          _ = r.walk.support.idxOf L.startpoint := hstartIdx.symm
      · rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
          G.graph.Adj L.walk).1 hxL with rfl | hxtail
        · exact le_rfl
        · exact (L.no_mem_after hxtail hxR).elim
    have hLpStartQ : Lp.startpoint ∈ q.support :=
      hpq.support_subset (Lp.support_subset Lp.walk.start_mem_support)
    have horderQ : q.walk.support.idxOf Lp.startpoint ≤
        q.walk.support.idxOf Lq.startpoint :=
      lastHitOrder Lq hLpStartQ Lp.startpoint_mem
    have horderP : p.walk.support.idxOf Lq.startpoint ≤
        p.walk.support.idxOf Lp.startpoint :=
      lastHitOrder Lp hLqStartP Lq.startpoint_mem
    have hidxLq : p.walk.support.idxOf Lq.startpoint =
        q.walk.support.idxOf Lq.startpoint :=
      hpq.idxOf_eq_of_mem hLqStartP
    have hidxLp : p.walk.support.idxOf Lp.startpoint =
        q.walk.support.idxOf Lp.startpoint :=
      hpq.idxOf_eq_of_mem (Lp.support_subset Lp.walk.start_mem_support)
    have hstarts : Lp.startpoint = Lq.startpoint := by
      apply (List.idxOf_inj hLpStartQ).1
      exact Nat.le_antisymm horderQ (by
        rw [← hidxLp, ← hidxLq]
        exact horderP)
    rw [terminalRoofSuffix, dif_pos hpMeet,
      terminalRoofSuffix, dif_pos hqMeet]
    obtain ⟨tail, htail⟩ := hpq
    have hSuffix : Lp.walk.support ++ tail <:+ q.walk.support := by
      obtain ⟨front, hfront⟩ := Lp.support_suffix
      refine ⟨front, ?_⟩
      rw [← htail, ← hfront, List.append_assoc]
    rcases List.suffix_total hSuffix Lq.support_suffix with h | h
    · have heq : Lp.walk.support ++ tail = Lq.walk.support := by
        apply List.Nodup.eq_of_head_mem_of_suffix h
        · rw [Lq.walk.head_support, ← hstarts]
          exact List.mem_append_left _ Lp.walk.start_mem_support
        · exact Lq.isPath q.isPath
      exact ⟨tail, heq⟩
    · have heq : Lq.walk.support = Lp.walk.support ++ tail := by
        have hne : Lp.walk.support ++ tail ≠ [] :=
          List.append_ne_nil_of_left_ne_nil Lp.walk.support_ne_nil tail
        apply List.Nodup.eq_of_head_mem_of_suffix (hne := hne) h
        · rw [List.head_append_of_ne_nil Lp.walk.support_ne_nil,
            Lp.walk.head_support, hstarts]
          exact Lq.walk.start_mem_support
        · exact hSuffix.nodup q.isPath
      exact ⟨tail, heq.symm⟩
  · have hpNotMeet : ¬p.walk.Meets (G.roof R) := by
      intro hpMeet
      obtain ⟨x, hxp, hxR⟩ := hpMeet
      exact hqMeet ⟨x, hpq.support_subset hxp, hxR⟩
    simpa only [terminalRoofSuffix, dif_neg hpNotMeet, dif_neg hqMeet] using hpq

/-- A finite member of a cast wave has a finite preimage with the identical
ordered vertex list.  The existing support-level cast lemma is insufficient
for commuting `suffixFrom`, whose answer depends on vertex order. -/
theorem exists_preimage_castWebWave_finite_walkSupport_terminal
    {H K : DWeb V} (h : H = K) (W : H.Wave)
    {p : FinitePath K.graph}
    (hp : (Sum.inl p : K.DPath) ∈ (h ▸ W).1) :
    ∃ q : FinitePath H.graph, (Sum.inl q : H.DPath) ∈ W.1 ∧
      p.walk.support = q.walk.support ∧ p.finish = q.finish := by
  subst K
  exact ⟨p, hp, rfl, rfl⟩

/-- Ordered finite provenance for a non-isolated member of a transported
wave.  In addition to the old finite member and survival condition, this
retains the complete ordered vertex list of its terminal-roof suffix. -/
theorem exists_old_finite_path_walkSupport_of_mem_waveToLargerQuotient_of_not_mem
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave)
    {p : FinitePath (G.quotient Y).graph}
    (hp : (Sum.inl p : (G.quotient Y).DPath) ∈
      (G.waveToLargerQuotient hNoEnter hXY W).1)
    {z : V} (hzp : z ∈ p.support) (hzY : z ∉ Y) :
    ∃ q : FinitePath (G.quotient X).graph,
      (Sum.inl q : (G.quotient X).DPath) ∈ W.1 ∧
      q.finish ∉ (G.quotient X).strictRoof Y ∧
      p.walk.support =
        ((G.quotient X).terminalRoofSuffix Y q).walk.support ∧
      p.finish = q.finish := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    ⟨H.generalWaveQuotient Y W.1,
      H.isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport :
      G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  rw [htransport] at hp
  obtain ⟨p₀, hp₀, hpWalk, hpFinish⟩ :=
    DWeb.exists_preimage_castWebWave_finite_walkSupport_terminal heq Z hp
  have hzp₀ : z ∈ p₀.support := by
    change z ∈ p.walk.support at hzp
    change z ∈ p₀.walk.support
    rw [← hpWalk]
    exact hzp
  change (Sum.inl p₀ : (H.quotient Y).DPath) ∈
    H.generalWaveQuotient Y W.1 at hp₀
  unfold generalWaveQuotient admissibleWarpQuotient at hp₀
  rcases hp₀ with hp₀ | hp₀
  · obtain ⟨r, hr⟩ := hp₀
    have hp₀eq : (Sum.inl p₀ : (H.quotient Y).DPath) =
        H.restrictPathToQuotient Y r.1
          (H.pathQuotientAdmissible_terminalSuffixFamily Y W.1
            r.1 r.2) := hr
    obtain ⟨q, hqW, hqfin, hrq⟩ := r.2
    have hrEq : r =
        ⟨(Sum.inl ((G.quotient X).terminalRoofSuffix Y q) : H.DPath),
          q, hqW, hqfin, rfl⟩ := Subtype.ext hrq
    subst r
    have hp₀eq' : p₀ = H.restrictFinitePathToQuotient Y
        (H.terminalRoofSuffix Y q)
        (H.pathQuotientAdmissible_terminalSuffixFamily Y W.1
          (Sum.inl (H.terminalRoofSuffix Y q) : H.DPath)
          ⟨q, hqW, hqfin, rfl⟩).1
        (H.pathQuotientAdmissible_terminalSuffixFamily Y W.1
          (Sum.inl (H.terminalRoofSuffix Y q) : H.DPath)
          ⟨q, hqW, hqfin, rfl⟩).2 := by
      exact Sum.inl.inj hp₀eq
    refine ⟨q, hqW, hqfin, ?_, ?_⟩
    · calc
        p.walk.support = p₀.walk.support := hpWalk
        _ = (H.terminalRoofSuffix Y q).walk.support := by
          rw [hp₀eq']
          exact H.support_restrictWalkToQuotient Y
            (H.terminalRoofSuffix Y q).walk _ _
    · exact hpFinish.trans (by
        rw [hp₀eq']
        exact H.terminalRoofSuffix_finish Y q)
  · obtain ⟨e, he, hp₀eq⟩ := hp₀
    have hze : z = e := by
      have hzt : z ∈ ((H.quotient Y).trivialPath e).support := by
        rw [hp₀eq]
        exact hzp₀
      simpa using hzt
    exact (hzY (hze ▸ he.1.1)).elim

/-- If `p` is a finite prefix of `q` and `g` has the same ordered vertex
list as `q` (possibly in another graph), then splicing the support of `p`
with the canonical suffix of `g` at `p.finish` recovers all of `g`'s
support. -/
theorem support_union_suffixFrom_eq_of_isPrefixOf_of_walkSupport_eq
    {D E : Digraph V} (p q : FinitePath D) (g : FinitePath E)
    (hpq : p.IsPrefixOf q) (hgq : g.walk.support = q.walk.support)
    (hx : p.finish ∈ g.support) :
    p.support ∪
        (DirectedPath.Path.suffixFrom
          (Sum.inl g : DirectedPath.Path E) p.finish hx).support =
      g.support := by
  classical
  obtain ⟨tail, htail⟩ := hpq
  have hdesired : p.finish :: tail <:+ g.walk.support := by
    refine ⟨p.walk.support.dropLast, ?_⟩
    calc
      p.walk.support.dropLast ++ p.finish :: tail =
          (p.walk.support.dropLast ++ [p.finish]) ++ tail := by simp
      _ = p.walk.support ++ tail := by
        have hlast := List.dropLast_append_getLast p.walk.support_ne_nil
        simpa only [p.walk.getLast_support] using
          congrArg (fun l : List V ↦ l ++ tail) hlast
      _ = q.walk.support := htail
      _ = g.walk.support := hgq.symm
  have hselected : (g.suffixData p.finish hx).walk.support <:+
      g.walk.support := g.suffixData_support_suffix p.finish hx
  have hsuffix : (g.suffixData p.finish hx).walk.support =
      p.finish :: tail := by
    rcases List.suffix_total hselected hdesired with h | h
    · apply List.Nodup.eq_of_head_mem_of_suffix (hne := by simp) h
      · change p.finish ∈ (g.suffixData p.finish hx).walk.support
        exact (g.suffixData p.finish hx).walk.start_mem_support
      · exact hdesired.nodup g.isPath
    · symm
      apply List.Nodup.eq_of_head_mem_of_suffix
        (hne := (g.suffixData p.finish hx).walk.support_ne_nil) h
      · rw [(g.suffixData p.finish hx).walk.head_support]
        exact List.mem_cons_self
      · exact hselected.nodup g.isPath
  ext x
  change x ∈ p.walk.support ∨
      x ∈ (g.suffixData p.finish hx).walk.support ↔
    x ∈ g.walk.support
  rw [hsuffix, hgq, ← htail]
  constructor
  · rintro (hxp | hxs)
    · exact List.mem_append_left _ hxp
    · rcases List.mem_cons.mp hxs with hxeq | hxtail
      · subst x
        exact List.mem_append_left _ p.finish_mem_support
      · exact List.mem_append_right _ hxtail
  · intro hxappend
    rcases List.mem_append.mp hxappend with hxp | hxtail
    · exact Or.inl hxp
    · exact Or.inr (List.mem_cons_of_mem _ hxtail)

/-- A finite final-closure suffix representative can be transported to the
next carrier and then extended to a finite member of the chosen successor.
The intermediate transported path still has exactly the prescribed final
suffix, and it is an ordered prefix of the successor member. -/
theorem exists_sectionSixAccumNext_finite_extension_finalSuffix
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage) {X : Set V}
    (hNextX : G.sectionSixAccumNextCarrier F K Y Q T s ⊆ X)
    (W : (G.quotient X).Wave)
    (p : DirectedPath.FinitePath (G.quotient X).graph)
    (hp : (Sum.inl p : (G.quotient X).DPath) ∈ W.1)
    (q : DirectedPath.FinitePath (G.quotient s.carrier).graph)
    (hq : (Sum.inl q : (G.quotient s.carrier).DPath) ∈ s.wave.1)
    (hSuffix : ((G.quotient s.carrier).terminalRoofSuffix X q).support =
      p.support)
    (hFinish : q.finish = p.finish) :
    ∃ a : DirectedPath.FinitePath (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).graph,
      (Sum.inl a : (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) ∈
          (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1 ∧
      ((G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).terminalRoofSuffix X a).support =
          p.support ∧
      a.finish = p.finish ∧
      ∃ b : DirectedPath.FinitePath (G.quotient
          (G.sectionSixAccumNextCarrier F K Y Q T s)).graph,
        (Sum.inl b : (G.quotient
          (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) ∈
            (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 ∧
        a.IsPrefixOf b := by
  have hCarrierNext : s.carrier ⊆
      G.sectionSixAccumNextCarrier F K Y Q T s :=
    G.sectionSixAccumStage_carrier_subset_next F K Y Q T s
  have hCarrierX : s.carrier ⊆ X := hCarrierNext.trans hNextX
  have hpSurvivesX : p.finish ∉
      (G.quotient s.carrier).strictRoof X :=
    G.not_mem_strictRoof_of_mem_crossQuotientWave hNoEnter
      hCarrierX W hp p.finish_mem_support
  have hStrictMono : (G.quotient s.carrier).strictRoof
      (G.sectionSixAccumNextCarrier F K Y Q T s) ⊆
      (G.quotient s.carrier).strictRoof X := by
    apply (G.quotient s.carrier).strictRoof_mono_of_roof_mono
    exact (G.quotient s.carrier).roof_mono hNextX
  have hqSurvives : q.finish ∉ (G.quotient s.carrier).strictRoof
      (G.sectionSixAccumNextCarrier F K Y Q T s) := by
    intro hqStrict
    exact hpSurvivesX (hFinish ▸ hStrictMono hqStrict)
  obtain ⟨a, haOld, haTerminal, haSuffix⟩ :=
    G.exists_mem_waveToLargerQuotient_of_old_finite_finalSuffix
      hNoEnter hCarrierNext hNextX s.wave q hq hqSurvives
  obtain ⟨bPath, hbNext, hab⟩ :=
    (G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s).1
      (Sum.inl a) haOld
  obtain ⟨b, rfl⟩ :=
    G.sectionSixAccumNext_hasFiniteCharacter hNoEnter F K Y Q T s hbNext
  have haFinish : a.finish = p.finish := by
    have : a.finish = q.finish := by
      simpa only [DWeb.terminal?_finite, Option.some.injEq] using haTerminal
    exact this.trans hFinish
  refine ⟨a, haOld, haSuffix.trans hSuffix, haFinish, b, hbNext, ?_⟩
  exact hab

/-- Ordered candidate commutation inside one successor warp.  The old
transported path is a prefix of `b`; the candidate-side path is the final
`S`-suffix of `r`.  Since `b` and `r` meet at the arrow contact, warp
disjointness identifies them, and the ordered suffix calculation shows that
the whole appended arrow is exactly their final `S`-suffix. -/
theorem terminalRoofSuffix_support_eq_appendAt_of_candidate_same_warp
    {K H : DWeb V} {A : Set K.DPath} (hA : K.IsWarp A)
    {U W : Set H.DPath} (f p : DirectedPath.FinitePath H.graph)
    (hf : (Sum.inl f : H.DPath) ∈ U)
    (c : H.ArrowCandidate U W f)
    {g : DirectedPath.FinitePath H.graph} (hcPath : c.path = Sum.inl g)
    {S : Set V}
    (a b r : DirectedPath.FinitePath K.graph)
    (hbA : (Sum.inl b : K.DPath) ∈ A)
    (hrA : (Sum.inl r : K.DPath) ∈ A)
    (hab : a.IsPrefixOf b)
    (haSuffix : (K.terminalRoofSuffix S a).support = f.support)
    (haFinish : a.finish = f.finish)
    (hgSuffix : g.walk.support =
      (K.terminalRoofSuffix S r).walk.support)
    (happend : DirectedPath.Path.appendAt f c.path c.finish_mem
      (c.appendable hf) = Sum.inl p) :
    (K.terminalRoofSuffix S b).support = p.support ∧
      b.finish = p.finish := by
  obtain ⟨cpath, cmem, cfinish, cclean⟩ := c
  dsimp only at hcPath happend ⊢
  subst cpath
  have hcontactB : f.finish ∈ b.support := by
    rw [← haFinish]
    exact hab.support_subset a.finish_mem_support
  have hcontactG : f.finish ∈ g.support := by
    exact cfinish
  have hcontactRSuffix : f.finish ∈
      (K.terminalRoofSuffix S r).support := by
    change f.finish ∈ (K.terminalRoofSuffix S r).walk.support
    rw [← hgSuffix]
    exact hcontactG
  have hcontactR : f.finish ∈ r.support :=
    K.terminalRoofSuffix_support_subset S r hcontactRSuffix
  have hbr : b = r := by
    by_contra hne
    exact Set.disjoint_left.1
      (hA hbA hrA (fun h ↦ hne (Sum.inl.inj h))) hcontactB hcontactR
  subst r
  have haFinishSuffix : (K.terminalRoofSuffix S a).finish = f.finish := by
    simpa only [K.terminalRoofSuffix_finish] using haFinish
  have hcontactBSuffix : a.finish ∈
      (K.terminalRoofSuffix S b).support := by
    rw [haFinish]
    change f.finish ∈ (K.terminalRoofSuffix S b).walk.support
    rw [← hgSuffix]
    exact hcontactG
  have hpref : (K.terminalRoofSuffix S a).IsPrefixOf
      (K.terminalRoofSuffix S b) :=
    K.terminalRoofSuffix_isPrefixOf_of_isPrefixOf_of_finish_mem
      hab hcontactBSuffix
  have hunion := support_union_suffixFrom_eq_of_isPrefixOf_of_walkSupport_eq
    (K.terminalRoofSuffix S a) (K.terminalRoofSuffix S b) g
      hpref hgSuffix (by rw [haFinishSuffix]; exact hcontactG)
  have happSupport := congrArg DirectedPath.Path.support happend
  have hsupport : (K.terminalRoofSuffix S b).support = p.support := by
    rw [DirectedPath.Path.support_appendAt] at happSupport
    calc
      (K.terminalRoofSuffix S b).support = g.support := by
        ext x
        change x ∈ (K.terminalRoofSuffix S b).walk.support ↔
          x ∈ g.walk.support
        rw [hgSuffix]
      _ = f.support ∪
          (DirectedPath.Path.suffixFrom (Sum.inl g : H.DPath)
            f.finish cfinish).support := by
        simpa only [haSuffix, haFinishSuffix] using hunion.symm
      _ = p.support := happSupport
  have hgbFinish : g.finish = b.finish := by
    calc
      g.finish = g.walk.support.getLast g.walk.support_ne_nil :=
        g.walk.getLast_support.symm
      _ = (K.terminalRoofSuffix S b).walk.support.getLast
          (K.terminalRoofSuffix S b).walk.support_ne_nil :=
        List.getLast_congr g.walk.support_ne_nil
          (K.terminalRoofSuffix S b).walk.support_ne_nil hgSuffix
      _ = (K.terminalRoofSuffix S b).finish :=
        (K.terminalRoofSuffix S b).walk.getLast_support
      _ = b.finish := K.terminalRoofSuffix_finish S b
  have hgpFinish : g.finish = p.finish := by
    have hterm : H.terminal? (Sum.inl g : H.DPath) =
        H.terminal? (Sum.inl p : H.DPath) := by
      calc
        H.terminal? (Sum.inl g : H.DPath) =
            H.terminal? (DirectedPath.Path.appendAt f (Sum.inl g) cfinish
              (ArrowCandidate.appendable
                ⟨Sum.inl g, cmem, cfinish, cclean⟩ hf)) :=
          (DirectedPath.Path.terminal?_appendAt f (Sum.inl g) cfinish
            (ArrowCandidate.appendable
              ⟨Sum.inl g, cmem, cfinish, cclean⟩ hf)).symm
        _ = H.terminal? (Sum.inl p : H.DPath) :=
          congrArg H.terminal? happend
    simpa only [DirectedPath.Path.terminal?_finite,
      Option.some.injEq] using hterm
  exact ⟨hsupport, hgbFinish.symm.trans hgpFinish⟩

/-- Appending a candidate to a trivial source path recovers the candidate
path itself.  Source normalization is used only to identify the contact with
the candidate's initial vertex. -/
theorem support_finish_eq_candidate_of_appendAt_trivial
    (hNoEnter : G.NoEdgeEnters G.source)
    {U W : Set G.DPath} (f p : DirectedPath.FinitePath G.graph)
    (hf : (Sum.inl f : G.DPath) ∈ U)
    (hfSource : f.start ∈ G.source)
    (hfTrivial : (Sum.inl f : G.DPath) = G.trivialPath f.start)
    (c : G.ArrowCandidate U W f)
    {g : DirectedPath.FinitePath G.graph} (hcPath : c.path = Sum.inl g)
    (happend : DirectedPath.Path.appendAt f c.path c.finish_mem
      (c.appendable hf) = Sum.inl p) :
    p.support = g.support ∧ p.finish = g.finish := by
  obtain ⟨cpath, cmem, cfinish, cclean⟩ := c
  dsimp only at hcPath happend ⊢
  subst cpath
  have hfSupport : f.support = ({f.start} : Set V) := by
    change DirectedPath.Path.support (Sum.inl f : G.DPath) = {f.start}
    rw [hfTrivial, G.support_trivialPath]
  have hfFinish : f.finish = f.start := by
    exact Set.mem_singleton_iff.mp (hfSupport ▸ f.finish_mem_support)
  have hcontactStart : f.finish = g.start :=
    DWeb.NoEdgeEnters.eq_initial_of_mem_path (G := G) hNoEnter
      (Sum.inl g : G.DPath) cfinish (hfFinish ▸ hfSource)
  have cfinishG : f.finish ∈ g.support := cfinish
  have hsuffix : (DirectedPath.Path.suffixFrom
      (Sum.inl g : G.DPath) f.finish cfinish).support = g.support := by
    change (g.suffixFromAux f.finish cfinishG).support = g.support
    have hsuppList : (g.suffixData f.finish cfinishG).walk.support =
        g.walk.support := by
      apply List.Nodup.eq_of_head_mem_of_suffix
        (hne := g.walk.support_ne_nil)
        (g.suffixData_support_suffix f.finish cfinishG)
      · simpa only [g.walk.head_support, ← hcontactStart] using
          (g.suffixData f.finish cfinishG).walk.start_mem_support
      · exact g.isPath
    ext x
    change x ∈ (g.suffixData f.finish cfinishG).walk.support ↔
      x ∈ g.walk.support
    rw [hsuppList]
  have happSupport := congrArg DirectedPath.Path.support happend
  rw [DirectedPath.Path.support_appendAt, hsuffix] at happSupport
  have hfg : f.support ⊆ g.support := by
    rw [hfSupport]
    intro x hx
    have hxEq : x = g.start := by
      simpa only [Set.mem_singleton_iff, ← hcontactStart, hfFinish] using hx
    exact hxEq ▸ g.start_mem_support
  have hpSupport : p.support = g.support := by
    rw [Set.union_eq_right.mpr hfg] at happSupport
    exact happSupport.symm
  have hpFinish : p.finish = g.finish := by
    have hterm : G.terminal? (Sum.inl p : G.DPath) =
        G.terminal? (Sum.inl g : G.DPath) := by
      calc
        G.terminal? (Sum.inl p : G.DPath) =
            G.terminal? (DirectedPath.Path.appendAt f (Sum.inl g) cfinish
              (ArrowCandidate.appendable
                ⟨Sum.inl g, cmem, cfinish, cclean⟩ hf)) :=
          congrArg G.terminal? happend.symm
        _ = G.terminal? (Sum.inl g : G.DPath) :=
          DirectedPath.Path.terminal?_appendAt f (Sum.inl g) cfinish
            (ArrowCandidate.appendable
              ⟨Sum.inl g, cmem, cfinish, cclean⟩ hf)
    simpa only [G.terminal?_finite, Option.some.injEq] using hterm
  exact ⟨hpSupport, hpFinish⟩

/-- A trivial right-hand candidate cannot enlarge the old finite path. -/
theorem support_finish_eq_left_of_candidate_trivial
    {U W : Set G.DPath} (f p : DirectedPath.FinitePath G.graph)
    (hf : (Sum.inl f : G.DPath) ∈ U)
    (c : G.ArrowCandidate U W f)
    {g : DirectedPath.FinitePath G.graph} (hcPath : c.path = Sum.inl g)
    (hgTrivial : (Sum.inl g : G.DPath) = G.trivialPath g.start)
    (happend : DirectedPath.Path.appendAt f c.path c.finish_mem
      (c.appendable hf) = Sum.inl p) :
    p.support = f.support ∧ p.finish = f.finish := by
  obtain ⟨cpath, cmem, cfinish, cclean⟩ := c
  dsimp only at hcPath happend ⊢
  subst cpath
  have hgSupport : g.support = ({g.start} : Set V) := by
    change DirectedPath.Path.support (Sum.inl g : G.DPath) = {g.start}
    rw [hgTrivial, G.support_trivialPath]
  have hcontact : f.finish = g.start := by
    have : f.finish ∈ ({g.start} : Set V) := hgSupport ▸ cfinish
    exact Set.mem_singleton_iff.mp this
  have cfinishG : f.finish ∈ g.support := cfinish
  have hsuffix : (DirectedPath.Path.suffixFrom
      (Sum.inl g : G.DPath) f.finish cfinish).support =
      ({f.finish} : Set V) := by
    change (g.suffixFromAux f.finish cfinishG).support = {f.finish}
    have hsub : (g.suffixFromAux f.finish cfinishG).support ⊆
        ({f.finish} : Set V) := by
      intro x hx
      have hxg : x ∈ g.support :=
        g.suffixFromAux_support_subset f.finish cfinishG hx
      have : x = g.start := Set.mem_singleton_iff.mp (hgSupport ▸ hxg)
      exact Set.mem_singleton_iff.mpr (this.trans hcontact.symm)
    apply Set.Subset.antisymm hsub
    intro x hx
    have hxEq : x = f.finish := Set.mem_singleton_iff.mp hx
    subst x
    exact (g.suffixFromAux f.finish cfinishG).start_mem_support
  have happSupport := congrArg DirectedPath.Path.support happend
  have hunion : f.support ∪ ({f.finish} : Set V) = f.support := by
    apply Set.union_eq_left.mpr
    intro x hx
    have hxEq : x = f.finish := Set.mem_singleton_iff.mp hx
    exact hxEq ▸ f.finish_mem_support
  rw [DirectedPath.Path.support_appendAt, hsuffix, hunion] at happSupport
  have hterm : G.terminal? (Sum.inl p : G.DPath) =
      G.terminal? (Sum.inl g : G.DPath) := by
    calc
      G.terminal? (Sum.inl p : G.DPath) =
          G.terminal? (DirectedPath.Path.appendAt f (Sum.inl g) cfinish
            (ArrowCandidate.appendable
              ⟨Sum.inl g, cmem, cfinish, cclean⟩ hf)) :=
        congrArg G.terminal? happend.symm
      _ = G.terminal? (Sum.inl g : G.DPath) :=
        DirectedPath.Path.terminal?_appendAt f (Sum.inl g) cfinish
          (ArrowCandidate.appendable
            ⟨Sum.inl g, cmem, cfinish, cclean⟩ hf)
  have hpFinishG : p.finish = g.finish := by
    simpa only [G.terminal?_finite, Option.some.injEq] using hterm
  have hgFinish : g.finish = g.start := by
    exact Set.mem_singleton_iff.mp (hgSupport ▸ g.finish_mem_support)
  exact ⟨happSupport.symm,
    hpFinishG.trans (hgFinish.trans hcontact.symm)⟩

end DWeb

end Erdos599
