/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.QuotientRoofTransport
import ErdosProblems.Erdos599.SafeLinkBridge
import ErdosProblems.Erdos599.SafeLinkClosure
import ErdosProblems.Erdos599.SafeLinkGround

/-!
# Final strict-roof bookkeeping for the Section 6 closure

This file supplies the part of Proposition 6.3(c) which is not merely a
set-theoretic consequence of the closing recurrence.  A bounded tree vertex
comes with a quotient wave over its grounding set.  Once that grounding set
has been inserted, roof maximality, the accumulated arrow, transport to the
raw-union quotient, and the final countable arrow successively enlarge its
roof.  The first lemma below shows that strict roofs are monotone under this
roof order; this lets the original strict witness pass through the whole
chain without an auxiliary essential-frontier disjointness hypothesis.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DirectedPath.FinitePath

variable {V : Type u} {D : Digraph V}

/-- A proper suffix of a finite simple path cannot contain the original
initial vertex. -/
theorem start_not_mem_suffixFromAux_of_ne (p : FinitePath D) {x : V}
    (hx : x ∈ p.support) (hxp : x ≠ p.start) :
    p.start ∉ (p.suffixFromAux x hx).support := by
  intro hstart
  have hsuffix := p.suffixData_support_suffix x hx
  obtain ⟨l, hl⟩ := hsuffix
  have hnodup : (l ++ (p.suffixData x hx).walk.support).Nodup := by
    rw [hl]
    exact p.isPath
  have hdisjoint := (List.nodup_append.mp hnodup).2.2
  cases l with
  | nil =>
      have heq : (p.suffixData x hx).walk.support = p.walk.support := by
        simpa using hl
      apply hxp
      have hheads := congrArg (fun l => l[0]?) heq
      rw [RelationalRoof.getElem?_zero_support D.Adj
          (p.suffixData x hx).walk,
        RelationalRoof.getElem?_zero_support D.Adj p.walk] at hheads
      exact Option.some.inj hheads
  | cons a l =>
      have ha : a = p.start := by
        have hheads := congrArg (fun l => l[0]?) hl
        rw [RelationalRoof.getElem?_zero_support D.Adj p.walk] at hheads
        simpa using Option.some.inj hheads
      have haLeft : p.start ∈ a :: l := by simp [ha]
      have haRight : p.start ∈ (p.suffixData x hx).walk.support := hstart
      exact hdisjoint p.start haLeft p.start haRight rfl

/-- The support of a last hit is unique on a simple path, independently of
the classical witness chosen for the last hit. -/
theorem lastHit_support_eq {p : FinitePath D} {S : Set V}
    (L M : p.walk.LastHit S) : L.walk.support = M.walk.support := by
  rcases List.suffix_or_suffix_of_suffix
      L.support_suffix M.support_suffix with hLM | hML
  · have hstartL : L.startpoint ∈ M.walk.support :=
      hLM.subset L.walk.start_mem_support
    have hcases : L.startpoint = M.startpoint ∨
        L.startpoint ∈ M.walk.support.tail := by
      have hhead : M.startpoint ∈ M.walk.support.head? := by
        rw [List.head?_eq_head M.walk.support_ne_nil, M.walk.head_support]
        simp
      have hs := List.eq_cons_of_mem_head? hhead
      rw [hs] at hstartL ⊢
      simpa using hstartL
    have hstarts : L.startpoint = M.startpoint := by
      rcases hcases with h | h
      · exact h
      · exact False.elim (M.no_mem_after h L.startpoint_mem)
    apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := M.walk.support_ne_nil) hLM
    · rw [M.walk.head_support, ← hstarts]
      exact L.walk.start_mem_support
    · exact M.isPath p.isPath
  · symm
    have hstartM : M.startpoint ∈ L.walk.support :=
      hML.subset M.walk.start_mem_support
    have hcases : M.startpoint = L.startpoint ∨
        M.startpoint ∈ L.walk.support.tail := by
      have hhead : L.startpoint ∈ L.walk.support.head? := by
        rw [List.head?_eq_head L.walk.support_ne_nil, L.walk.head_support]
        simp
      have hs := List.eq_cons_of_mem_head? hhead
      rw [hs] at hstartM ⊢
      simpa using hstartM
    have hstarts : M.startpoint = L.startpoint := by
      rcases hcases with h | h
      · exact h
      · exact False.elim (L.no_mem_after h M.startpoint_mem)
    apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := L.walk.support_ne_nil) hML
    · rw [L.walk.head_support, ← hstarts]
      exact M.walk.start_mem_support
    · exact L.isPath p.isPath

/-- The support of a last hit depends only on the ordered vertex list, not
on the ambient edge relation used to type that list. -/
theorem lastHit_support_eq_of_support_eq
    {E : Digraph V} {p : FinitePath D} {q : FinitePath E}
    {S T : Set V}
    (hpq : p.walk.support = q.walk.support)
    (hST : S = T) (L : p.walk.LastHit S) (M : q.walk.LastHit T) :
    L.walk.support = M.walk.support := by
  subst T
  have hMsuffix : M.walk.support <:+ p.walk.support := by
    rw [hpq]
    exact M.support_suffix
  rcases List.suffix_or_suffix_of_suffix L.support_suffix hMsuffix with
      hLM | hML
  · have hstartL : L.startpoint ∈ M.walk.support :=
      hLM.subset L.walk.start_mem_support
    have hcases : L.startpoint = M.startpoint ∨
        L.startpoint ∈ M.walk.support.tail := by
      have hhead : M.startpoint ∈ M.walk.support.head? := by
        rw [List.head?_eq_head M.walk.support_ne_nil, M.walk.head_support]
        simp
      have hs := List.eq_cons_of_mem_head? hhead
      rw [hs] at hstartL ⊢
      simpa using hstartL
    have hstarts : L.startpoint = M.startpoint := by
      rcases hcases with h | h
      · exact h
      · exact False.elim (M.no_mem_after h L.startpoint_mem)
    apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := M.walk.support_ne_nil) hLM
    · rw [M.walk.head_support, ← hstarts]
      exact L.walk.start_mem_support
    · exact M.isPath q.isPath
  · symm
    have hstartM : M.startpoint ∈ L.walk.support :=
      hML.subset M.walk.start_mem_support
    have hcases : M.startpoint = L.startpoint ∨
        M.startpoint ∈ L.walk.support.tail := by
      have hhead : L.startpoint ∈ L.walk.support.head? := by
        rw [List.head?_eq_head L.walk.support_ne_nil, L.walk.head_support]
        simp
      have hs := List.eq_cons_of_mem_head? hhead
      rw [hs] at hstartM ⊢
      simpa using hstartM
    have hstarts : M.startpoint = L.startpoint := by
      rcases hcases with h | h
      · exact h
      · exact False.elim (L.no_mem_after h M.startpoint_mem)
    apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := L.walk.support_ne_nil) hML
    · rw [L.walk.head_support, ← hstarts]
      exact M.walk.start_mem_support
    · exact L.isPath p.isPath

end DirectedPath.FinitePath

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Strict roofs are monotone in the roof preorder.  The nontrivial point
is that, if `v` were essential for the later separator, an avoiding path
from `v` could be cut after its first encounter with the earlier separator;
the remaining proper suffix is then forced to meet the later separator away
from `v`, a contradiction. -/
theorem strictRoof_mono_of_roof_mono {S T : Set V}
    (hST : G.roof S ⊆ G.roof T) :
    G.strictRoof S ⊆ G.strictRoof T := by
  intro v hv
  refine ⟨hST hv.1, ?_⟩
  intro hvEssT
  have hvWithout : v ∈ G.roof (S \ {v}) := by
    by_cases hvS : v ∈ S
    · by_contra h
      exact hv.2 ⟨hvS, h⟩
    · apply G.roof_mono (show S ⊆ S \ {v} by
        intro x hx
        exact ⟨hx, fun hxv ↦ hvS (hxv ▸ hx)⟩)
      exact hv.1
  obtain ⟨p, hp, hpAvoid⟩ :=
    (G.not_mem_roof_iff (T \ {v}) v).1 hvEssT.2
  obtain ⟨s, hsp, hsS⟩ := hvWithout p hp
  have hsv : s ≠ v := by
    intro hsv
    exact hsS.2 (hsv ▸ Set.mem_singleton v)
  let q := p.suffixFromAux s hsp
  have hqTarget : G.IsTargetPathFrom s q := ⟨rfl, hp.2⟩
  obtain ⟨r, hrq, hrT⟩ := hST (G.subset_roof S hsS.1) q hqTarget
  have hrv : r ≠ v := by
    intro hrv
    have hvq : v ∈ q.support := hrv ▸ hrq
    exact p.start_not_mem_suffixFromAux_of_ne hsp
      (by simpa [hp.1] using hsv) (by simpa [hp.1] using hvq)
  exact Set.disjoint_left.1 hpAvoid
    (p.suffixFromAux_support_subset s hsp hrq) ⟨hrT, by
      intro hrv'
      exact hrv (Set.mem_singleton_iff.mp hrv')⟩

/-- Enlarging the roof used for terminal trimming can only shorten the
retained suffix. -/
theorem terminalRoofSuffix_support_mono {R S : Set V}
    (hRS : G.roof R ⊆ G.roof S)
    (p : DirectedPath.FinitePath G.graph) :
    (G.terminalRoofSuffix S p).support ⊆
      (G.terminalRoofSuffix R p).support := by
  classical
  by_cases hS : p.walk.Meets (G.roof S)
  · by_cases hR : p.walk.Meets (G.roof R)
    · rw [terminalRoofSuffix, dif_pos hS, terminalRoofSuffix, dif_pos hR]
      let LS := p.walk.lastHit (G.roof S) hS
      let LR := p.walk.lastHit (G.roof R) hR
      rcases List.suffix_or_suffix_of_suffix
          LS.support_suffix LR.support_suffix with hLS | hLR
      · exact hLS.subset
      · have hstartR : LR.startpoint ∈ LS.walk.support :=
          hLR.subset LR.walk.start_mem_support
        have hcases : LR.startpoint = LS.startpoint ∨
            LR.startpoint ∈ LS.walk.support.tail := by
          have hhead : LS.startpoint ∈ LS.walk.support.head? := by
            rw [List.head?_eq_head LS.walk.support_ne_nil,
              LS.walk.head_support]
            simp
          have hs := List.eq_cons_of_mem_head? hhead
          rw [hs] at hstartR ⊢
          simpa using hstartR
        have hstarts : LR.startpoint = LS.startpoint := by
          rcases hcases with h | h
          · exact h
          · exact False.elim (LS.no_mem_after h (hRS LR.startpoint_mem))
        have heq : LR.walk.support = LS.walk.support := by
          apply List.Nodup.eq_of_head_mem_of_suffix
            (hne := LS.walk.support_ne_nil) hLR
          · rw [LS.walk.head_support, ← hstarts]
            exact LR.walk.start_mem_support
          · exact LS.isPath p.isPath
        change LS.walk.support ⊆ LR.walk.support
        rw [heq]
        exact Set.Subset.rfl
    · rw [terminalRoofSuffix, dif_pos hS, terminalRoofSuffix, dif_neg hR]
      exact p.lastHit_support_subset (G.roof S) hS
  · have hR : ¬p.walk.Meets (G.roof R) := by
      intro h
      obtain ⟨x, hxp, hxR⟩ := h
      exact hS ⟨x, hxp, hRS hxR⟩
    rw [terminalRoofSuffix, dif_neg hS, terminalRoofSuffix, dif_neg hR]

theorem terminalRoofSuffix_support_suffix (R : Set V)
    (p : DirectedPath.FinitePath G.graph) :
    (G.terminalRoofSuffix R p).walk.support <:+ p.walk.support := by
  classical
  by_cases hR : p.walk.Meets (G.roof R)
  · rw [terminalRoofSuffix, dif_pos hR]
    exact (p.walk.lastHit (G.roof R) hR).support_suffix
  · rw [terminalRoofSuffix, dif_neg hR]

/-- A terminal-roof suffix which still contains the old initial vertex did
not discard any part of the old finite path. -/
theorem terminalRoofSuffix_support_eq_of_start_mem (R : Set V)
    (p : DirectedPath.FinitePath G.graph)
    (hstart : p.start ∈ (G.terminalRoofSuffix R p).support) :
    (G.terminalRoofSuffix R p).support = p.support := by
  change p.start ∈ (G.terminalRoofSuffix R p).walk.support at hstart
  have heq : (G.terminalRoofSuffix R p).walk.support = p.walk.support := by
    apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := p.walk.support_ne_nil)
      (G.terminalRoofSuffix_support_suffix R p)
    · rw [p.walk.head_support]
      exact hstart
    · exact p.isPath
  ext v
  change v ∈ (G.terminalRoofSuffix R p).walk.support ↔ v ∈ p.walk.support
  rw [heq]

/-- Trimming first at a smaller roof and then at a larger roof has the same
support as trimming directly at the larger roof. -/
theorem terminalRoofSuffix_comp_support {R S : Set V}
    (hRS : G.roof R ⊆ G.roof S)
    (p : DirectedPath.FinitePath G.graph) :
    (G.terminalRoofSuffix S (G.terminalRoofSuffix R p)).support =
      (G.terminalRoofSuffix S p).support := by
  classical
  by_cases hS : p.walk.Meets (G.roof S)
  · by_cases hR : p.walk.Meets (G.roof R)
    · let r := p.lastHit (G.roof R) hR
      let L := p.walk.lastHit (G.roof S) hS
      have hLr : L.walk.support ⊆ r.walk.support := by
        intro v hv
        have hv' : v ∈ (G.terminalRoofSuffix S p).support := by
          rw [terminalRoofSuffix, dif_pos hS]
          exact hv
        have := G.terminalRoofSuffix_support_mono hRS p hv'
        rw [terminalRoofSuffix, dif_pos hR] at this
        exact this
      have hSr : r.walk.Meets (G.roof S) :=
        ⟨L.startpoint, hLr L.walk.start_mem_support, L.startpoint_mem⟩
      let N := r.walk.lastHit (G.roof S) hSr
      let M : p.walk.LastHit (G.roof S) := {
        startpoint := N.startpoint
        walk := N.walk
        startpoint_mem := N.startpoint_mem
        support_suffix := N.support_suffix.trans
          (p.walk.lastHit (G.roof R) hR).support_suffix
        no_mem_after := N.no_mem_after }
      have hEq : N.walk.support = L.walk.support :=
        (DirectedPath.FinitePath.lastHit_support_eq L M).symm
      have hRtrim : G.terminalRoofSuffix R p = r := by
        rw [terminalRoofSuffix, dif_pos hR]
      have hSrtrim : G.terminalRoofSuffix S r =
          r.lastHit (G.roof S) hSr := by
        rw [terminalRoofSuffix, dif_pos hSr]
      have hStrim : G.terminalRoofSuffix S p =
          p.lastHit (G.roof S) hS := by
        rw [terminalRoofSuffix, dif_pos hS]
      rw [hRtrim, hSrtrim, hStrim]
      ext v
      change v ∈ N.walk.support ↔ v ∈ L.walk.support
      rw [hEq]
    · have hRtrim : G.terminalRoofSuffix R p = p := by
        rw [terminalRoofSuffix, dif_neg hR]
      rw [hRtrim]
  · have hR : ¬p.walk.Meets (G.roof R) := by
      intro h
      obtain ⟨x, hxp, hxR⟩ := h
      exact hS ⟨x, hxp, hRS hxR⟩
    have hRtrim : G.terminalRoofSuffix R p = p := by
      rw [terminalRoofSuffix, dif_neg hR]
    rw [hRtrim]

/-- Terminal-roof trimming has the same support for two finite paths with
the same ordered vertex list when the two ambient roofs agree. -/
theorem terminalRoofSuffix_support_eq_of_walkSupport_eq
    {H : DWeb V} {R S : Set V}
    (hRoof : G.roof R = H.roof S)
    (p : DirectedPath.FinitePath G.graph)
    (q : DirectedPath.FinitePath H.graph)
    (hpq : p.walk.support = q.walk.support) :
    (G.terminalRoofSuffix R p).support =
      (H.terminalRoofSuffix S q).support := by
  classical
  by_cases hpMeet : p.walk.Meets (G.roof R)
  · have hqMeet : q.walk.Meets (H.roof S) := by
      obtain ⟨x, hxp, hxR⟩ := hpMeet
      exact ⟨x, by simpa only [← hpq] using hxp,
        by simpa only [← hRoof] using hxR⟩
    rw [terminalRoofSuffix, dif_pos hpMeet,
      terminalRoofSuffix, dif_pos hqMeet]
    have hlist := DirectedPath.FinitePath.lastHit_support_eq_of_support_eq
      hpq hRoof (p.walk.lastHit (G.roof R) hpMeet)
        (q.walk.lastHit (H.roof S) hqMeet)
    ext x
    change x ∈ (p.walk.lastHit (G.roof R) hpMeet).walk.support ↔
      x ∈ (q.walk.lastHit (H.roof S) hqMeet).walk.support
    rw [hlist]
  · have hqMeet : ¬ q.walk.Meets (H.roof S) := by
      intro hqMeet
      obtain ⟨x, hxq, hxS⟩ := hqMeet
      apply hpMeet
      exact ⟨x, by simpa only [hpq] using hxq,
        by simpa only [hRoof] using hxS⟩
    rw [terminalRoofSuffix, dif_neg hpMeet,
      terminalRoofSuffix, dif_neg hqMeet]
    ext x
    change x ∈ p.walk.support ↔ x ∈ q.walk.support
    rw [hpq]

/-- Every vertex actually used by a quotient wave lies in the quotient's
represented vertex region, including the possible length-zero initials. -/
theorem quotientWave_vertexSet_subset_quotientVertexSet
    (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    {W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W) :
    (G.quotient X).vertexSet W ⊆ G.quotientVertexSet X := by
  rintro v ⟨p, hpW, hvp⟩
  have hpSource : p.initial ∈ (G.quotient X).source :=
    hW.2.1 ⟨p, hpW, rfl⟩
  have hpInitial : p.initial ∉ G.strictRoof X := by
    rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hNoEnter] at hpSource
    exact hpSource.2
  rcases hp : p with f | r
  · rw [hp] at hvp hpInitial
    have hvp' : v ∈ f.walk.support := hvp
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        (G.quotient X).graph.Adj f.walk).1 hvp' with hv | hv
    · intro h
      apply hpInitial
      change f.start ∈ G.strictRoof X
      rw [← hv]
      exact h
    · exact (G.quotientWalk_tail_avoids f.walk hv).1
  · rw [hp] at hvp hpInitial
    obtain ⟨n, rfl⟩ := hvp
    cases n with
    | zero => exact hpInitial
    | succ n => exact (G.quotient_adj_endpoints (r.adj_succ n)).2.1

/-- A cast of a bundled wave has a preimage preserving both support and
terminal.  This strengthens `exists_preimage_castWebWave` only by retaining
the terminal equality that is definitionally present before the cast. -/
theorem exists_preimage_castWebWave_support_terminal
    {H K : DWeb V} (h : H = K) (W : H.Wave)
    {p : K.DPath} (hp : p ∈ (h ▸ W).1) :
    ∃ q ∈ W.1, p.support = q.support ∧
      K.terminal? p = H.terminal? q := by
  subst K
  exact ⟨p, hp, rfl, rfl⟩

@[simp] theorem support_castWebPath {H K : DWeb V} (h : H = K)
    (p : H.DPath) : (h ▸ p).support = p.support := by
  subst K
  rfl

@[simp] theorem terminal_castWebPath {H K : DWeb V} (h : H = K)
    (p : H.DPath) : K.terminal? (h ▸ p) = H.terminal? p := by
  subst K
  rfl

theorem mem_castWebWave {H K : DWeb V} (h : H = K) (W : H.Wave)
    {p : H.DPath} (hp : p ∈ W.1) : (h ▸ p) ∈ (h ▸ W).1 := by
  subst K
  exact hp

theorem castWebPath_inl {H K : DWeb V} (h : H = K)
    (p : DirectedPath.FinitePath H.graph) :
    h ▸ (Sum.inl p : H.DPath) =
      (Sum.inl (congrArg DWeb.graph h ▸ p) : K.DPath) := by
  subst K
  rfl

theorem walk_support_castFinitePath {D E : Digraph V} (h : D = E)
    (p : DirectedPath.FinitePath D) :
    (h ▸ p).walk.support = p.walk.support := by
  subst E
  rfl

/-- Quotienting by a subset of the commitment set does not change that
set's essential part. -/
theorem essential_quotient_eq_of_subset {X Y : Set V} (hXY : X ⊆ Y) :
    (G.quotient X).essential Y = G.essential Y := by
  rw [← (G.quotient X).sdiff_strictRoof_self Y,
    ← G.sdiff_strictRoof_self Y,
    G.strictRoof_quotient_eq_strictRoof_union,
    Set.union_eq_right.mpr hXY]

/-- Quotienting by a subset of a set does not change the roof of that set. -/
theorem roof_quotient_eq_of_subset {X Y : Set V} (hXY : X ⊆ Y) :
    (G.quotient X).roof Y = G.roof Y := by
  rw [show (G.quotient X).roof Y =
      (G.quotient X).strictRoof Y ∪ (G.quotient X).essential Y by
        exact RelationalRoof.roof_eq_strictRoof_union_essential
          (G.quotient X).graph.Adj (G.quotient X).target Y,
    show G.roof Y = G.strictRoof Y ∪ G.essential Y by
      exact RelationalRoof.roof_eq_strictRoof_union_essential
        G.graph.Adj G.target Y,
    G.strictRoof_quotient_eq_strictRoof_union,
    Set.union_eq_right.mpr hXY,
    G.essential_quotient_eq_of_subset hXY]

/-- A surviving finite old member has a concrete member in the transported
wave: its terminal-roof suffix, represented in the larger quotient. -/
theorem exists_mem_waveToLargerQuotient_of_old_finite
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave)
    (q : DirectedPath.FinitePath (G.quotient X).graph)
    (hqW : (Sum.inl q : (G.quotient X).DPath) ∈ W.1)
    (hqfin : q.finish ∉ (G.quotient X).strictRoof Y) :
    ∃ p ∈ (G.waveToLargerQuotient hNoEnter hXY W).1,
      p.support = ((G.quotient X).terminalRoofSuffix Y q).support ∧
      (G.quotient Y).terminal? p = some q.finish := by
  let H := G.quotient X
  let r : H.DPath := Sum.inl (H.terminalRoofSuffix Y q)
  have hrSuffix : r ∈ H.terminalSuffixFamily Y W.1 :=
    ⟨q, hqW, hqfin, rfl⟩
  let hadm := H.pathQuotientAdmissible_terminalSuffixFamily Y W.1 r hrSuffix
  let p₀ : (H.quotient Y).DPath := H.restrictPathToQuotient Y r hadm
  let Z : (H.quotient Y).Wave :=
    ⟨H.generalWaveQuotient Y W.1,
      H.isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have hp₀ : p₀ ∈ Z.1 := by
    exact Or.inl ⟨⟨r, hrSuffix⟩, rfl⟩
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  let p : (G.quotient Y).DPath := heq ▸ p₀
  have htransport :
      G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [htransport]
    exact DWeb.mem_castWebWave heq Z hp₀
  · rw [show p.support = p₀.support by
      exact DWeb.support_castWebPath heq p₀]
    rw [show p₀.support = r.support by
      exact H.support_restrictPathToQuotient Y r hadm]
    rfl
  · rw [show (G.quotient Y).terminal? p =
      (H.quotient Y).terminal? p₀ by
        exact DWeb.terminal_castWebPath heq p₀]
    rw [show (H.quotient Y).terminal? p₀ = H.terminal? r by
      exact H.terminal_restrictPathToQuotient Y r hadm]
    simp only [r, H.terminal?_finite, H.terminalRoofSuffix_finish]

/-- A surviving old finite member can be transported while retaining its
final-roof suffix exactly.  This is the across-quotient form of nested
terminal-roof trimming used by the dependent-stage ancestry induction. -/
theorem exists_mem_waveToLargerQuotient_of_old_finite_finalSuffix
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y Zset : Set V} (hXY : X ⊆ Y) (hYZ : Y ⊆ Zset)
    (W : (G.quotient X).Wave)
    (q : DirectedPath.FinitePath (G.quotient X).graph)
    (hqW : (Sum.inl q : (G.quotient X).DPath) ∈ W.1)
    (hqfin : q.finish ∉ (G.quotient X).strictRoof Y) :
    ∃ p : DirectedPath.FinitePath (G.quotient Y).graph,
      (Sum.inl p : (G.quotient Y).DPath) ∈
        (G.waveToLargerQuotient hNoEnter hXY W).1 ∧
      (G.quotient Y).terminal? (.inl p) = some q.finish ∧
      ((G.quotient Y).terminalRoofSuffix Zset p).support =
        ((G.quotient X).terminalRoofSuffix Zset q).support := by
  let H := G.quotient X
  let t := H.terminalRoofSuffix Y q
  have htSuffix : (Sum.inl t : H.DPath) ∈
      H.terminalSuffixFamily Y W.1 := ⟨q, hqW, hqfin, rfl⟩
  let hadm := H.pathQuotientAdmissible_terminalSuffixFamily Y W.1
    (Sum.inl t : H.DPath) htSuffix
  let p₀ : DirectedPath.FinitePath (H.quotient Y).graph :=
    H.restrictFinitePathToQuotient Y t hadm.1 hadm.2
  let Zq : (H.quotient Y).Wave :=
    ⟨H.generalWaveQuotient Y W.1,
      H.isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have hp₀ : (Sum.inl p₀ : (H.quotient Y).DPath) ∈ Zq.1 := by
    exact Or.inl ⟨⟨(Sum.inl t : H.DPath), htSuffix⟩, rfl⟩
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  let hgraph : (H.quotient Y).graph = (G.quotient Y).graph :=
    congrArg DWeb.graph heq
  let p : DirectedPath.FinitePath (G.quotient Y).graph := hgraph ▸ p₀
  have hpCast : heq ▸ (Sum.inl p₀ : (H.quotient Y).DPath) =
      (Sum.inl p : (G.quotient Y).DPath) := by
    exact DWeb.castWebPath_inl heq p₀
  have htransport :
      G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Zq := by
    apply Subtype.ext
    rfl
  have hpTransport : (Sum.inl p : (G.quotient Y).DPath) ∈
      (G.waveToLargerQuotient hNoEnter hXY W).1 := by
    rw [htransport, ← hpCast]
    exact DWeb.mem_castWebWave heq Zq hp₀
  have hpWalk : p.walk.support = t.walk.support := by
    have hp₀Walk : p₀.walk.support = t.walk.support := by
      exact H.support_restrictWalkToQuotient Y t.walk hadm.1 hadm.2
    exact (DWeb.walk_support_castFinitePath hgraph p₀).trans hp₀Walk
  have hRoof : H.roof Zset = (G.quotient Y).roof Zset := by
    calc
      H.roof Zset = G.roof Zset :=
        G.roof_quotient_eq_of_subset (hXY.trans hYZ)
      _ = (G.quotient Y).roof Zset :=
        (G.roof_quotient_eq_of_subset hYZ).symm
  have hCross : (H.terminalRoofSuffix Zset t).support =
      ((G.quotient Y).terminalRoofSuffix Zset p).support :=
    H.terminalRoofSuffix_support_eq_of_walkSupport_eq hRoof t p hpWalk.symm
  refine ⟨p, hpTransport, ?_, ?_⟩
  · calc
      (G.quotient Y).terminal? (.inl p) =
          (G.quotient Y).terminal?
            (heq ▸ (Sum.inl p₀ : (H.quotient Y).DPath)) := by
              rw [hpCast]
      _ = (H.quotient Y).terminal? (.inl p₀) :=
        DWeb.terminal_castWebPath heq _
      _ = some q.finish := by
        simp only [DWeb.terminal?_finite, Option.some.injEq]
        change t.finish = q.finish
        exact H.terminalRoofSuffix_finish Y q
  · calc
      ((G.quotient Y).terminalRoofSuffix Zset p).support =
          (H.terminalRoofSuffix Zset t).support := hCross.symm
      _ = (H.terminalRoofSuffix Zset q).support :=
        H.terminalRoofSuffix_comp_support (H.roof_mono hYZ) q

/-- Same-path provenance for a nontrivial transported path, retaining the
finite old member, its survival condition, and its terminal. -/
theorem exists_old_finite_path_of_mem_waveToLargerQuotient_of_not_mem
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave)
    {p : (G.quotient Y).DPath}
    (hp : p ∈ (G.waveToLargerQuotient hNoEnter hXY W).1)
    {z : V} (hzp : z ∈ p.support) (hzY : z ∉ Y) :
    ∃ q : DirectedPath.FinitePath (G.quotient X).graph,
      (Sum.inl q : (G.quotient X).DPath) ∈ W.1 ∧
      q.finish ∉ (G.quotient X).strictRoof Y ∧
      p.support =
        ((G.quotient X).terminalRoofSuffix Y q).support ∧
      (G.quotient Y).terminal? p = some q.finish := by
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
  obtain ⟨p₀, hp₀, hsupp, hterminal⟩ :=
    DWeb.exists_preimage_castWebWave_support_terminal heq Z hp
  have hzp₀ : z ∈ p₀.support := hsupp ▸ hzp
  change p₀ ∈ H.generalWaveQuotient Y W.1 at hp₀
  unfold generalWaveQuotient admissibleWarpQuotient at hp₀
  rcases hp₀ with hp₀ | hp₀
  · obtain ⟨r, hr⟩ := hp₀
    have hp₀eq : p₀ = H.restrictPathToQuotient Y r.1
        (H.pathQuotientAdmissible_terminalSuffixFamily Y W.1
          r.1 r.2) := hr
    obtain ⟨q, hqW, hqfin, hrq⟩ := r.2
    refine ⟨q, hqW, hqfin, ?_, ?_⟩
    · calc
        p.support = p₀.support := hsupp
        _ = r.1.support := by
          rw [hp₀eq, H.support_restrictPathToQuotient]
        _ = (H.terminalRoofSuffix Y q).support := by
          rw [hrq]
          rfl
    · rw [hterminal, hp₀eq, H.terminal_restrictPathToQuotient]
      rw [hrq]
      simp only [H.terminal?_finite, H.terminalRoofSuffix_finish]
  · obtain ⟨e, he, hp₀eq⟩ := hp₀
    subst p₀
    have hze : z = e := by simpa using hzp₀
    exact (hzY (hze ▸ he.1.1)).elim

/-- Every strict-roof point of a dependent stage remains in the ambient
strict roof of the final common wave.  This is the stage-independent core
of the strict-roof argument used below for grounding vertices. -/
theorem sectionSixAccumStage_strictRoof_subset_commonWave
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ) :
    G.strictRoof ((G.quotient
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalFrontier
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1) ⊆
      G.strictRoof ((G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).terminalFrontier
          (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1) := by
  let Xn := (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier
  let X := G.sectionSixAccumClosure hNoEnter F K Y Q T y
  let A := (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave
  let C := G.sectionSixAccumCommonStage hNoEnter F K Y Q T y n
  let M := G.sectionSixAccumCommonWave hNoEnter F K Y Q T y
  have hXnX : Xn ⊆ X :=
    G.sectionSixAccumStage_carrier_subset_closure hNoEnter F K Y Q T y n
  have hStageCommon :
      G.roof ((G.quotient Xn).terminalFrontier A.1) ⊆
        G.roof ((G.quotient X).terminalFrontier C.1) := by
    exact G.roof_terminalFrontier_subset_waveToLargerQuotient
      hNoEnter hXnX A
  have hCommonFinalQ :
      (G.quotient X).RoofLE C.1 M.1 := by
    exact G.sectionSixAccumCommonStage_roofLE
      hNoEnter F K Y Q T y n
  have hCommonFinal :
      G.roof ((G.quotient X).terminalFrontier C.1) ⊆
        G.roof ((G.quotient X).terminalFrontier M.1) := by
    exact G.original_roofLE_of_quotient_roofLE
      hNoEnter M.2 hCommonFinalQ
  exact G.strictRoof_mono_of_roof_mono
    (hStageCommon.trans hCommonFinal)

/-- A finite essential member of the final omega-arrow has stabilized at
every sufficiently late accumulated-arrow stage.  This support form is the
one used by the Section 6 closing recurrence. -/
theorem exists_later_omegaArrowStage_path_supporting_essential
    (W : ℕ → G.Wave) (k : ℕ) {q : G.DPath}
    (hq : q ∈ G.essentialWarpPart (G.omegaArrow W).1) :
    ∃ m, k ≤ m ∧ ∃ p ∈ (G.omegaArrowStage W m).1,
      q.support ⊆ p.support := by
  obtain ⟨hqFinal, t, hqt, _htEssential⟩ := hq
  rcases hqPath : q with qf | qr
  · have hqFinish : qf.finish = t := by
      simpa only [hqPath, DWeb.terminal?_finite, Option.some.injEq] using hqt
    have htFinal : t ∈ G.terminalFrontier (G.omegaArrow W).1 :=
      ⟨q, hqFinal, hqt⟩
    obtain ⟨n, p, hpStage, hpt⟩ := Set.mem_iUnion.mp
      (SafeLinkGround.DWeb.terminalFrontier_omegaArrow_subset_iUnion_stages
        G W htFinal)
    let c := Set.range (G.omegaArrowStage W)
    let hcne := G.omegaArrowStage_range_nonempty W
    let hc := G.omegaArrowStage_range_isChain W
    have hnFinal : G.ForwardExtension (G.omegaArrowStage W n).1
        (G.omegaArrow W).1 := by
      exact G.le_waveChainUpperWave c hcne hc (Set.mem_range_self n)
    obtain ⟨r, hrFinal, hpr⟩ := hnFinal.1 p hpStage
    have htr : t ∈ r.support :=
      G.support_mono_of_extends hpr (G.terminal_mem_support hpt)
    have htq : t ∈ q.support := G.terminal_mem_support hqt
    have hrq : r = q := by
      by_contra hne
      exact Set.disjoint_left.1
        ((G.omegaArrow W).2.1 hrFinal hqFinal hne) htr htq
    subst r
    let m := max n k
    have hnm : n ≤ m := Nat.le_max_left n k
    have hkm : k ≤ m := Nat.le_max_right n k
    obtain ⟨s, hsStage, hps⟩ :=
      (G.omegaArrowStage_mono W hnm).1 p hpStage
    have hmFinal : G.ForwardExtension (G.omegaArrowStage W m).1
        (G.omegaArrow W).1 := by
      exact G.le_waveChainUpperWave c hcne hc (Set.mem_range_self m)
    obtain ⟨u, huFinal, hsu⟩ := hmFinal.1 s hsStage
    have hts : t ∈ s.support :=
      G.support_mono_of_extends hps (G.terminal_mem_support hpt)
    have htu : t ∈ u.support := G.support_mono_of_extends hsu hts
    have huq : u = q := by
      by_contra hne
      exact Set.disjoint_left.1
        ((G.omegaArrow W).2.1 huFinal hqFinal hne) htu htq
    subst u
    rcases hsPath : s with sf | sr
    · have hsq : DirectedPath.Path.Extends (.inl sf) (.inl qf) := by
        simpa only [hsPath, hqPath] using hsu
      have htSf : qf.finish ∈ sf.support := by
        rw [hqFinish]
        rw [hsPath] at hts
        exact hts
      have hsupp :=
        SafeLinkGround.DirectedPath.FinitePath.support_eq_of_isPrefixOf_of_finish_mem
          hsq htSf
      refine ⟨m, hkm, s, hsStage, ?_⟩
      rw [hsPath]
      intro v hv
      change v ∈ sf.walk.support
      change v ∈ qf.walk.support at hv
      rwa [hsupp]
    · have : False := by
        simpa only [hsPath, hqPath,
          DirectedPath.Path.not_extends_ray_finite] using hsu
      exact this.elim
  · rw [hqPath] at hqt
    simp at hqt

/-- Support-exact form of finite-stage stabilization.  An essential member
of the countable up-arrow is not merely supported by a sufficiently late
finite arrow stage: the supporting stage member has exactly the same
support.  Indeed, extend that stage member to the final arrow.  It meets the
given essential member at the latter's terminal, so the final warp forces
the two extensions to be equal. -/
theorem exists_later_omegaArrowStage_path_same_support_of_essential
    (W : ℕ → G.Wave) (k : ℕ) {q : G.DPath}
    (hq : q ∈ G.essentialWarpPart (G.omegaArrow W).1) :
    ∃ m, k ≤ m ∧ ∃ p ∈ (G.omegaArrowStage W m).1,
      p.support = q.support := by
  have hqEssential := hq
  obtain ⟨hqFinal, t, hqt, _htEssential⟩ := hq
  obtain ⟨m, hkm, p, hpStage, hqp⟩ :=
    G.exists_later_omegaArrowStage_path_supporting_essential W k hqEssential
  let c := Set.range (G.omegaArrowStage W)
  let hcne := G.omegaArrowStage_range_nonempty W
  let hc := G.omegaArrowStage_range_isChain W
  have hmFinal : G.ForwardExtension (G.omegaArrowStage W m).1
      (G.omegaArrow W).1 := by
    exact G.le_waveChainUpperWave c hcne hc (Set.mem_range_self m)
  obtain ⟨u, huFinal, hpu⟩ := hmFinal.1 p hpStage
  have htq : t ∈ q.support := G.terminal_mem_support hqt
  have htu : t ∈ u.support :=
    G.support_mono_of_extends hpu (hqp htq)
  have huq : u = q := by
    by_contra hne
    exact Set.disjoint_left.1
      ((G.omegaArrow W).2.1 huFinal hqFinal hne) htu htq
  subst u
  exact ⟨m, hkm, p, hpStage,
    Set.Subset.antisymm (G.support_mono_of_extends hpu) hqp⟩

/-- An essential terminal for a later roof cannot be passed by a forward
extension.  Consequently the extending member has exactly the same finite
support. -/
theorem exists_forwardExtension_path_same_support_of_essential
    {U W : Set G.DPath} (hW : G.IsWave W)
    (hUW : G.ForwardExtension U W) {S : Set V}
    (hRoof : G.roof (G.terminalFrontier W) ⊆ G.roof S)
    (f : DirectedPath.FinitePath G.graph)
    (hfU : (Sum.inl f : G.DPath) ∈ U)
    (hEss : f.finish ∈ G.essential S) :
    ∃ q ∈ W, G.Extends (Sum.inl f) q ∧ q.support = f.support ∧
      G.terminal? q = some f.finish := by
  obtain ⟨q, hqW, hfq⟩ := hUW.1 (Sum.inl f) hfU
  have hfinishQ : f.finish ∈ q.support :=
    G.support_mono_of_extends hfq f.finish_mem_support
  have hfinishRoof : f.finish ∈ G.roof (G.terminalFrontier W) :=
    (DWeb.IsWave.self_roofing (Γ := G) hW) ⟨q, hqW, hfinishQ⟩
  have hfinishTerminal : f.finish ∈ G.terminalFrontier W := by
    by_contra hnot
    have hStrict : f.finish ∈ G.strictRoof (G.terminalFrontier W) :=
      ⟨hfinishRoof, fun h ↦ hnot (G.essential_subset _ h)⟩
    have hStrictS := G.strictRoof_mono_of_roof_mono hRoof hStrict
    exact Set.disjoint_left.1 (G.disjoint_strictRoof_essential S)
      hStrictS hEss
  have hqTerminal : G.terminal? q = some f.finish :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      G hW.1 hqW hfinishQ hfinishTerminal
  rcases hqPath : q with qf | qr
  · have hqFinish : qf.finish = f.finish := by
      simpa only [hqPath, G.terminal?_finite, Option.some.injEq] using hqTerminal
    have hprefix : f.IsPrefixOf qf := by
      change DirectedPath.Path.Extends (.inl f) q at hfq
      rw [hqPath] at hfq
      exact hfq
    have hsupp :=
      SafeLinkGround.DirectedPath.FinitePath.support_eq_of_isPrefixOf_of_finish_mem
        hprefix (hqFinish ▸ f.finish_mem_support)
    refine ⟨q, hqW, hfq, ?_, hqTerminal⟩
    rw [hqPath]
    ext v
    change v ∈ qf.walk.support ↔ v ∈ f.walk.support
    rw [hsupp]
  · rw [hqPath] at hqTerminal
    simp at hqTerminal

/-- Ambient version of the preceding lemma for a quotient wave.  Quotient
self-roofing supplies ambient roof membership, while the explicit strict
roof comparison rules out passing the specified essential terminal. -/
theorem exists_quotient_forwardExtension_path_same_support_of_essential
    (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    {U W : Set (G.quotient X).DPath} (hW : (G.quotient X).IsWave W)
    (hUW : (G.quotient X).ForwardExtension U W) {S : Set V}
    (hStrict : G.strictRoof ((G.quotient X).terminalFrontier W) ⊆
      G.strictRoof S)
    (f : DirectedPath.FinitePath (G.quotient X).graph)
    (hfU : (Sum.inl f : (G.quotient X).DPath) ∈ U)
    (hEss : f.finish ∈ G.essential S) :
    ∃ q ∈ W, (G.quotient X).Extends (Sum.inl f) q ∧
      q.support = f.support ∧
      (G.quotient X).terminal? q = some f.finish := by
  let H := G.quotient X
  obtain ⟨q, hqW, hfq⟩ := hUW.1 (Sum.inl f) hfU
  have hfinishQ : f.finish ∈ q.support :=
    H.support_mono_of_extends hfq f.finish_mem_support
  have hfinishRoofQ : f.finish ∈ H.roof (H.terminalFrontier W) :=
    (DWeb.IsWave.self_roofing (Γ := H) hW) ⟨q, hqW, hfinishQ⟩
  have hfinishRoof : f.finish ∈ G.roof (H.terminalFrontier W) :=
    G.quotientWave_roof_subset_original_roof_general
      hNoEnter hW hfinishRoofQ
  have hfinishTerminal : f.finish ∈ H.terminalFrontier W := by
    by_contra hnot
    have hOldStrict : f.finish ∈
        G.strictRoof (H.terminalFrontier W) :=
      ⟨hfinishRoof, fun h ↦ hnot (G.essential_subset _ h)⟩
    exact Set.disjoint_left.1 (G.disjoint_strictRoof_essential S)
      (hStrict hOldStrict) hEss
  have hqTerminal : H.terminal? q = some f.finish :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      H hW.1 hqW hfinishQ hfinishTerminal
  rcases hqPath : q with qf | qr
  · have hqFinish : qf.finish = f.finish := by
      simpa only [hqPath, H.terminal?_finite, Option.some.injEq] using hqTerminal
    have hprefix : f.IsPrefixOf qf := by
      change DirectedPath.Path.Extends (.inl f) q at hfq
      rw [hqPath] at hfq
      exact hfq
    have hsupp :=
      SafeLinkGround.DirectedPath.FinitePath.support_eq_of_isPrefixOf_of_finish_mem
        hprefix (hqFinish ▸ f.finish_mem_support)
    refine ⟨q, hqW, hfq, ?_, hqTerminal⟩
    rw [hqPath]
    ext v
    change v ∈ qf.walk.support ↔ v ∈ f.walk.support
    rw [hsupp]
  · rw [hqPath] at hqTerminal
    simp at hqTerminal

/-- Ambient version of finite-thread stabilization for waves in a quotient.
If the endpoint is essential for a later ambient separator, a forward
extension cannot continue past it: doing so would make the endpoint strict
for the later ambient roof. -/
theorem exists_forwardExtension_path_same_support_of_ambient_essential
    (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    {U W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W)
    (hUW : (G.quotient X).ForwardExtension U W) {S : Set V}
    (hRoof : G.roof ((G.quotient X).terminalFrontier W) ⊆ G.roof S)
    (f : DirectedPath.FinitePath (G.quotient X).graph)
    (hfU : (Sum.inl f : (G.quotient X).DPath) ∈ U)
    (hEss : f.finish ∈ G.essential S) :
    ∃ q ∈ W, (G.quotient X).Extends (Sum.inl f) q ∧
      q.support = f.support ∧
      (G.quotient X).terminal? q = some f.finish := by
  let H := G.quotient X
  obtain ⟨q, hqW, hfq⟩ := hUW.1 (Sum.inl f) hfU
  have hfinishQ : f.finish ∈ q.support :=
    H.support_mono_of_extends hfq f.finish_mem_support
  have hfinishRoofH :
      f.finish ∈ H.roof (H.terminalFrontier W) :=
    (DWeb.IsWave.self_roofing (Γ := H) hW) ⟨q, hqW, hfinishQ⟩
  have hfinishRoof :
      f.finish ∈ G.roof (H.terminalFrontier W) :=
    G.quotientWave_roof_subset_original_roof_general
      hNoEnter hW hfinishRoofH
  have hfinishTerminal : f.finish ∈ H.terminalFrontier W := by
    by_contra hnot
    have hStrict : f.finish ∈ G.strictRoof (H.terminalFrontier W) :=
      ⟨hfinishRoof, fun h ↦ hnot (G.essential_subset _ h)⟩
    have hStrictS := G.strictRoof_mono_of_roof_mono hRoof hStrict
    exact Set.disjoint_left.1 (G.disjoint_strictRoof_essential S)
      hStrictS hEss
  have hqTerminal : H.terminal? q = some f.finish :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      H hW.1 hqW hfinishQ hfinishTerminal
  rcases hqPath : q with qf | qr
  · have hqFinish : qf.finish = f.finish := by
      simpa only [hqPath, H.terminal?_finite, Option.some.injEq] using hqTerminal
    have hprefix : f.IsPrefixOf qf := by
      change DirectedPath.Path.Extends (.inl f) q at hfq
      rw [hqPath] at hfq
      exact hfq
    have hsupp :=
      SafeLinkGround.DirectedPath.FinitePath.support_eq_of_isPrefixOf_of_finish_mem
        hprefix (hqFinish ▸ f.finish_mem_support)
    refine ⟨q, hqW, hfq, ?_, hqTerminal⟩
    rw [hqPath]
    ext v
    change v ∈ qf.walk.support ↔ v ∈ f.walk.support
    rw [hsupp]
  · rw [hqPath] at hqTerminal
    simp at hqTerminal

/-- Exact forward-extension absorption when the protected endpoint is
essential only in a later quotient.  Ambient strict-roof propagation is
enough: a surviving ambient strict point descends to a strict point in the
later quotient, contradicting essentiality there. -/
theorem exists_quotient_forwardExtension_path_same_support_of_later_essential
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    {U W : Set (G.quotient X).DPath} (hW : (G.quotient X).IsWave W)
    (hUW : (G.quotient X).ForwardExtension U W)
    (M : (G.quotient Y).Wave)
    (hStrict : G.strictRoof ((G.quotient X).terminalFrontier W) ⊆
      G.strictRoof ((G.quotient Y).terminalFrontier M.1))
    (f : DirectedPath.FinitePath (G.quotient X).graph)
    (hfU : (Sum.inl f : (G.quotient X).DPath) ∈ U)
    (hEss : f.finish ∈ (G.quotient Y).essential
      ((G.quotient Y).terminalFrontier M.1)) :
    ∃ q ∈ W, (G.quotient X).Extends (Sum.inl f) q ∧
      q.support = f.support ∧
      (G.quotient X).terminal? q = some f.finish := by
  let H := G.quotient X
  let S := (G.quotient Y).terminalFrontier M.1
  obtain ⟨q, hqW, hfq⟩ := hUW.1 (Sum.inl f) hfU
  have hfinishQ : f.finish ∈ q.support :=
    H.support_mono_of_extends hfq f.finish_mem_support
  have hfinishRoofH : f.finish ∈ H.roof (H.terminalFrontier W) :=
    (DWeb.IsWave.self_roofing (Γ := H) hW) ⟨q, hqW, hfinishQ⟩
  have hfinishRoof : f.finish ∈ G.roof (H.terminalFrontier W) :=
    G.quotientWave_roof_subset_original_roof_general
      hNoEnter hW hfinishRoofH
  have hfrontierSurvives : Disjoint S (G.strictRoof Y) := by
    apply Set.disjoint_left.2
    intro z hzS hzStrict
    obtain ⟨p, hpM, hpt⟩ := hzS
    have hzVertex : z ∈ (G.quotient Y).vertexSet M.1 :=
      ⟨p, hpM, (G.quotient Y).terminal_mem_support hpt⟩
    exact G.quotientWave_vertexSet_subset_quotientVertexSet
      hNoEnter M.2 hzVertex hzStrict
  have hSeq : S \ G.strictRoof Y = S :=
    sdiff_eq_left.mpr hfrontierSurvives
  have hfinishTerminal : f.finish ∈ H.terminalFrontier W := by
    by_contra hnot
    have hOldStrict : f.finish ∈ G.strictRoof (H.terminalFrontier W) :=
      ⟨hfinishRoof, fun h ↦ hnot (G.essential_subset _ h)⟩
    have hFinalStrictAmbient : f.finish ∈ G.strictRoof S := hStrict hOldStrict
    have hfinishSurvives : f.finish ∉ G.strictRoof Y := by
      exact Set.disjoint_left.1 hfrontierSurvives
        ((G.quotient Y).essential_subset S hEss)
    have hFinalStrict : f.finish ∈ (G.quotient Y).strictRoof S := by
      rw [← hSeq]
      exact G.strictRoof_inter_quotientVertexSet_subset_strictRoof_quotient
        S Y ⟨hFinalStrictAmbient, hfinishSurvives⟩
    exact Set.disjoint_left.1
      ((G.quotient Y).disjoint_strictRoof_essential S)
      hFinalStrict hEss
  have hqTerminal : H.terminal? q = some f.finish :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      H hW.1 hqW hfinishQ hfinishTerminal
  rcases hqPath : q with qf | qr
  · have hqFinish : qf.finish = f.finish := by
      simpa only [hqPath, H.terminal?_finite, Option.some.injEq] using hqTerminal
    have hprefix : f.IsPrefixOf qf := by
      change DirectedPath.Path.Extends (.inl f) q at hfq
      rw [hqPath] at hfq
      exact hfq
    have hsupp :=
      SafeLinkGround.DirectedPath.FinitePath.support_eq_of_isPrefixOf_of_finish_mem
        hprefix (hqFinish ▸ f.finish_mem_support)
    refine ⟨q, hqW, hfq, ?_, hqTerminal⟩
    rw [hqPath]
    ext v
    change v ∈ qf.walk.support ↔ v ∈ f.walk.support
    rw [hsupp]
  · rw [hqPath] at hqTerminal
    simp at hqTerminal

/-- Essentiality descends to an intermediate subset containing the point.
The same target path which avoids the larger set with the point removed
also avoids the smaller one. -/
theorem mem_essential_of_mem_of_subset_of_mem_essential
    {C D : Set V} {x : V} (hxC : x ∈ C) (hCD : C ⊆ D)
    (hxD : x ∈ G.essential D) : x ∈ G.essential C := by
  refine ⟨hxC, ?_⟩
  intro hxRoof
  apply hxD.2
  apply G.roof_mono ?_ hxRoof
  intro z hz
  exact ⟨hCD hz.1, hz.2⟩

/-- The general wave quotient starts a path at every essential commitment
vertex, whether that vertex is retained by a terminal suffix or inserted as
an isolated path. -/
theorem essential_subset_initialSet_generalWaveQuotient
    (X : Set V) (U : Set G.DPath) :
    G.essential X ⊆
      (G.quotient X).initialSet (G.generalWaveQuotient X U) := by
  rw [generalWaveQuotient,
    G.initialSet_admissibleWarpQuotient_source_formula]
  intro x hx
  exact ⟨Or.inr (G.essential_subset X hx), fun hxStrict ↦
    Set.disjoint_left.1 (G.disjoint_strictRoof_essential X) hxStrict hx⟩

@[simp] theorem initial_castWebPath_eq {H K : DWeb V} (h : H = K)
    (p : H.DPath) : (h ▸ p).initial = p.initial := by
  subst K
  rfl

/-- Transport to a larger quotient starts a path at every essential vertex
of the larger commitment set. -/
theorem essential_subset_initialSet_waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    G.essential Y ⊆
      (G.quotient Y).initialSet
        (G.waveToLargerQuotient hNoEnter hXY W).1 := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    ⟨H.generalWaveQuotient Y W.1,
      H.isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  let heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport :
      G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  intro x hx
  have hxH : x ∈ H.essential Y := by
    rw [G.essential_quotient_eq_of_subset hXY]
    exact hx
  obtain ⟨p, hpZ, hpInitial⟩ :=
    H.essential_subset_initialSet_generalWaveQuotient Y W.1 hxH
  rw [htransport]
  refine ⟨heq ▸ p, DWeb.mem_castWebWave heq Z hpZ, ?_⟩
  simpa only [DWeb.initial_castWebPath_eq] using hpInitial

/-- If the old prefix and an arrow candidate both descend from members of
one warp, and the old member has exactly the prefix support, then the
candidate cannot add a new vertex.  The two descendants meet at the arrow
contact, so warp disjointness identifies them. -/
theorem support_appendAt_eq_of_candidate_descends_to_same_warp
    {K H : DWeb V} {A : Set K.DPath} (hA : K.IsWarp A)
    {U W : Set H.DPath} (f : DirectedPath.FinitePath H.graph)
    (hfU : (Sum.inl f : H.DPath) ∈ U)
    (c : H.ArrowCandidate U W f)
    {q r : K.DPath} (hqA : q ∈ A) (hrA : r ∈ A)
    (hqSupport : q.support = f.support)
    (hcSupport : c.path.support ⊆ r.support) :
    (DirectedPath.Path.appendAt f c.path c.finish_mem
      (c.appendable hfU)).support = f.support := by
  have hfinishQ : f.finish ∈ q.support :=
    hqSupport.symm ▸ f.finish_mem_support
  have hfinishR : f.finish ∈ r.support := hcSupport c.finish_mem
  have hqr : q = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hA hqA hrA hne) hfinishQ hfinishR
  rw [DirectedPath.Path.support_appendAt]
  apply Set.Subset.antisymm
  · rintro x (hxf | hxc)
    · exact hxf
    · have hxpath : x ∈ c.path.support :=
        c.path.support_suffixFrom_subset f.finish c.finish_mem hxc
      have hxr : x ∈ r.support := hcSupport hxpath
      rw [← hqr, hqSupport] at hxr
      exact hxr
  · exact Set.subset_union_left

/-- Final-suffix form of the arrow-candidate merge.  It is enough that the
two members of the dependent warp have the prescribed supports after
trimming by the final commitment roof. -/
theorem support_appendAt_eq_of_candidate_finalSuffix_same_warp
    {K H : DWeb V} {A : Set K.DPath} (hA : K.IsWarp A)
    {U W : Set H.DPath} (f : DirectedPath.FinitePath H.graph)
    (hfU : (Sum.inl f : H.DPath) ∈ U)
    (c : H.ArrowCandidate U W f) (S : Set V)
    (q r : DirectedPath.FinitePath K.graph)
    (hqA : (Sum.inl q : K.DPath) ∈ A)
    (hrA : (Sum.inl r : K.DPath) ∈ A)
    (hqSuffix : (K.terminalRoofSuffix S q).support = f.support)
    (hcSuffix : c.path.support =
      (K.terminalRoofSuffix S r).support) :
    (DirectedPath.Path.appendAt f c.path c.finish_mem
      (c.appendable hfU)).support = f.support := by
  have hfinishQSuffix : f.finish ∈
      (K.terminalRoofSuffix S q).support :=
    hqSuffix.symm ▸ f.finish_mem_support
  have hfinishQ : f.finish ∈ q.support :=
    K.terminalRoofSuffix_support_subset S q hfinishQSuffix
  have hfinishRSuffix : f.finish ∈
      (K.terminalRoofSuffix S r).support := hcSuffix ▸ c.finish_mem
  have hfinishR : f.finish ∈ r.support :=
    K.terminalRoofSuffix_support_subset S r hfinishRSuffix
  have hqr : q = r := by
    by_contra hne
    exact Set.disjoint_left.1
      (hA hqA hrA (fun h ↦ hne (Sum.inl.inj h))) hfinishQ hfinishR
  rw [DirectedPath.Path.support_appendAt]
  apply Set.Subset.antisymm
  · rintro x (hxf | hxc)
    · exact hxf
    · have hxpath : x ∈ c.path.support :=
        c.path.support_suffixFrom_subset f.finish c.finish_mem hxc
      have hxrSuffix : x ∈ (K.terminalRoofSuffix S r).support :=
        hcSuffix ▸ hxpath
      rw [← hqr, hqSuffix] at hxrSuffix
      exact hxrSuffix
  · exact Set.subset_union_left

/-- Inclusion form of the candidate merge.  The left dependent-stage
representative is allowed to extend the old finite prefix, as happens after
transport followed by a forward extension.  Sharing the arrow contact with
the right representative still identifies the two warp members, so the
entire appended arrow path lies in that one member. -/
theorem support_appendAt_subset_of_candidate_same_warp
    {K H : DWeb V} {A : Set K.DPath} (hA : K.IsWarp A)
    {U W : Set H.DPath} (f : DirectedPath.FinitePath H.graph)
    (hfU : (Sum.inl f : H.DPath) ∈ U)
    (c : H.ArrowCandidate U W f)
    (q r : K.DPath) (hqA : q ∈ A) (hrA : r ∈ A)
    (hfq : f.support ⊆ q.support)
    (hcr : (c.path.suffixFrom f.finish c.finish_mem).support ⊆ r.support) :
    (DirectedPath.Path.appendAt f c.path c.finish_mem
      (c.appendable hfU)).support ⊆ q.support := by
  have hfinishQ : f.finish ∈ q.support := hfq f.finish_mem_support
  have hfinishSuffix : f.finish ∈
      (c.path.suffixFrom f.finish c.finish_mem).support := by
    have hsingleton : f.finish ∈ ({f.finish} : Set V) :=
      Set.mem_singleton f.finish
    rw [← c.clean] at hsingleton
    exact hsingleton.1
  have hfinishR : f.finish ∈ r.support := hcr hfinishSuffix
  have hqr : q = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hA hqA hrA hne) hfinishQ hfinishR
  rw [DirectedPath.Path.support_appendAt]
  rintro x (hxf | hxc)
  · exact hfq hxf
  · rw [hqr]
    exact hcr hxc

/-- If the chosen arrow leaves a finite member unchanged, then every clean
candidate for that member contributes no new vertex after the contact.

The arrow constructor chooses an arbitrary candidate when candidates exist.
Warp disjointness makes all candidates use the same path, so this conclusion
is independent of that choice.  Keeping this elementary consequence packaged
avoids unfolding the choice inside finite-arrow ancestry arguments. -/
theorem ArrowCandidate.suffix_support_subset_of_arrowPath_eq
    {U W : Set G.DPath} (hW : G.IsWarp W)
    (f : DirectedPath.FinitePath G.graph)
    (hf : (Sum.inl f : G.DPath) ∈ U)
    (c : G.ArrowCandidate U W f)
    (heq : G.arrowPath U W ⟨Sum.inl f, hf⟩ = Sum.inl f) :
    (c.path.suffixFrom f.finish c.finish_mem).support ⊆ f.support := by
  classical
  change G.arrowFinite U W f hf = Sum.inl f at heq
  rw [arrowFinite, dif_pos ⟨c⟩] at heq
  let d := Classical.choice
    (show Nonempty (G.ArrowCandidate U W f) from ⟨c⟩)
  change DirectedPath.Path.appendAt f d.path d.finish_mem
      (d.appendable hf) = Sum.inl f at heq
  have hdc : d.path = c.path :=
    ArrowCandidate.path_eq (G := G) hW d c
  obtain ⟨cpath, cmem, cfinish, cclean⟩ := c
  obtain ⟨dpath, dmem, dfinish, dclean⟩ := d
  dsimp only at hdc ⊢
  subst dpath
  have hsuffix :
      (cpath.suffixFrom f.finish dfinish).support =
        (cpath.suffixFrom f.finish cfinish).support := by
    rfl
  have hsupp := congrArg DirectedPath.Path.support heq
  rw [DirectedPath.Path.support_appendAt, hsuffix] at hsupp
  intro x hxc
  have hxUnion : x ∈ f.support ∪
      (cpath.suffixFrom f.finish cfinish).support := Or.inr hxc
  rw [hsupp] at hxUnion
  exact hxUnion

/-- In a web with no edge entering its source, a source vertex occurring on
any directed path is its initial vertex.  This is the exact normalization
fact needed below for the common quotient; unlike the global normalization
predicate it does not mention the target side. -/
theorem NoEdgeEnters.eq_initial_of_mem_path {A : Set V}
    (hA : G.NoEdgeEnters A) (p : G.DPath) {x : V}
    (hxp : x ∈ p.support) (hxA : x ∈ A) : x = p.initial := by
  rcases p with f | r
  · rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        G.graph.Adj f.walk).1 hxp with hx | hxtail
    · exact hx
    · exact (G.walk_tail_avoids_of_noEdgeEnters hA f.walk hxtail hxA).elim
  · rcases hxp with ⟨n, rfl⟩
    cases n with
    | zero => rfl
    | succ n => exact (hA (r.adj_succ n) hxA).elim

/-- A path in a quotient wave which meets the quotienting set meets it at
its initial vertex.  The point is first known to survive the quotient from
wave membership; the quotient-source formula then makes it a source, and
no-edge-entry forces it to be the initial vertex. -/
theorem quotientWave_eq_initial_of_mem_support_mem_quotientSet
    (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    {W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W) {p : (G.quotient X).DPath}
    (hpW : p ∈ W) {x : V} (hxp : x ∈ p.support) (hxX : x ∈ X) :
    x = p.initial := by
  have hxVertex : x ∈ (G.quotient X).vertexSet W := ⟨p, hpW, hxp⟩
  have hxSurvives : x ∉ G.strictRoof X :=
    G.quotientWave_vertexSet_subset_quotientVertexSet hNoEnter hW hxVertex
  have hxSource : x ∈ (G.quotient X).source := by
    rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hNoEnter]
    exact ⟨Or.inr hxX, hxSurvives⟩
  exact DWeb.NoEdgeEnters.eq_initial_of_mem_path
    (G := G.quotient X) hNoEnter.quotient p hxp hxSource

/-- Consequently, an essential final common-wave path meeting the accumulated
closure starts at a point of that closure.  This is the source-faithful
starting point for the finite-arrow ancestry induction: later vertices never
have to be connected back to an arbitrary marked point of the path. -/
theorem essentialMeetingPath_initial_mem
    (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    {W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W) {p : (G.quotient X).DPath}
    (hp : p ∈ (G.quotient X).essentialMeetingPaths W X) :
    p.initial ∈ X := by
  obtain ⟨x, hxp, hxX⟩ := hp.2
  exact (G.quotientWave_eq_initial_of_mem_support_mem_quotientSet
    hNoEnter hW hp.1.1 hxp hxX) ▸ hxX

/-- Members of an essential subwarp are finite. -/
theorem finite_of_mem_essentialWarpPart {W : Set G.DPath} {p : G.DPath}
    (hp : p ∈ G.essentialWarpPart W) :
    ∃ f : DirectedPath.FinitePath G.graph, p = .inl f := by
  obtain ⟨_hpW, t, hpt, _ht⟩ := hp
  rcases p with f | r
  · exact ⟨f, rfl⟩
  · simp at hpt

/-- A nontrivial transported path whose initial vertex already belongs to
the old commitment set comes from an old finite path with exactly the same
support and terminal.  The transport can only retain a terminal-roof
suffix; containing the old commitment point forces that suffix to begin at
the old path's own initial vertex. -/
theorem exists_old_finite_path_same_support_of_mem_waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source) {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave)
    {p : (G.quotient Y).DPath}
    (hp : p ∈ (G.waveToLargerQuotient hNoEnter hXY W).1)
    (hpNontrivial : p ≠ (G.quotient Y).trivialPath p.initial)
    (hpInitial : p.initial ∈ X) :
    ∃ q : DirectedPath.FinitePath (G.quotient X).graph,
      (Sum.inl q : (G.quotient X).DPath) ∈ W.1 ∧
      q.support = p.support ∧
      (G.quotient X).terminal? (.inl q) =
        (G.quotient Y).terminal? p := by
  obtain ⟨z, hzp, hzNe⟩ :=
    (G.quotient Y).exists_support_ne_initial_of_ne_trivial p hpNontrivial
  have hzY : z ∉ Y :=
    (G.quotientPath_avoids_after_initial Y p hzp hzNe).2
  obtain ⟨q, hqW, _hqSurvives, hpSupport, hpTerminal⟩ :=
    G.exists_old_finite_path_of_mem_waveToLargerQuotient_of_not_mem
      hNoEnter hXY W hp hzp hzY
  have hpInitialSuffix : p.initial ∈
      ((G.quotient X).terminalRoofSuffix Y q).support := by
    rw [← hpSupport]
    exact p.initial_mem_support
  have hpInitialQ : p.initial ∈ q.support :=
    (G.quotient X).terminalRoofSuffix_support_suffix Y q |>.subset
      hpInitialSuffix
  have hInitial : p.initial = q.start :=
    G.quotientWave_eq_initial_of_mem_support_mem_quotientSet
      hNoEnter W.2 hqW hpInitialQ hpInitial
  have hqStartSuffix : q.start ∈
      ((G.quotient X).terminalRoofSuffix Y q).support := by
    rwa [← hInitial]
  have hSuffix := (G.quotient X).terminalRoofSuffix_support_eq_of_start_mem
    Y q hqStartSuffix
  refine ⟨q, hqW, ?_, ?_⟩
  · exact hSuffix.symm.trans hpSupport.symm
  · simpa only [DWeb.terminal?_finite] using hpTerminal.symm

/-- A quotient-wave member which contains a committed vertex becomes a
member of the lifted meeting set, with all of its support retained. -/
theorem mem_meetingVertexSet_liftQuotientFamily
    {X : Set V} {W : Set (G.quotient X).DPath}
    {p : (G.quotient X).DPath} (hpW : p ∈ W)
    {x z : V} (hxp : x ∈ p.support) (hxX : x ∈ X)
    (hzp : z ∈ p.support) :
    z ∈ G.meetingVertexSet (SafeLink.liftQuotientFamily G X W) X := by
  let q : G.DPath := G.liftQuotientPath X p
  have hqW : q ∈ SafeLink.liftQuotientFamily G X W := ⟨p, hpW, rfl⟩
  have hxq : x ∈ q.support := by simpa only [q, G.support_liftQuotientPath]
  have hzq : z ∈ q.support := by simpa only [q, G.support_liftQuotientPath]
  rw [meetingVertexSet]
  exact Set.mem_iUnion_of_mem q (Set.mem_iUnion_of_mem
    ⟨hqW, ⟨x, hxq, hxX⟩⟩ hzq)

end DWeb

namespace SafeLink

variable {V : Type u}

/-- Proposition 6.3(c) for the actual dependent Section 6 closure.  The
grounding-set inclusion is a literal successor clause of the recursion.
For the strict-roof clause, the chosen boundedness witness is transported
to the first carrier containing its grounding set, compared with the maximal
successor wave there, and then followed through the common quotient and the
countable arrow. -/
theorem sectionSixAccumClosure_grounding
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T : Set V} (hT : Maximal (G.IsTreeSet a) T) :
    let base := G.delete {a}
    let hNoEnter : base.NoEdgeEnters base.source :=
      delete_root_noEdgeEnters_source G hG a
    let F := fun z ↦ boundaryObstruction G hG hT z
    let K := groundingSet G a T
    let Y := G.outerBoundary T
    let Q := nonBoundedTreeVertices G a T
    let X := base.sectionSixAccumClosure hNoEnter F K Y Q T
    let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T
    ∀ y t, t ∈ X y \ Q →
      K t ⊆ X y ∧
      t ∈ G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a (X y) (M y).1)) := by
  dsimp only
  intro y t ht
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T y
  obtain ⟨n, htn⟩ := Set.mem_iUnion.mp ht.1
  have htStage : t ∈
      (base.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier \ Q :=
    ⟨htn, ht.2⟩
  have hKsucc : K t ⊆
      (base.sectionSixAccumStage hNoEnter F K Y Q T y (n + 1)).carrier :=
    base.sectionSixAccum_K_subset_succ hNoEnter F K Y Q T y n htStage
  have hKX : K t ⊆ X := hKsucc.trans
    (base.sectionSixAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y (n + 1))
  refine ⟨by simpa only [K, X] using hKX, ?_⟩

  have htOffRoot : t ∈ T \ {a} := by
    apply G.sectionSixAccumStage_carrier_subset_offRoot a hNoEnter
      F K Y Q T y
      (boundaryObstruction_subset G hG hT)
      (groundingSet_subset_offRoot G a T) n
    exact htn
  have htBounded : IsBoundedTreeVertex G a T t := by
    by_contra htNotBounded
    exact ht.2 ⟨htOffRoot.1, htNotBounded⟩
  obtain ⟨U, hU, htStrictG⟩ :=
    exists_wave_for_groundingSet G a T htBounded
  let Uw : (base.quotient (K t)).Wave := ⟨U, hU⟩
  let s := base.sectionSixAccumStage hNoEnter F K Y Q T y n
  let Xnext := base.sectionSixAccumNextCarrier F K Y Q T s
  have hKnext : K t ⊆ Xnext := by
    intro x hx
    exact Or.inl (Or.inr
      (Set.mem_iUnion_of_mem t (Set.mem_iUnion_of_mem htStage hx)))
  let oldAtNext := base.waveToLargerQuotient hNoEnter hKnext Uw
  let next := base.sectionSixAccumNext hNoEnter F K Y Q T s

  have hRoofTransport :
      base.roof ((base.quotient (K t)).terminalFrontier Uw.1) ⊆
        base.roof ((base.quotient Xnext).terminalFrontier oldAtNext.1) :=
    base.roof_terminalFrontier_subset_waveToLargerQuotient
      hNoEnter hKnext Uw

  have hOldNextQ :
      (base.quotient Xnext).RoofLE oldAtNext.1 next.wave.1 := by
    exact base.sectionSixAccumNext_roofs hNoEnter F K Y Q T s oldAtNext
  have hRoofNext :
      base.roof ((base.quotient Xnext).terminalFrontier oldAtNext.1) ⊆
        base.roof ((base.quotient Xnext).terminalFrontier next.wave.1) :=
    base.original_roofLE_of_quotient_roofLE hNoEnter
      next.wave.2 hOldNextQ

  have hXnextX : Xnext ⊆ X := by
    intro x hx
    apply Set.mem_iUnion_of_mem (n + 1)
    change x ∈ Xnext
    exact hx
  let commonNext := base.waveToLargerQuotient hNoEnter hXnextX next.wave

  have hRoofCommonStage :
      base.roof ((base.quotient Xnext).terminalFrontier next.wave.1) ⊆
        base.roof ((base.quotient X).terminalFrontier commonNext.1) := by
    exact base.roof_terminalFrontier_subset_waveToLargerQuotient hNoEnter
      hXnextX next.wave

  have hCommonNextEq : commonNext =
      base.sectionSixAccumCommonStage hNoEnter F K Y Q T y (n + 1) := by
    apply Subtype.ext
    rfl

  have hCommonFinalQ :
      (base.quotient X).RoofLE commonNext.1 M.1 := by
    rw [hCommonNextEq]
    exact base.sectionSixAccumCommonStage_roofLE
      hNoEnter F K Y Q T y (n + 1)
  have hRoofFinal :
      base.roof ((base.quotient X).terminalFrontier commonNext.1) ⊆
        base.roof ((base.quotient X).terminalFrontier M.1) :=
    base.original_roofLE_of_quotient_roofLE hNoEnter M.2 hCommonFinalQ

  have hRoofAll :
      base.roof ((base.quotient (K t)).terminalFrontier U) ⊆
        base.roof ((base.quotient X).terminalFrontier M.1) :=
    hRoofTransport.trans
      (hRoofNext.trans (hRoofCommonStage.trans hRoofFinal))
  have htStrictBaseOld :
      t ∈ base.strictRoof ((base.quotient (K t)).terminalFrontier U) := by
    have hdelete := G.strictRoof_subset_delete_strictRoof
      ((base.quotient (K t)).terminalFrontier U) ({a} : Set V)
    apply hdelete
    change t ∈ G.strictRoof
      ((base.quotient (K t)).terminalFrontier U)
    rw [← base.terminalFrontier_liftQuotientFamily]
    rw [← G.terminalFrontier_liftDeleteFamily]
    exact htStrictG
  have htStrictBaseFinal :
      t ∈ base.strictRoof ((base.quotient X).terminalFrontier M.1) :=
    base.strictRoof_mono_of_roof_mono hRoofAll htStrictBaseOld
  have htNeA : t ≠ a := by
    intro hta
    exact htOffRoot.2 (hta ▸ Set.mem_singleton a)
  have htStrictFinal := strictRoof_delete_source_subset_ambient_of_ne
    G hG ha htNeA htStrictBaseFinal
  change t ∈ G.strictRoof (G.terminalFrontier
    (G.liftDeleteFamily {a} (base.liftQuotientFamily X M.1)))
  rw [G.terminalFrontier_liftDeleteFamily,
    base.terminalFrontier_liftQuotientFamily]
  exact htStrictFinal

end SafeLink

end Erdos599
