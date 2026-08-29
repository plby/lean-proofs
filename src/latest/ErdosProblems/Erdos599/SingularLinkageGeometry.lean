/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularContinuation

/-!
# Terminal-exact linkage geometry for singular continuation

The singular continuation construction needs the old source--stopover
linkage to meet the stopover only at path terminals.  This property follows
directly when the stopover is *exactly* the terminal frontier: a warp member
cannot contain the terminal of a distinct member.

The resulting terminal-clean certificate, together with the separating
property of the stopover, also supplies the old-family roof bound used by
the quotient continuation.  Separation is retained as an explicit premise:
a source--`C` linkage by itself does not imply that `C` separates the source
from the target.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularContinuation

universe u

variable {V : Type u}

/-- A warp is terminal-clean at any set which is exactly its terminal
frontier.  The proof uses only vertex-disjointness of distinct members. -/
theorem terminalCleanAt_of_isWarp_terminalFrontier_eq
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (hW : G.IsWarp W) (hfront : G.terminalFrontier W = C) :
    TerminalCleanAt G W C := by
  rw [← hfront]
  intro p hpW x hxp hxFrontier
  obtain ⟨q, hqW, hqx⟩ := hxFrontier
  have hpq : p = q := by
    by_contra hpq
    exact Set.disjoint_left.1 (hW hpW hqW hpq) hxp
      (G.terminal_mem_support hqx)
  subst q
  exact hqx

/-- A full source--`C` linkage with exact terminal frontier is
terminal-clean at `C`. -/
theorem terminalCleanAt_of_linkage_terminalFrontier_eq
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hfront : G.terminalFrontier W = C) :
    TerminalCleanAt G W C :=
  terminalCleanAt_of_isWarp_terminalFrontier_eq G hW.isWarp hfront

/-- Exact terminal-frontier data and separation give the old-family roof
bound required by singular quotient continuation.  The separator premise
is necessary: existence of a source--`C` linkage alone does not make `C` a
source--target separator. -/
theorem linkage_vertexSet_subset_roof_of_terminalFrontier_eq
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (hfront : G.terminalFrontier W = C) :
    G.vertexSet W ⊆ G.roof C := by
  exact linkage_vertexSet_subset_roof G hW hsep
    (terminalCleanAt_of_linkage_terminalFrontier_eq G hW hfront)

/-- Bundle the two geometric facts consumed together at a singular
continuation step. -/
theorem terminalCleanAt_and_vertexSet_subset_roof_of_linkage_terminalFrontier_eq
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (hfront : G.terminalFrontier W = C) :
    TerminalCleanAt G W C ∧ G.vertexSet W ⊆ G.roof C := by
  let hclean := terminalCleanAt_of_linkage_terminalFrontier_eq G hW hfront
  exact ⟨hclean, linkage_vertexSet_subset_roof G hW hsep hclean⟩

/-- Exact old frontier upgrades the one-sided terminal-frontier statement
for quotient continuation to an equality.  Every lifted quotient path
starts at a quotient source, hence (by the separator/trimmed source
identity and `hfront`) at an actual old terminal.  The generic source-star
lemma then supplies the reverse inclusion. -/
theorem terminalFrontier_continuation_eq_of_terminalFrontier_eq
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (hfront : G.terminalFrontier W = C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUinit : (G.quotient C).initialSet U =
      (G.quotient C).source) :
    G.terminalFrontier
        (continuation G hW hsep htrim hclean U hUinit) =
      (G.quotient C).terminalFrontier U := by
  rw [← G.terminalFrontier_liftQuotientFamily C U]
  apply Set.Subset.antisymm
  · exact terminalFrontier_continuation_subset
      G hW hsep htrim hclean hUinit
  · apply G.terminalFrontier_subset_star
      (DWeb.IsWarp.liftQuotientFamily G hU)
      (starCompatible_liftQuotientFamily_of_linkage
        G hW hsep htrim hclean hUinit)
    rintro q ⟨q₀, hq₀U, rfl⟩
    have hq₀Initial : q₀.initial ∈ (G.quotient C).initialSet U :=
      ⟨q₀, hq₀U, rfl⟩
    rw [hUinit, quotient_source_eq_stopover G hsep htrim] at hq₀Initial
    rw [hfront]
    simpa only [G.initial_liftQuotientPath] using hq₀Initial

/-- In a normalized web, finite source-pure target links can be recovered
from the simpler statement that the selected component starts at the
designated source and terminates in the target. -/
theorem linksToTarget_of_initial_terminal
    (G : DWeb V) (hNorm : G.IsNormalized)
    {W : Set G.DPath} {A : Set V}
    (hfinite : G.HasFiniteCharacter W)
    (hA : A ⊆ G.source)
    (hterminal : ∀ a ∈ A, ∃ p ∈ W, p.initial = a ∧
      ∃ b ∈ G.target, G.terminal? p = some b) :
    LinksToTarget G W A := by
  intro a ha
  obtain ⟨p, hpW, hpInitial, b, hbTarget, hpTerminal⟩ := hterminal a ha
  obtain ⟨f, rfl⟩ := hfinite hpW
  have hfStart : f.start = a := hpInitial
  have hfPure : f.support ∩ A = {a} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxStart : x = f.start :=
        hNorm.eq_initial_of_mem_path (.inl f) hx.1 (hA hx.2)
      exact Set.mem_singleton_iff.2 (hxStart.trans hfStart)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨by simpa only [hfStart] using f.start_mem_support, ha⟩
  have hfFinish : f.finish = b := Option.some.inj hpTerminal
  refine ⟨.inl f, hpW, f, rfl, hfPure, [], f.walk.support.tail, ?_,
    b, hbTarget, ?_⟩
  · simp only [List.nil_append]
    calc
      f.walk.support =
          f.walk.support.head f.walk.support_ne_nil ::
            f.walk.support.tail :=
        (f.walk.support.cons_head_tail f.walk.support_ne_nil).symm
      _ = a :: f.walk.support.tail := by
        exact congrArg (fun x ↦ x :: f.walk.support.tail)
          (f.walk.head_support.trans hfStart)
  · have hcons : a :: f.walk.support.tail = f.walk.support := by
      calc
        a :: f.walk.support.tail =
            f.walk.support.head f.walk.support_ne_nil ::
              f.walk.support.tail := by
          exact congrArg (fun x ↦ x :: f.walk.support.tail)
            (hfStart.symm.trans f.walk.head_support.symm)
        _ = f.walk.support :=
          f.walk.support.cons_head_tail f.walk.support_ne_nil
    change b ∈ a :: f.walk.support.tail
    rw [hcons, ← hfFinish]
    exact f.finish_mem_support

/-- Target links at the active old terminal boundary lift through a full
source quotient continuation to target links at the corresponding original
sources.  The active boundary is written extensionally so this lemma stays
independent of the target-machine bookkeeping module. -/
theorem linksToTarget_continuation_of_activeBoundary
    (G : DWeb V) (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C D A : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (hA : A ⊆ G.source)
    {U : Set (G.quotient C).DPath}
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D)
    (hUlinks : LinksToTarget (G.quotient C) U
      {c | ∃ p ∈ W, p.initial ∈ A ∧ G.terminal? p = some c}) :
    LinksToTarget G
      (continuation G hW hsep htrim hclean U hD.linkage.initialSet_eq) A := by
  let boundary : Set V :=
    {c | ∃ p ∈ W, p.initial ∈ A ∧ G.terminal? p = some c}
  let L : Set G.DPath := liftedQuotientFamily G C U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_linkage
      G hW hsep htrim hclean hD.linkage.initialSet_eq
  have hterminal : ∀ a ∈ A, ∃ p ∈ G.star hc, p.initial = a ∧
      ∃ b ∈ G.target, G.terminal? p = some b := by
    intro a ha
    have haInitial : a ∈ G.initialSet W := hW.initialSet_eq.symm ▸ hA ha
    obtain ⟨p, hpW, hpInitial⟩ := haInitial
    obtain ⟨f, rfl⟩ := hW.finiteCharacter hpW
    have hfStart : f.start = a := hpInitial
    have hfBoundary : f.finish ∈ boundary := by
      refine ⟨.inl f, hpW, ?_, rfl⟩
      change f.start ∈ A
      rw [hfStart]
      exact ha
    obtain ⟨q, hqU, g, rfl, hgPure, hgSuffix⟩ :=
      hUlinks f.finish hfBoundary
    have hfSupport : f.finish ∈ g.support := by
      have : f.finish ∈ g.support ∩ boundary := by
        rw [hgPure]
        exact Set.mem_singleton f.finish
      exact this.1
    have hfC : f.finish ∈ C := by
      exact hW.terminalFrontier_subset ⟨.inl f, hpW, rfl⟩
    have hfQuotientSource : f.finish ∈ (G.quotient C).source := by
      rw [quotient_source_eq_stopover G hsep htrim]
      exact hfC
    have hgStart : g.start = f.finish := by
      obtain ⟨r, hrg, _hrEnds, hrSource⟩ :=
        hD.linkage.endpointPure (.inl g) hqU
      have hrgEq : r = g := by simpa using hrg.symm
      subst r
      have hfSource : f.finish ∈ g.support ∩ (G.quotient C).source :=
        ⟨hfSupport, hfQuotientSource⟩
      rw [hrSource] at hfSource
      exact (Set.mem_singleton_iff.1 hfSource).symm
    obtain ⟨_before, _after, hgSupport, b, hbTarget, hbAfter⟩ := hgSuffix
    have hbSupport : b ∈ g.support := by
      change b ∈ g.walk.support
      rw [hgSupport]
      exact List.mem_append_right _ hbAfter
    have hbLiftSupport : b ∈
        (G.liftQuotientPath C (.inl g)).support := by
      rw [G.support_liftQuotientPath]
      exact hbSupport
    have hgTerminal : G.terminal?
        (G.liftQuotientPath C (.inl g)) = some b :=
      hNorm.terminal?_eq_of_mem_path
        (G.liftQuotientPath C (.inl g)) hbLiftSupport hbTarget
    let old : W := ⟨(.inl f : G.DPath), hpW⟩
    have hLiftMem : G.liftQuotientPath C (.inl g) ∈ L :=
      ⟨.inl g, hqU, rfl⟩
    have hLiftStart : (G.liftQuotientPath C (.inl g)).initial = f.finish := by
      rw [G.initial_liftQuotientPath]
      exact hgStart
    refine ⟨G.starPath hc old, ⟨old, rfl⟩,
      (G.initial_starPath hc old).trans hfStart,
      b, hbTarget, ?_⟩
    dsimp only [old]
    simp only [DWeb.starPath]
    split
    next hex =>
      let q' := Classical.choose hex
      have hq'L : q' ∈ L := (Classical.choose_spec hex).1
      have hq'Start : q'.initial = f.finish :=
        (Classical.choose_spec hex).2
      have hq'Eq : q' = G.liftQuotientPath C (.inl g) := by
        apply DWeb.IsWarp.eq_of_initial_eq G
          (DWeb.IsWarp.liftQuotientFamily G hD.linkage.isWarp)
          hq'L hLiftMem
        exact hq'Start.trans hLiftStart.symm
      calc
        G.terminal? (DirectedPath.Path.appendFinite f q' _ _) =
            G.terminal? q' :=
          DirectedPath.Path.terminal?_appendFinite f q' _ _
        _ = some b := by simpa only [hq'Eq] using hgTerminal
    next hnone =>
      exfalso
      apply hnone
      exact ⟨G.liftQuotientPath C (.inl g), hLiftMem, hLiftStart⟩
  apply linksToTarget_of_initial_terminal G hNorm
    (continuation_finiteCharacter G hW hsep htrim hclean
      hD.linkage.finiteCharacter hD.linkage.initialSet_eq)
    hA
  simpa only [continuation, L, hc] using hterminal

end SingularContinuation
end CardinalInduction
end Erdos599
