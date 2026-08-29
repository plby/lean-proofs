/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.LadderConstruction
import ErdosProblems.Erdos599.LadderFrontierInvariants
import ErdosProblems.Erdos599.LadderSuccessorBridge
import ErdosProblems.Erdos599.RegularSplitLegality

/-!
# Constructing stage intervals from surviving ladder components

This file supplies the path-geometric constructor behind
`SliceCandidate.StageIntervalRealization`.  Its input records that the
essential component ending at a selected point of the earlier frontier has
an essential extension at the later stage.  The selected interval is the
literal suffix of that later finite path after the earlier terminal.

The additional `LadderGrows` hypothesis is used only for endpoint purity:
it rules out a suffix meeting the terminal of a different earlier-stage
component.  This is the exact survival/growth information available in the
canonical ladder construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath

universe u

variable {V : Type u}

private theorem finitePath_eq_of_walk_support_eq
    {D : Digraph V} (p q : FinitePath D)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hsupport : p.walk.support = q.walk.support) : p = q := by
  rcases p with ⟨a, b, p, hp⟩
  rcases q with ⟨c, d, q, hq⟩
  dsimp only at hstart hfinish hsupport
  subst c
  subst d
  have hpq : p = q := DirectedPath.Walk.eq_of_support_eq p q hsupport
  subst q
  rfl

/-- If `p` is a finite prefix of `q`, the canonical suffix of `q` starting
at `p.finish` has exactly the vertices following that prefix, with the
common endpoint retained as its first vertex. -/
theorem suffixFrom_support_eq_of_isPrefixOf
    {D : Digraph V} (p q : FinitePath D) (hpq : p.IsPrefixOf q) :
    let hx : p.finish ∈ q.support := hpq.support_subset p.finish_mem_support
    ∃ tail : List V,
      p.walk.support ++ tail = q.walk.support ∧
      (q.suffixFrom p.finish hx).walk.support = p.finish :: tail := by
  let hx : p.finish ∈ q.support := hpq.support_subset p.finish_mem_support
  obtain ⟨tail, htail⟩ := hpq
  refine ⟨tail, htail, ?_⟩
  have hdesired : p.finish :: tail <:+ q.walk.support := by
    refine ⟨p.walk.support.dropLast, ?_⟩
    calc
      p.walk.support.dropLast ++ p.finish :: tail =
          (p.walk.support.dropLast ++ [p.finish]) ++ tail := by simp
      _ = p.walk.support ++ tail := by
        have hlast := List.dropLast_append_getLast p.walk.support_ne_nil
        simpa only [p.walk.getLast_support] using
          congrArg (fun l : List V ↦ l ++ tail) hlast
      _ = q.walk.support := htail
  have hsuffix : (q.suffixFrom p.finish hx).walk.support <:+
      q.walk.support := by
    unfold FinitePath.suffixFrom
    exact (q.walk.lastHit {p.finish}
      ⟨p.finish, hx, Set.mem_singleton p.finish⟩).support_suffix
  rcases List.suffix_total hsuffix hdesired with hsd | hds
  · apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := by simp) hsd
    · change p.finish ∈ (q.suffixFrom p.finish hx).walk.support
      have hstart := (q.suffixFrom p.finish hx).start_mem_support
      change (q.suffixFrom p.finish hx).start ∈
        (q.suffixFrom p.finish hx).walk.support at hstart
      simpa only [FinitePath.suffixFrom_start] using hstart
    · exact hdesired.nodup q.isPath
  · symm
    apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := (q.suffixFrom p.finish hx).walk.support_ne_nil) hds
    · rw [(q.suffixFrom p.finish hx).walk.head_support,
        FinitePath.suffixFrom_start]
      exact List.mem_cons_self
    · exact hsuffix.nodup q.isPath

/-- A prefix meets its canonical complementary suffix only at their common
endpoint. -/
theorem support_inter_suffixFrom_eq_of_isPrefixOf
    {D : Digraph V} (p q : FinitePath D) (hpq : p.IsPrefixOf q) :
    let hx : p.finish ∈ q.support := hpq.support_subset p.finish_mem_support
    p.support ∩ (q.suffixFrom p.finish hx).support = {p.finish} := by
  let hx : p.finish ∈ q.support := hpq.support_subset p.finish_mem_support
  obtain ⟨tail, htail, hsuffix⟩ :=
    suffixFrom_support_eq_of_isPrefixOf p q hpq
  have hnodup : (p.walk.support ++ tail).Nodup := by
    rw [htail]
    exact q.isPath
  have hdis := (List.nodup_append.mp hnodup).2.2
  ext y
  constructor
  · rintro ⟨hyp, hyq⟩
    change y ∈ p.walk.support at hyp
    change y ∈ (q.suffixFrom p.finish hx).walk.support at hyq
    rw [hsuffix] at hyq
    rcases List.mem_cons.mp hyq with rfl | hytail
    · exact Set.mem_singleton p.finish
    · exact (hdis y hyp y hytail rfl).elim
  · intro hy
    have hyfinish : y = p.finish := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨p.finish_mem_support, ?_⟩
    change p.finish ∈ (q.suffixFrom p.finish hx).walk.support
    have hstart := (q.suffixFrom p.finish hx).start_mem_support
    change (q.suffixFrom p.finish hx).start ∈
      (q.suffixFrom p.finish hx).walk.support at hstart
    simpa only [FinitePath.suffixFrom_start] using hstart

/-- Appending a finite prefix to its canonical complementary suffix
reconstructs the original finite path literally. -/
theorem appendFinite_suffixFrom_eq_of_isPrefixOf
    {D : Digraph V} (p q : FinitePath D) (hpq : p.IsPrefixOf q) :
    let hx : p.finish ∈ q.support := hpq.support_subset p.finish_mem_support
    let s := q.suffixFrom p.finish hx
    Path.appendFinite p (.inl s) (FinitePath.suffixFrom_start q p.finish hx)
      (support_inter_suffixFrom_eq_of_isPrefixOf p q hpq).subset =
        (.inl q : Path D) := by
  let hx : p.finish ∈ q.support := hpq.support_subset p.finish_mem_support
  let s := q.suffixFrom p.finish hx
  have hinter : p.support ∩ s.support ⊆ {p.finish} :=
    (support_inter_suffixFrom_eq_of_isPrefixOf p q hpq).subset
  change (Sum.inl (p.appendFinite s
    (FinitePath.suffixFrom_start q p.finish hx) hinter) : Path D) = .inl q
  congr 1
  apply finitePath_eq_of_walk_support_eq
  · exact (p.appendFinite_start s _ _).trans hpq.start_eq
  · exact p.appendFinite_finish s _ _
  · obtain ⟨tail, htail, hsuffix⟩ :=
      suffixFrom_support_eq_of_isPrefixOf p q hpq
    rw [p.appendFinite_walk_support s _ _, hsuffix]
    simpa only [List.tail_cons] using htail

/-- Coordinatewise essential extensions from an earlier ladder frontier to
a later accumulated warp.  No final limiting warp occurs in this datum. -/
structure EssentialStageExtensions
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (delta beta : Ladder.Stage kappa)
    (S : Set V) where
  leftPrefix : S → FinitePath Gamma.graph
  rightPrefix : S → FinitePath Gamma.graph
  left_mem : ∀ x, (Sum.inl (leftPrefix x) : Gamma.DPath) ∈
    Gamma.essentialWarpPart (L.warpAt delta)
  right_mem : ∀ x, (Sum.inl (rightPrefix x) : Gamma.DPath) ∈
    Gamma.essentialWarpPart (L.warpAt beta)
  left_finish : ∀ x, (leftPrefix x).finish = x.1
  extension : ∀ x, Gamma.Extends (.inl (leftPrefix x)) (.inl (rightPrefix x))

namespace EssentialStageExtensions

variable {Gamma : DWeb V} {kappa : Cardinal.{u}}
  {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
  {S : Set V}

private theorem finish_mem_essential_of_mem_essentialWarpPart
    {W : Set Gamma.DPath} {p : FinitePath Gamma.graph}
    (hp : (Sum.inl p : Gamma.DPath) ∈ Gamma.essentialWarpPart W) :
    p.finish ∈ Gamma.essential (Gamma.terminalFrontier W) := by
  obtain ⟨t, hterm, ht⟩ := hp.2
  have hfinish : p.finish = t := Option.some.inj hterm
  exact hfinish ▸ ht

theorem rightPrefix_injective (E : EssentialStageExtensions L delta beta S)
    (hdelta : Gamma.IsWarp (L.warpAt delta)) :
    Function.Injective E.rightPrefix := by
  intro x y hright
  have hleft : E.leftPrefix x = E.leftPrefix y := by
    by_contra hne
    have hdis := hdelta (E.left_mem x).1 (E.left_mem y).1
      (fun h ↦ hne (Sum.inl.inj h))
    have hstartx := Gamma.extends_initial (E.extension x)
    have hstarty := Gamma.extends_initial (E.extension y)
    apply Set.disjoint_left.1 hdis
      (E.leftPrefix x).start_mem_support
    have hstarts : (E.leftPrefix x).start =
        (E.leftPrefix y).start := by
      calc
        (E.leftPrefix x).start = (E.rightPrefix x).start := by
          simpa only [Path.initial] using hstartx
        _ = (E.rightPrefix y).start := congrArg FinitePath.start hright
        _ = (E.leftPrefix y).start := by
          simpa only [Path.initial] using hstarty.symm
    exact hstarts ▸ (E.leftPrefix y).start_mem_support
  apply Subtype.ext
  calc
    x.1 = (E.leftPrefix x).finish := (E.left_finish x).symm
    _ = (E.leftPrefix y).finish := congrArg FinitePath.finish hleft
    _ = y.1 := E.left_finish y

private theorem exists_essentialFinitePath_finish
    (hroof : L.RoofsSourceAtStages) {a : Ladder.Stage kappa}
    {x : V} (hx : x ∈ L.frontier a) :
    ∃ p : FinitePath Gamma.graph,
      (Sum.inl p : Gamma.DPath) ∈
        Gamma.essentialWarpPart (L.warpAt a) ∧ p.finish = x := by
  obtain ⟨p, hp, hterm⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (hroof (Ladder.Stage.toExtended a)) hx
  rcases p with p | r
  · exact ⟨p, hp, Option.some.inj hterm⟩
  · simp at hterm

noncomputable def segment (E : EssentialStageExtensions L delta beta S)
    (x : S) : FinitePath Gamma.graph :=
  let hx : (E.leftPrefix x).finish ∈ (E.rightPrefix x).support := by
    change (E.leftPrefix x).finish ∈
      Path.support (.inl (E.rightPrefix x))
    exact Gamma.support_mono_of_extends (E.extension x)
      (E.leftPrefix x).finish_mem_support
  (E.rightPrefix x).suffixFrom (E.leftPrefix x).finish hx

@[simp]
theorem segment_start (E : EssentialStageExtensions L delta beta S)
    (x : S) : (E.segment x).start = x.1 := by
  unfold segment
  exact (FinitePath.suffixFrom_start _ _ _).trans (E.left_finish x)

@[simp]
theorem segment_finish (E : EssentialStageExtensions L delta beta S)
    (x : S) : (E.segment x).finish = (E.rightPrefix x).finish := by
  unfold segment
  exact FinitePath.suffixFrom_finish _ _ _

theorem segment_subpath (E : EssentialStageExtensions L delta beta S)
    (x : S) : (E.segment x).IsSubpathOf (.inl (E.rightPrefix x)) := by
  unfold segment
  exact FinitePath.suffixFrom_isSubpathOf _ _ _

theorem prefix_inter (E : EssentialStageExtensions L delta beta S)
    (x : S) :
    (E.leftPrefix x).support ∩ (E.segment x).support =
      {(E.leftPrefix x).finish} := by
  exact support_inter_suffixFrom_eq_of_isPrefixOf
    (E.leftPrefix x) (E.rightPrefix x) (E.extension x)

theorem append_eq (E : EssentialStageExtensions L delta beta S)
    (x : S) :
    Path.appendFinite (E.leftPrefix x) (.inl (E.segment x))
      (E.segment_start x |>.trans (E.left_finish x).symm)
      (E.prefix_inter x).subset =
        (.inl (E.rightPrefix x) : Gamma.DPath) := by
  exact appendFinite_suffixFrom_eq_of_isPrefixOf
    (E.leftPrefix x) (E.rightPrefix x) (E.extension x)

theorem segment_frontier_delta
    (E : EssentialStageExtensions L delta beta S)
    (hL : L.IsSplitLegal)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta))
    (x : S) :
    (E.segment x).support ∩ L.frontier delta = {(E.segment x).start} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hyseg, hyfrontier⟩
    obtain ⟨p, hp, hpfinish⟩ :=
      exists_essentialFinitePath_finish hL.roofsSourceAtStages hyfrontier
    obtain ⟨q, hq, hpq⟩ := hgrows (.inl p) hp.1
    have hqright : q = (.inl (E.rightPrefix x) : Gamma.DPath) := by
      by_contra hne
      have hdis := hL.warpStages (Ladder.Stage.toExtended beta)
        hq (E.right_mem x).1 hne
      exact Set.disjoint_left.1 hdis
        (Gamma.support_mono_of_extends hpq
          (hpfinish.symm ▸ p.finish_mem_support))
        ((E.segment_subpath x).1 hyseg)
    have hpleft : p = E.leftPrefix x := by
      by_contra hne
      have hdis := hL.warpStages (Ladder.Stage.toExtended delta)
        hp.1 (E.left_mem x).1 (fun h ↦ hne (Sum.inl.inj h))
      have hpstart := Gamma.extends_initial hpq
      have hlstart := Gamma.extends_initial (E.extension x)
      apply Set.disjoint_left.1 hdis p.start_mem_support
      have : p.start = (E.leftPrefix x).start := by
        calc
          p.start = q.initial := hpstart
          _ = (E.rightPrefix x).start := by
            rw [hqright]
            rfl
          _ = (E.leftPrefix x).start := by
            simpa only [Path.initial] using hlstart.symm
      exact this ▸ (E.leftPrefix x).start_mem_support
    apply Set.mem_singleton_iff.mpr
    calc
      y = p.finish := hpfinish.symm
      _ = (E.leftPrefix x).finish := congrArg FinitePath.finish hpleft
      _ = x.1 := E.left_finish x
      _ = (E.segment x).start := (E.segment_start x).symm
  · intro y hy
    have hy' : y = (E.segment x).start := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨(E.segment x).start_mem_support, ?_⟩
    rw [E.segment_start x,
      L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages delta]
    rw [← E.left_finish x]
    exact finish_mem_essential_of_mem_essentialWarpPart (E.left_mem x)

theorem segment_frontier_beta
    (E : EssentialStageExtensions L delta beta S)
    (hL : L.IsSplitLegal) (x : S) :
    (E.segment x).support ∩ L.frontier beta = {(E.segment x).finish} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hyseg, hyfrontier⟩
    obtain ⟨p, hp, hpfinish⟩ :=
      exists_essentialFinitePath_finish hL.roofsSourceAtStages hyfrontier
    have hpright : p = E.rightPrefix x := by
      by_contra hne
      have hdis := hL.warpStages (Ladder.Stage.toExtended beta)
        hp.1 (E.right_mem x).1 (fun h ↦ hne (Sum.inl.inj h))
      exact Set.disjoint_left.1 hdis
        (hpfinish.symm ▸ p.finish_mem_support)
        ((E.segment_subpath x).1 hyseg)
    apply Set.mem_singleton_iff.mpr
    calc
      y = p.finish := hpfinish.symm
      _ = (E.rightPrefix x).finish := congrArg FinitePath.finish hpright
      _ = (E.segment x).finish := (E.segment_finish x).symm
  · intro y hy
    have hy' : y = (E.segment x).finish := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨(E.segment x).finish_mem_support, ?_⟩
    rw [E.segment_finish x]
    rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages beta]
    exact finish_mem_essential_of_mem_essentialWarpPart (E.right_mem x)

/-- Surviving essential components at two ladder stages canonically produce
the exact `StageIntervalRealization` consumed by the component-replacement
slice constructor. -/
noncomputable def toStageIntervalRealization
    (E : EssentialStageExtensions L delta beta S)
    (hL : L.IsSplitLegal)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta)) :
    StageIntervalRealization L delta beta S where
  source_subset x hx := by
    rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages delta]
    have hessential := finish_mem_essential_of_mem_essentialWarpPart
      (E.left_mem ⟨x, hx⟩)
    simpa only [E.left_finish] using hessential
  carrier := fun x ↦ .inl (E.rightPrefix x)
  carrier_mem x := (E.right_mem x).1
  carrier_injective := by
    intro x y hxy
    exact E.rightPrefix_injective
      (hL.warpStages (Ladder.Stage.toExtended delta))
      (Sum.inl.inj hxy)
  segment := E.segment
  segment_start := E.segment_start
  segment_finish_mem x := by
    rw [E.segment_finish x]
    rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages beta]
    exact finish_mem_essential_of_mem_essentialWarpPart (E.right_mem x)
  segment_subpath := E.segment_subpath
  segment_endpoints x := by
    rw [Set.inter_union_distrib_left, E.segment_frontier_delta hL hgrows x,
      E.segment_frontier_beta hL x]
    rfl
  segment_source x := E.segment_frontier_delta hL hgrows x
  leftPrefix := E.leftPrefix
  rightPrefix := E.rightPrefix
  left_mem := E.left_mem
  right_mem := E.right_mem
  left_finish := E.left_finish
  right_finish x := (E.segment_finish x).symm
  prefix_inter := E.prefix_inter
  append_eq := E.append_eq

end EssentialStageExtensions

end SliceCandidate
end CardinalInduction
end Erdos599
