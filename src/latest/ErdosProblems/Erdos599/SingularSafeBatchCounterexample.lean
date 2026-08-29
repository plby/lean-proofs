/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFutureSafeBatch

/-!
# Full source coverage does not imply future safety

This finite web records the crossing obstruction behind the joint-selection
field in `SingularFutureSafeBatch`.  There are two disjoint source--target
routes, but the displayed half-way batch uses a different completed route
from `d` through `x`.  The only continuation of the pending `b` component
also uses `x`.  Thus deleting the completed carrier strands the pending
frontier, even though the old stop-over is trimmed and separating.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeBatchCounterexample

open DirectedPath SingularExtension SingularSafeBatch
  SingularFutureSafeBatch

inductive Vertex
  | d | b | x | y | q | w | t1 | t2 | r
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj u v :=
    (u = d ∧ v = x) ∨ (u = x ∧ v = t1) ∨
    (u = d ∧ v = w) ∨ (u = w ∧ v = t2) ∨
    (u = b ∧ v = y) ∨ (u = y ∧ v = x) ∨
    (u = x ∧ v = r) ∨
    (u = b ∧ v = q) ∨ (u = q ∧ v = t1)

@[simp] theorem graph_adj (u v : Vertex) :
    graph.Adj u v ↔
      (u = d ∧ v = x) ∨ (u = x ∧ v = t1) ∨
      (u = d ∧ v = w) ∨ (u = w ∧ v = t2) ∨
      (u = b ∧ v = y) ∨ (u = y ∧ v = x) ∨
      (u = x ∧ v = r) ∨
      (u = b ∧ v = q) ∨ (u = q ∧ v = t1) :=
  Iff.rfl

def dxt1 : FinitePath graph where
  start := d
  finish := t1
  walk := Walk.cons (u := d) (v := x) (w := t1) (by simp [graph])
    (Walk.cons (u := x) (v := t1) (w := t1) (by simp [graph]) Walk.nil)
  isPath := by
    change [d, x, t1].Nodup
    simp

def dwt2 : FinitePath graph where
  start := d
  finish := t2
  walk := Walk.cons (u := d) (v := w) (w := t2) (by simp [graph])
    (Walk.cons (u := w) (v := t2) (w := t2) (by simp [graph]) Walk.nil)
  isPath := by
    change [d, w, t2].Nodup
    simp

def byPath : FinitePath graph where
  start := b
  finish := y
  walk := Walk.cons (u := b) (v := y) (w := y) (by simp [graph]) Walk.nil
  isPath := by
    change [b, y].Nodup
    simp

def yxr : FinitePath graph where
  start := y
  finish := r
  walk := Walk.cons (u := y) (v := x) (w := r) (by simp [graph])
    (Walk.cons (u := x) (v := r) (w := r) (by simp [graph]) Walk.nil)
  isPath := by
    change [y, x, r].Nodup
    simp

def byxr : FinitePath graph where
  start := b
  finish := r
  walk := Walk.cons (u := b) (v := y) (w := r) (by simp [graph])
    (Walk.cons (u := y) (v := x) (w := r) (by simp [graph])
      (Walk.cons (u := x) (v := r) (w := r) (by simp [graph]) Walk.nil))
  isPath := by
    change [b, y, x, r].Nodup
    simp

/-- The second `b`--target route makes `t1` indispensable in the displayed
separator, without changing the incompatible continuation of the old prefix
`b -> y`. -/
def bqt1 : FinitePath graph where
  start := b
  finish := t1
  walk := Walk.cons (u := b) (v := q) (w := t1) (by simp [graph])
    (Walk.cons (u := q) (v := t1) (w := t1) (by simp [graph]) Walk.nil)
  isPath := by
    change [b, q, t1].Nodup
    simp

@[simp] theorem support_dxt1 : dxt1.support = ({d, x, t1} : Set Vertex) := by
  ext v
  change v ∈ [d, x, t1] ↔ _
  simp [or_assoc]

@[simp] theorem support_dwt2 : dwt2.support = ({d, w, t2} : Set Vertex) := by
  ext v
  change v ∈ [d, w, t2] ↔ _
  simp [or_assoc]

@[simp] theorem support_byPath : byPath.support = ({b, y} : Set Vertex) := by
  ext v
  change v ∈ [b, y] ↔ _
  simp

@[simp] theorem support_yxr : yxr.support = ({y, x, r} : Set Vertex) := by
  ext v
  change v ∈ [y, x, r] ↔ _
  simp [or_assoc]

@[simp] theorem support_byxr : byxr.support = ({b, y, x, r} : Set Vertex) := by
  ext v
  change v ∈ [b, y, x, r] ↔ _
  simp [or_assoc]

@[simp] theorem support_bqt1 : bqt1.support = ({b, q, t1} : Set Vertex) := by
  ext v
  change v ∈ [b, q, t1] ↔ _
  simp [or_assoc]

def web : DWeb Vertex where
  graph := graph
  source := {d, b}
  target := {t1, t2, r}

def paths : Set web.DPath := {.inl dxt1, .inl byPath}

def boundary : Set Vertex := {d, t1, y}

@[simp] theorem dxt1_start : dxt1.start = d := rfl
@[simp] theorem dxt1_finish : dxt1.finish = t1 := rfl
@[simp] theorem dwt2_start : dwt2.start = d := rfl
@[simp] theorem dwt2_finish : dwt2.finish = t2 := rfl
@[simp] theorem byPath_start : byPath.start = b := rfl
@[simp] theorem byPath_finish : byPath.finish = y := rfl
@[simp] theorem yxr_start : yxr.start = y := rfl
@[simp] theorem yxr_finish : yxr.finish = r := rfl
@[simp] theorem byxr_start : byxr.start = b := rfl
@[simp] theorem byxr_finish : byxr.finish = r := rfl
@[simp] theorem bqt1_start : bqt1.start = b := rfl
@[simp] theorem bqt1_finish : bqt1.finish = t1 := rfl

theorem web_normalized : web.IsNormalized := by
  intro u v huv
  change graph.Adj u v at huv
  simp only [graph_adj] at huv
  rcases huv with huv | huv | huv | huv | huv | huv | huv | huv | huv
  all_goals rcases huv with ⟨rfl, rfl⟩ <;> simp [web]

theorem paths_isWarp : web.IsWarp paths := by
  intro p hp q hq hpq
  simp only [paths, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint dxt1.support byPath.support
    rw [support_dxt1, support_byPath]
    exact Set.disjoint_left.2 (by intro v hv₁ hv₂; cases v <;> simp_all)
  · change Disjoint byPath.support dxt1.support
    rw [support_byPath, support_dxt1]
    exact Set.disjoint_left.2 (by intro v hv₁ hv₂; cases v <;> simp_all)
  · exact (hpq rfl).elim

theorem paths_finiteCharacter : web.HasFiniteCharacter paths := by
  intro p hp
  simp only [paths, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨dxt1, rfl⟩
  · exact ⟨byPath, rfl⟩

@[simp] theorem paths_initialSet : web.initialSet paths = web.source := by
  ext v
  constructor
  · rintro ⟨p, hp, hpv⟩
    simp only [paths, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · left
      change d = v at hpv
      exact hpv.symm
    · right
      change b = v at hpv
      exact hpv.symm
  · intro hv
    change v ∈ ({d, b} : Set Vertex) at hv
    rcases hv with (rfl | hv)
    · exact ⟨.inl dxt1, by simp [paths], rfl⟩
    · have : v = b := by simpa using hv
      subst v
      exact ⟨.inl byPath, by simp [paths], rfl⟩

@[simp] theorem paths_terminalFrontier :
    web.terminalFrontier paths = ({t1, y} : Set Vertex) := by
  ext v
  constructor
  · rintro ⟨p, hp, hpv⟩
    simp only [paths, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · left
      simpa [web, dxt1] using hpv.symm
    · right
      simpa [web, byPath] using hpv.symm
  · intro hv
    rcases hv with (rfl | hv)
    · exact ⟨.inl dxt1, by simp [paths], rfl⟩
    · have : v = y := by simpa using hv
      subst v
      exact ⟨.inl byPath, by simp [paths], rfl⟩

/-- A separating half-way stop-over need not be a wave: wave maximality is
ordered by the actual terminal frontier, not by the larger recorded
stop-over.  Here `boundary` separates because it also contains `d`, while
the displayed terminal frontier `{t1,y}` misses the route `d-w-t2`. -/
theorem paths_not_isWave : ¬ web.IsWave paths := by
  intro hwave
  have hdRoof : d ∈ web.roof (web.terminalFrontier paths) :=
    hwave.2.2 (by simp [web])
  rw [paths_terminalFrontier] at hdRoof
  obtain ⟨z, hzPath, hzFrontier⟩ :=
    hdRoof dwt2 ⟨rfl, by simp [web]⟩
  change z ∈ [d, w, t2] at hzPath
  cases z <;> simp at hzPath hzFrontier

theorem paths_linkage :
    IsLinkageBetween web web.source boundary paths := by
  refine ⟨paths_isWarp, paths_finiteCharacter, paths_initialSet,
    ?_, ?_⟩
  · rw [paths_terminalFrontier]
    intro v hv
    rcases hv with hv | hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  · intro p hp
    simp only [paths, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · refine ⟨dxt1, rfl, ?_, ?_⟩
      · change dxt1.support ∩ (web.source ∪ boundary) =
          {dxt1.start, dxt1.finish}
        rw [support_dxt1]
        ext v
        cases v <;> simp [web, boundary, dxt1]
      · change dxt1.support ∩ web.source = {dxt1.start}
        rw [support_dxt1]
        ext v
        cases v <;> simp [web, dxt1]
    · refine ⟨byPath, rfl, ?_, ?_⟩
      · change byPath.support ∩ (web.source ∪ boundary) =
          {byPath.start, byPath.finish}
        rw [support_byPath]
        ext v
        cases v <;> simp [web, boundary, byPath]
      · change byPath.support ∩ web.source = {byPath.start}
        rw [support_byPath]
        ext v
        cases v <;> simp [web, byPath]

theorem boundary_trimmed : IsTrimmedSeparator web boundary := by
  apply Set.Subset.antisymm (web.essential_subset boundary)
  intro v hv
  change v ∈ ({d, t1, y} : Set Vertex) at hv
  rcases hv with rfl | hv
  · rw [web.mem_essential_iff]
    refine ⟨by simp [boundary], ?_⟩
    rw [web.not_mem_roof_iff]
    refine ⟨dwt2, ⟨rfl, by simp [web]⟩, ?_⟩
    change Disjoint dwt2.support (boundary \ {d})
    rw [support_dwt2]
    apply Set.disjoint_left.2
    intro v hv₁ hv₂
    cases v <;> simp [boundary] at *
  · rcases hv with rfl | hv
    · exact target_mem_essential (by simp [web]) (by simp [boundary])
    · have : v = y := by simpa using hv
      subst v
      rw [web.mem_essential_iff]
      refine ⟨by simp [boundary], ?_⟩
      rw [web.not_mem_roof_iff]
      refine ⟨yxr, ⟨rfl, by simp [web]⟩, ?_⟩
      change Disjoint yxr.support (boundary \ {y})
      rw [support_yxr]
      apply Set.disjoint_left.2
      intro v hv₁ hv₂
      cases v <;> simp [boundary] at *

theorem targetPathFrom_b_meets_boundary
    (p : FinitePath web.graph) (hp : web.IsTargetPathFrom b p) :
    web.Meets p boundary := by
  rcases p with ⟨s, t, walk, hpath⟩
  change s = b ∧ t ∈ web.target at hp
  have hs : s = b := hp.1
  subst s
  cases walk with
  | nil =>
      have hbt : b ∈ web.target := hp.2
      simpa [web] using hbt
  | @cons _ v _ hadj rest =>
      have hnext : v = y ∨ v = q := by
        change graph.Adj b v at hadj
        simpa [graph] using hadj
      rcases hnext with hnext | hnext
      · subst v
        refine ⟨y, ?_, by simp [boundary]⟩
        exact List.mem_cons_of_mem b rest.start_mem_support
      · subst v
        cases rest with
        | nil =>
            have hqt : q ∈ web.target := hp.2
            simpa [web] using hqt
        | @cons _ v _ hadj' rest' =>
            have hnext' : v = t1 := by
              change graph.Adj q v at hadj'
              simpa [graph] using hadj'
            subst v
            refine ⟨t1, ?_, by simp [boundary]⟩
            exact List.mem_cons_of_mem b
              (List.mem_cons_of_mem q rest'.start_mem_support)

theorem boundary_separator :
    IsSeparatorFrom web web.source boundary := by
  intro a ha
  change a ∈ ({d, b} : Set Vertex) at ha
  rcases ha with rfl | ha
  · exact web.subset_roof boundary (by simp [boundary])
  · have hab : a = b := by simpa using ha
    subst a
    intro p hp
    exact targetPathFrom_b_meets_boundary p hp

/-- The corrected boundary is literally inclusion-minimal, not merely
trimmed.  The three indispensable points are witnessed by `d-w-t2`,
`b-q-t1`, and `b-y-x-r`, respectively. -/
theorem boundary_minimal :
    IsMinimalSeparatorFrom web web.source boundary := by
  rw [IsMinimalSeparatorFrom.iff_separator_and_singleton_deletions]
  refine ⟨boundary_separator, ?_⟩
  intro c hc hsep
  change c ∈ ({d, t1, y} : Set Vertex) at hc
  rcases hc with rfl | hc
  · have hnroof : d ∉ web.roof (boundary \ {d}) := by
      rw [web.not_mem_roof_iff]
      refine ⟨dwt2, ⟨rfl, by simp [web]⟩, ?_⟩
      change Disjoint dwt2.support (boundary \ {d})
      rw [support_dwt2]
      exact Set.disjoint_left.2 (by
        intro v hvp hvC
        cases v <;> simp [boundary] at hvp hvC)
    exact hnroof (hsep (by simp [web]))
  · rcases hc with rfl | hc
    · have hnroof : b ∉ web.roof (boundary \ {t1}) := by
        rw [web.not_mem_roof_iff]
        refine ⟨bqt1, ⟨rfl, by simp [web]⟩, ?_⟩
        change Disjoint bqt1.support (boundary \ {t1})
        rw [support_bqt1]
        exact Set.disjoint_left.2 (by
          intro v hvp hvC
          cases v <;> simp [boundary] at hvp hvC)
      exact hnroof (hsep (by simp [web]))

    · have hcy : c = y := by simpa using hc
      subst c
      have hnroof : b ∉ web.roof (boundary \ {y}) := by
        rw [web.not_mem_roof_iff]
        refine ⟨byxr, ⟨rfl, by simp [web]⟩, ?_⟩
        change Disjoint byxr.support (boundary \ {y})
        rw [support_byxr]
        exact Set.disjoint_left.2 (by
          intro v hvp hvC
          cases v <;> simp [boundary] at hvp hvC)
      exact hnroof (hsep (by simp [web]))

/-- The completed `d` component and the only continuation of the displayed
pending prefix `b -> y` meet at `x`. -/
theorem completed_continuation_not_disjoint :
    ¬ Disjoint dxt1.support yxr.support := by
  rw [support_dxt1, support_yxr]
  intro hdis
  exact Set.disjoint_left.1 hdis
    (show x ∈ ({d, x, t1} : Set Vertex) by simp)
    (show x ∈ ({y, x, r} : Set Vertex) by simp)

/-- Every target path which extends the displayed prefix `b -> y` must use
the crossing vertex `x`. -/
theorem x_mem_of_byPath_prefix_of_target
    (f : FinitePath web.graph) (hprefix : byPath.IsPrefixOf f)
    (htarget : f.finish ∈ web.target) : x ∈ f.support := by
  rcases f with ⟨s, t, walk, hpath⟩
  change [b, y] <+: walk.support at hprefix
  cases walk with
  | nil =>
      simp only [Walk.support_nil] at hprefix
      have hlen := List.IsPrefix.length_le hprefix
      simp at hlen
  | cons hadj rest =>
      have h0 := hprefix.getElem (i := 0) (by simp)
      simp only [Walk.support_cons, List.getElem_cons_zero] at h0
      subst_vars
      cases rest with
      | nil =>
          simp only [Walk.support_cons, Walk.support_nil] at hprefix
          have h1 := hprefix.getElem (i := 1) (by simp)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h1
          subst_vars
          have : y ∈ web.target := htarget
          simpa [web] using this
      | cons hadj' rest' =>
          simp only [Walk.support_cons] at hprefix
          have h1 := hprefix.getElem (i := 1) (by simp)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h1
          subst_vars
          simp [web, graph] at hadj'
          subst_vars
          change x ∈ (Walk.cons hadj (Walk.cons hadj' rest')).support
          simp

/-- No warp can be both a forward extension of the displayed row and a
target-linkage for the newly exposed source `b`.  The old completed member
forces `x` onto one new component, while extension of `b -> y` and target
linking force `x` onto the other. -/
theorem no_forward_warp_links_b :
    ¬ ∃ T : Set web.DPath,
      web.IsWarp T ∧ web.ForwardExtension paths T ∧
        LinksToTarget web T {b} := by
  rintro ⟨T, hwarp, hforward, hlinks⟩
  obtain ⟨pd, hpdT, hpdext⟩ := hforward.1 (.inl dxt1) (by simp [paths])
  obtain ⟨pb, hpbT, f, rfl, hfpure, before, after, hsupport,
    z, hzTarget, hzAfter⟩ := hlinks b (by simp)
  have hbSupport : b ∈ f.support := by
    have hbInter : b ∈ f.support ∩ ({b} : Set Vertex) := by
      rw [hfpure]
      simp
    exact hbInter.1
  have hfStart : f.start = b :=
    (web_normalized.eq_initial_of_mem_path (.inl f) hbSupport
      (by simp [web])).symm
  obtain ⟨pold, hpold, hpoldext⟩ := hforward.2 (.inl f) hpbT
  have hprefix : byPath.IsPrefixOf f := by
    simp only [paths, Set.mem_insert_iff, Set.mem_singleton_iff] at hpold
    rcases hpold with rfl | rfl
    · have hdb : d = b := by
        have hinit := web.extends_initial hpoldext
        change d = f.start at hinit
        exact hinit.trans hfStart
      exact Vertex.noConfusion hdb
    · exact hpoldext
  have hzSupport : z ∈ f.support := by
    change z ∈ f.walk.support
    rw [hsupport]
    exact List.mem_append_right before hzAfter
  have hfTerminal : web.terminal? (.inl f : web.DPath) = some z :=
    web_normalized.terminal?_eq_of_mem_path (.inl f) hzSupport hzTarget
  have hfFinish : f.finish = z := by
    simpa only [web.terminal?_finite, Option.some.injEq] using hfTerminal
  have hxF : x ∈ f.support :=
    x_mem_of_byPath_prefix_of_target f hprefix (hfFinish ▸ hzTarget)
  have hxPd : x ∈ pd.support :=
    web.support_mono_of_extends hpdext (by
      change x ∈ dxt1.support
      rw [support_dxt1]
      simp)
  have hne : pd ≠ (.inl f : web.DPath) := by
    intro heq
    have hdb : d = b := by
      have hinit := web.extends_initial hpdext
      have heqinit := congrArg
        (fun p : web.DPath => DirectedPath.Path.initial p) heq
      change d = DirectedPath.Path.initial pd at hinit
      change DirectedPath.Path.initial pd = f.start at heqinit
      exact hinit.trans (heqinit.trans hfStart)
    exact Vertex.noConfusion hdb
  exact Set.disjoint_left.1 (hwarp hpdT hpbT hne) hxPd hxF

/-- Literal minimality, endpoint-pure full source coverage, and normalization
still do not imply the crossing-disjointness required by the singular
successor splice. -/
theorem exactMinimal_crossing_obstruction :
    web.IsNormalized ∧
      IsLinkageBetween web web.source boundary paths ∧
      IsMinimalSeparatorFrom web web.source boundary ∧
      ¬ Disjoint dxt1.support yxr.support :=
  ⟨web_normalized, paths_linkage, boundary_minimal,
    completed_continuation_not_disjoint⟩

#print axioms paths_not_isWave

end SingularSafeBatchCounterexample
end CardinalInduction
end Erdos599
