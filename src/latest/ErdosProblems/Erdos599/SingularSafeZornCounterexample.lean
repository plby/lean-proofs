/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeZornReduction
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# Literal safe-linkage chains need not have literal safe upper bounds

This countable web exhibits the limit failure isolated by
`SingularSafeZornReduction`.  For every `n`, choose the first `n` paths
`a_i -> x_i`.  Deleting their carriers is safe: every unchosen `a_j` has
the private route `a_j -> s_j`, and `b` still has the route `b -> x_n`.
At the union, however, every `x_i` has been deleted and the surviving source
`b` is stranded.

The paths form a literal inclusion chain of ambiently safe candidates, but
their union is not safe.  Moreover no literal safe upper candidate exists:
any additional path starts at some `a_i` and meets the already retained path
there.  Hence a successful maximal construction must reroute at limit stages;
ordinary Zorn on literal path inclusion cannot prove the batch selector.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeZornCounterexample

open DirectedPath
open SingularSafeZornReduction

inductive Vertex
  | b
  | a (i : Nat)
  | x (i : Nat)
  | s (i : Nat)
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj u v :=
    (∃ i, u = a i ∧ v = x i) ∨
    (∃ i, u = a i ∧ v = s i) ∨
    (∃ i, u = b ∧ v = x i)

@[simp] theorem graph_adj (u v : Vertex) :
    graph.Adj u v ↔
      (∃ i, u = a i ∧ v = x i) ∨
      (∃ i, u = a i ∧ v = s i) ∨
      (∃ i, u = b ∧ v = x i) :=
  Iff.rfl

def web : DWeb Vertex where
  graph := graph
  source := {b} ∪ Set.range a
  target := Set.range x ∪ Set.range s

def requested : Set Vertex := Set.range a

def covered (n : Nat) : Set Vertex :=
  {v | ∃ i < n, v = a i}

def badPath (i : Nat) : FinitePath graph where
  start := a i
  finish := x i
  walk := Walk.cons (u := a i) (v := x i) (w := x i)
    (by simp [graph]) Walk.nil
  isPath := by
    change [a i, x i].Nodup
    simp

def privatePath (i : Nat) : FinitePath graph where
  start := a i
  finish := s i
  walk := Walk.cons (u := a i) (v := s i) (w := s i)
    (by simp [graph]) Walk.nil
  isPath := by
    change [a i, s i].Nodup
    simp

def bPath (i : Nat) : FinitePath graph where
  start := b
  finish := x i
  walk := Walk.cons (u := b) (v := x i) (w := x i)
    (by simp [graph]) Walk.nil
  isPath := by
    change [b, x i].Nodup
    simp

def paths (n : Nat) : Set web.DPath :=
  {p | ∃ i < n, p = (.inl (badPath i) : web.DPath)}

@[simp] theorem support_badPath (i : Nat) :
    (badPath i).support = ({a i, x i} : Set Vertex) := by
  ext v
  change v ∈ [a i, x i] ↔ _
  simp

@[simp] theorem support_privatePath (i : Nat) :
    (privatePath i).support = ({a i, s i} : Set Vertex) := by
  ext v
  change v ∈ [a i, s i] ↔ _
  simp

@[simp] theorem support_bPath (i : Nat) :
    (bPath i).support = ({b, x i} : Set Vertex) := by
  ext v
  change v ∈ [b, x i] ↔ _
  simp

theorem web_normalized : web.IsNormalized := by
  intro u v huv
  change graph.Adj u v at huv
  simp only [graph_adj] at huv
  rcases huv with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
  all_goals simp [web]

theorem requested_subset_source : requested ⊆ web.source := by
  rintro v ⟨i, rfl⟩
  exact Or.inr ⟨i, rfl⟩

theorem paths_mono : Monotone paths := by
  intro m n hmn p hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, hi.trans_le hmn, rfl⟩

theorem paths_isWarp (n : Nat) : web.IsWarp (paths n) := by
  intro p hp q hq hpq
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨j, hj, rfl⟩ := hq
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hpq rfl
  change Disjoint (badPath i).support (badPath j).support
  rw [support_badPath, support_badPath]
  apply Set.disjoint_left.2
  intro v hvi hvj
  rcases v <;> simp_all

theorem paths_finiteCharacter (n : Nat) :
    web.HasFiniteCharacter (paths n) := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨badPath i, rfl⟩

@[simp] theorem paths_initialSet (n : Nat) :
    web.initialSet (paths n) = covered n := by
  ext v
  constructor
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨i, hi, rfl⟩ := hp
    change a i = v at hpv
    exact ⟨i, hi, hpv.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨.inl (badPath i), ⟨i, hi, rfl⟩, rfl⟩

theorem paths_linkage (n : Nat) :
    IsLinkageBetween web (covered n) web.target (paths n) := by
  refine ⟨paths_isWarp n, paths_finiteCharacter n,
    paths_initialSet n, ?_, ?_⟩
  · rintro v ⟨p, hp, hpv⟩
    obtain ⟨i, hi, rfl⟩ := hp
    change (some (x i) : Option Vertex) = some v at hpv
    have hv : v = x i := (Option.some.inj hpv).symm
    subst v
    exact Or.inl ⟨i, rfl⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := hp
    refine ⟨badPath i, rfl, ?_, ?_⟩
    · change (badPath i).support ∩ (covered n ∪ web.target) =
        {(badPath i).start, (badPath i).finish}
      rw [support_badPath]
      ext v
      rcases v with (_ | j | j | j) <;>
        simp_all [covered, web, badPath]
    · change (badPath i).support ∩ covered n = {(badPath i).start}
      rw [support_badPath]
      ext v
      rcases v with (_ | j | j | j) <;>
        simp_all [covered, badPath]

/-- Exact carrier membership for a finite stage. -/
theorem mem_vertexSet_paths_iff (n : Nat) (v : Vertex) :
    v ∈ web.vertexSet (paths n) ↔
      ∃ i < n, v = a i ∨ v = x i := by
  constructor
  · rintro ⟨p, hp, hvp⟩
    obtain ⟨i, hi, rfl⟩ := hp
    change v ∈ (badPath i).support at hvp
    rw [support_badPath] at hvp
    exact ⟨i, hi, hvp⟩
  · rintro ⟨i, hi, hv⟩
    refine ⟨.inl (badPath i), ⟨i, hi, rfl⟩, ?_⟩
    change v ∈ (badPath i).support
    rw [support_badPath]
    exact hv

theorem covered_subset_requested (n : Nat) : covered n ⊆ requested := by
  rintro v ⟨i, hi, rfl⟩
  exact ⟨i, rfl⟩

private theorem a_not_mem_vertexSet_paths_of_le
    {n j : Nat} (hjn : n ≤ j) : a j ∉ web.vertexSet (paths n) := by
  rw [mem_vertexSet_paths_iff]
  rintro ⟨i, hi, hai | hxi⟩
  · injection hai with hji
    omega
  · exact Vertex.noConfusion hxi

private theorem x_not_mem_vertexSet_paths_of_le
    {n j : Nat} (hjn : n ≤ j) : x j ∉ web.vertexSet (paths n) := by
  rw [mem_vertexSet_paths_iff]
  rintro ⟨i, hi, hai | hxi⟩
  · exact Vertex.noConfusion hai
  · injection hxi with hji
    omega

private theorem s_not_mem_vertexSet_paths
    {n j : Nat} : s j ∉ web.vertexSet (paths n) := by
  rw [mem_vertexSet_paths_iff]
  rintro ⟨i, hi, hai | hxi⟩
  · exact Vertex.noConfusion hai
  · exact Vertex.noConfusion hxi

private theorem b_not_mem_vertexSet_paths
    {n : Nat} : b ∉ web.vertexSet (paths n) := by
  rw [mem_vertexSet_paths_iff]
  rintro ⟨i, hi, hai | hxi⟩
  · exact Vertex.noConfusion hai
  · exact Vertex.noConfusion hxi

/-- The private route of an unprocessed source, viewed in the finite-stage
residual. -/
def residualPrivatePath (n j : Nat) (hjn : n ≤ j) :
    FinitePath (web.delete (web.vertexSet (paths n))).graph where
  start := a j
  finish := s j
  walk := Walk.cons (u := a j) (v := s j) (w := s j)
    ⟨Or.inr (Or.inl ⟨j, rfl, rfl⟩), a_not_mem_vertexSet_paths_of_le hjn,
      s_not_mem_vertexSet_paths⟩ Walk.nil
  isPath := by
    change [a j, s j].Nodup
    simp

/-- At stage `n`, the route through `x_n` is still available to `b`. -/
def residualBPath (n : Nat) :
    FinitePath (web.delete (web.vertexSet (paths n))).graph where
  start := b
  finish := x n
  walk := Walk.cons (u := b) (v := x n) (w := x n)
    ⟨Or.inr (Or.inr ⟨n, rfl, rfl⟩), b_not_mem_vertexSet_paths,
      x_not_mem_vertexSet_paths_of_le (le_refl n)⟩ Walk.nil
  isPath := by
    change [b, x n].Nodup
    simp

@[simp] theorem support_residualPrivatePath (n j : Nat) (hjn : n ≤ j) :
    (residualPrivatePath n j hjn).support = ({a j, s j} : Set Vertex) := by
  ext v
  change v ∈ [a j, s j] ↔ _
  simp

@[simp] theorem support_residualBPath (n : Nat) :
    (residualBPath n).support = ({b, x n} : Set Vertex) := by
  ext v
  change v ∈ [b, x n] ↔ _
  simp

private def reachA (i : Nat) : Set Vertex := {a i, x i, s i}

private def reachB : Set Vertex := {b} ∪ Set.range x

private theorem reachA_step {n i : Nat} {u v : Vertex}
    (hu : u ∈ reachA i)
    (huv : (web.delete (web.vertexSet (paths n))).graph.Adj u v) :
    v ∈ reachA i := by
  have huv' : graph.Adj u v := huv.1
  simp only [graph_adj] at huv'
  rcases huv' with ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  all_goals simp_all [reachA]

private theorem reachB_step {n : Nat} {u v : Vertex}
    (hu : u ∈ reachB)
    (huv : (web.delete (web.vertexSet (paths n))).graph.Adj u v) :
    v ∈ reachB := by
  have huv' : graph.Adj u v := huv.1
  simp only [graph_adj] at huv'
  rcases huv' with ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  all_goals simp_all [reachB]

private theorem walk_preserves_reachA {n i : Nat} {u v : Vertex}
    (p : Walk (web.delete (web.vertexSet (paths n))).graph u v)
    (hu : u ∈ reachA i) : v ∈ reachA i := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih => exact ih (reachA_step hu hab)

private theorem walk_preserves_reachB {n : Nat} {u v : Vertex}
    (p : Walk (web.delete (web.vertexSet (paths n))).graph u v)
    (hu : u ∈ reachB) : v ∈ reachB := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih => exact ih (reachB_step hu hab)

private theorem finite_start_eq_a_of_finish_s
    {n j : Nat}
    (f : FinitePath (web.delete (web.vertexSet (paths n))).graph)
    (hstart : f.start ∈ (web.delete (web.vertexSet (paths n))).source)
    (hfinish : f.finish = s j) : f.start = a j := by
  have hsource : f.start ∈ web.source := hstart.1
  change f.start ∈ ({b} ∪ Set.range a : Set Vertex) at hsource
  rcases hsource with hb | ⟨i, hai⟩
  · have hbeq : f.start = b := by simpa using hb
    have hsReach : f.finish ∈ reachB :=
      walk_preserves_reachB f.walk (by simp [hbeq, reachB])
    rw [hfinish] at hsReach
    simpa [reachB] using hsReach
  · have hreach : f.finish ∈ reachA i :=
      walk_preserves_reachA f.walk (by simp [hai, reachA])
    rw [hfinish] at hreach
    have hji : j = i := by simpa [reachA] using hreach
    exact hai.symm.trans (congrArg a hji.symm)

private theorem finite_start_eq_b_or_a_of_finish_x
    {n j : Nat}
    (f : FinitePath (web.delete (web.vertexSet (paths n))).graph)
    (hstart : f.start ∈ (web.delete (web.vertexSet (paths n))).source)
    (hfinish : f.finish = x j) : f.start = b ∨ f.start = a j := by
  have hsource : f.start ∈ web.source := hstart.1
  change f.start ∈ ({b} ∪ Set.range a : Set Vertex) at hsource
  rcases hsource with hb | ⟨i, hai⟩
  · exact Or.inl (by simpa using hb)
  · right
    have hreach : f.finish ∈ reachA i :=
      walk_preserves_reachA f.walk (by simp [hai, reachA])
    rw [hfinish] at hreach
    have hji : j = i := by simpa [reachA] using hreach
    exact hai.symm.trans (congrArg a hji.symm)

private theorem residual_normalized (n : Nat) :
    (web.delete (web.vertexSet (paths n))).IsNormalized := by
  intro u v huv
  refine ⟨?_, ?_⟩
  · intro hvSource
    exact (web_normalized huv.1).1 hvSource.1
  · intro huTarget
    exact (web_normalized huv.1).2 huTarget.1

/-- A wave in a finite-stage residual has a member starting at every
unprocessed `a_j`, and that member has its terminal on the private two-point
route. -/
private theorem exists_private_wave_member
    {n j : Nat} (hjn : n ≤ j)
    (W : Set (web.delete (web.vertexSet (paths n))).DPath)
    (hW : (web.delete (web.vertexSet (paths n))).IsWave W) :
    ∃ f : FinitePath (web.delete (web.vertexSet (paths n))).graph,
      (.inl f : (web.delete (web.vertexSet (paths n))).DPath) ∈ W ∧
        f.start = a j ∧ (f.finish = a j ∨ f.finish = s j) := by
  let H := web.delete (web.vertexSet (paths n))
  have haSource : a j ∈ H.source := by
    exact ⟨Or.inr ⟨j, rfl⟩, a_not_mem_vertexSet_paths_of_le hjn⟩
  let q := residualPrivatePath n j hjn
  have hqTarget : H.IsTargetPathFrom (a j) q := by
    refine ⟨rfl, ?_⟩
    exact ⟨Or.inr ⟨j, rfl⟩, s_not_mem_vertexSet_paths⟩
  obtain ⟨z, hzq, hzFrontier⟩ := hW.2.2 haSource q hqTarget
  obtain ⟨p, hpW, hpz⟩ := hzFrontier
  rcases p with f | ray
  · have hfinish : f.finish = z := Option.some.inj hpz
    have hzSupport : z = a j ∨ z = s j := by
      have hzq' : z ∈ ({a j, s j} : Set Vertex) := by
        simpa only [q, support_residualPrivatePath] using hzq
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzq'
    have hfSource : f.start ∈ H.source :=
      hW.2.1 ⟨.inl f, hpW, rfl⟩
    have hfStart : f.start = a j := by
      rcases hzSupport with hza | hzs
      · have haSupport : a j ∈ f.support := by
          rw [← hza, ← hfinish]
          exact f.finish_mem_support
        exact (DWeb.IsNormalized.eq_initial_of_mem_path
          (residual_normalized n) (.inl f) haSupport haSource).symm
      · exact finite_start_eq_a_of_finish_s f hfSource
          (hfinish.trans hzs)
    refine ⟨f, hpW, hfStart, ?_⟩
    exact hzSupport.imp (hfinish.trans) (hfinish.trans)
  · simp at hpz

private theorem exists_wave_member_starting_b
    (n : Nat)
    (W : Set (web.delete (web.vertexSet (paths n))).DPath)
    (hW : (web.delete (web.vertexSet (paths n))).IsWave W) :
    ∃ f : FinitePath (web.delete (web.vertexSet (paths n))).graph,
      (.inl f : (web.delete (web.vertexSet (paths n))).DPath) ∈ W ∧
        f.start = b := by
  let H := web.delete (web.vertexSet (paths n))
  have hbSource : b ∈ H.source := by
    exact ⟨Or.inl (Set.mem_singleton b), b_not_mem_vertexSet_paths⟩
  let q := residualBPath n
  have hqTarget : H.IsTargetPathFrom b q := by
    refine ⟨rfl, ?_⟩
    exact ⟨Or.inl ⟨n, rfl⟩,
      x_not_mem_vertexSet_paths_of_le (le_refl n)⟩
  obtain ⟨z, hzq, hzFrontier⟩ := hW.2.2 hbSource q hqTarget
  obtain ⟨p, hpW, hpz⟩ := hzFrontier
  rcases p with f | ray
  · have hfinish : f.finish = z := Option.some.inj hpz
    have hzSupport : z = b ∨ z = x n := by
      have hzq' : z ∈ ({b, x n} : Set Vertex) := by
        simpa only [q, support_residualBPath] using hzq
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzq'
    have hfSource : f.start ∈ H.source :=
      hW.2.1 ⟨.inl f, hpW, rfl⟩
    rcases hzSupport with hzb | hzx
    · have hbSupport : b ∈ f.support := by
        rw [← hzb, ← hfinish]
        exact f.finish_mem_support
      have hfStart : f.start = b :=
        (DWeb.IsNormalized.eq_initial_of_mem_path
          (residual_normalized n) (.inl f) hbSupport hbSource).symm
      exact ⟨f, hpW, hfStart⟩
    · rcases finite_start_eq_b_or_a_of_finish_x f hfSource
          (hfinish.trans hzx) with hfb | hfa
      · exact ⟨f, hpW, hfb⟩
      · obtain ⟨g, hgW, hga, hgfinish⟩ :=
          exists_private_wave_member (n := n) (j := n) (le_refl n) W hW
        by_cases hfg : (.inl f : H.DPath) = .inl g
        · have hfg' : f = g := Sum.inl.inj hfg
          subst g
          rcases hgfinish with hgaFinish | hgsFinish
          · have : x n = a n := (hfinish.trans hzx).symm.trans hgaFinish
            exact Vertex.noConfusion this
          · have : x n = s n := (hfinish.trans hzx).symm.trans hgsFinish
            exact Vertex.noConfusion this
        · have hdis := hW.1 hpW hgW hfg
          have hfaSupport : a n ∈ f.support :=
            hfa.symm ▸ f.start_mem_support
          have hgaSupport : a n ∈ g.support :=
            hga.symm ▸ g.start_mem_support
          exact (Set.disjoint_left.1 hdis hfaSupport hgaSupport).elim
  · simp at hpz

/-- Every finite-stage residual is unhindered. -/
theorem delete_paths_isUnhindered (n : Nat) :
    (web.delete (web.vertexSet (paths n))).IsUnhindered := by
  let H := web.delete (web.vertexSet (paths n))
  rw [H.isUnhindered_iff]
  intro W hW
  apply Set.Subset.antisymm hW.2.1
  intro v hvSource
  have hvWeb : v ∈ web.source := hvSource.1
  change v ∈ ({b} ∪ Set.range a : Set Vertex) at hvWeb
  rcases hvWeb with hvb | ⟨j, hvj⟩
  · have hvb' : v = b := by simpa using hvb
    obtain ⟨f, hfW, hfb⟩ := exists_wave_member_starting_b n W hW
    exact ⟨.inl f, hfW, hfb.trans hvb'.symm⟩
  · subst v
    have hjn : n ≤ j := by
      by_contra hnj
      apply hvSource.2
      rw [mem_vertexSet_paths_iff]
      exact ⟨j, Nat.lt_of_not_ge hnj, Or.inl rfl⟩
    obtain ⟨f, hfW, hfa, -⟩ :=
      exists_private_wave_member hjn W hW
    exact ⟨.inl f, hfW, hfa⟩

/-- Each finite stage is an ambiently safe candidate for the requested set. -/
theorem paths_isSafeCandidate (n : Nat) :
    IsSafeCandidate web requested (paths n) := by
  refine ⟨?_, ?_, delete_paths_isUnhindered n⟩
  · rw [paths_initialSet]
    exact covered_subset_requested n
  · rw [paths_initialSet]
    exact paths_linkage n

/-- The literal union of the finite stages. -/
def limitPaths : Set web.DPath := ⋃ n, paths n

theorem mem_limitPaths_iff (p : web.DPath) :
    p ∈ limitPaths ↔ ∃ i, p = (.inl (badPath i) : web.DPath) := by
  constructor
  · intro hp
    obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 hp
    obtain ⟨i, hi, hpi⟩ := hpn
    exact ⟨i, hpi⟩
  · rintro ⟨i, rfl⟩
    apply Set.mem_iUnion.2
    exact ⟨i + 1, i, Nat.lt_succ_self i, rfl⟩

theorem mem_vertexSet_limitPaths_iff (v : Vertex) :
    v ∈ web.vertexSet limitPaths ↔
      ∃ i, v = a i ∨ v = x i := by
  constructor
  · rintro ⟨p, hp, hvp⟩
    obtain ⟨i, rfl⟩ := (mem_limitPaths_iff p).mp hp
    change v ∈ (badPath i).support at hvp
    rw [support_badPath] at hvp
    exact ⟨i, hvp⟩
  · rintro ⟨i, hv⟩
    refine ⟨.inl (badPath i), (mem_limitPaths_iff _).2 ⟨i, rfl⟩, ?_⟩
    change v ∈ (badPath i).support
    rw [support_badPath]
    exact hv

theorem b_not_reachable_after_limit :
    b ∉ (web.delete (web.vertexSet limitPaths)).reachableToTarget := by
  rintro ⟨p, hp⟩
  rcases p with ⟨u, v, walk, hpath⟩
  change u = b ∧ v ∈ (web.delete (web.vertexSet limitPaths)).target at hp
  have hu : u = b := hp.1
  subst u
  cases walk with
  | nil =>
      have hbTarget : b ∈ web.target := hp.2.1
      simpa [web] using hbTarget
  | @cons _ y _ hby rest =>
      have hbyGraph : graph.Adj b y := hby.1
      have hy : ∃ i, y = x i := by
        simpa [graph] using hbyGraph
      obtain ⟨i, rfl⟩ := hy
      exact hby.2.2 ((mem_vertexSet_limitPaths_iff (x i)).2
        ⟨i, Or.inr rfl⟩)

/-- The omega-union deletion is hindered: `b` survives but has no target
path. -/
theorem delete_limitPaths_isHindered :
    (web.delete (web.vertexSet limitPaths)).IsHindered := by
  apply (web.delete (web.vertexSet limitPaths)).exists_hindrance_of_source_not_subset_reachableToTarget
  apply Set.not_subset.mpr
  refine ⟨b, ?_, b_not_reachable_after_limit⟩
  refine ⟨Or.inl (Set.mem_singleton b), ?_⟩
  rw [mem_vertexSet_limitPaths_iff]
  rintro ⟨i, hai | hxi⟩
  · exact Vertex.noConfusion hai
  · exact Vertex.noConfusion hxi

theorem web_unhindered : web.IsUnhindered := by
  have hp0 : paths 0 = ∅ := by
    ext p
    simp [paths]
  have hv0 : web.vertexSet (paths 0) = ∅ := by
    rw [hp0]
    ext v
    simp [DWeb.vertexSet]
  have h0 := delete_paths_isUnhindered 0
  rw [hv0, web.delete_empty] at h0
  exact h0

/-- The finite path families form a chain of safe candidates. -/
def candidateChain : Set (Set web.DPath) := Set.range paths

theorem candidateChain_subset :
    candidateChain ⊆ {P | IsSafeCandidate web requested P} := by
  rintro P ⟨n, rfl⟩
  exact paths_isSafeCandidate n

theorem candidateChain_isChain : IsChain (· ⊆ ·) candidateChain := by
  rintro P ⟨m, rfl⟩ Q ⟨n, rfl⟩ hne
  rcases le_total m n with hmn | hnm
  · exact Or.inl (paths_mono hmn)
  · exact Or.inr (paths_mono hnm)

theorem sUnion_candidateChain : ⋃₀ candidateChain = limitPaths := by
  ext p
  constructor
  · rintro ⟨P, ⟨n, rfl⟩, hp⟩
    exact Set.mem_iUnion.2 ⟨n, hp⟩
  · intro hp
    obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 hp
    exact ⟨paths n, ⟨n, rfl⟩, hpn⟩

/-- Any candidate containing every finite stage would have to equal the bad
literal union: a further path starts at some `a_i` and collides with the
already retained `a_i -> x_i`. -/
theorem candidate_eq_limit_of_upper
    {U : Set web.DPath} (hU : IsSafeCandidate web requested U)
    (hupper : ∀ P ∈ candidateChain, P ⊆ U) :
    U = limitPaths := by
  apply Set.Subset.antisymm
  · intro q hqU
    have hqInitial : q.initial ∈ web.initialSet U := ⟨q, hqU, rfl⟩
    obtain ⟨i, hai⟩ := hU.1 hqInitial
    have hbadStage : paths (i + 1) ∈ candidateChain := ⟨i + 1, rfl⟩
    have hbad : (.inl (badPath i) : web.DPath) ∈ U :=
      hupper _ hbadStage ⟨i, Nat.lt_succ_self i, rfl⟩
    by_cases hq : q = (.inl (badPath i) : web.DPath)
    · exact (mem_limitPaths_iff q).2 ⟨i, hq⟩
    · have hdis := hU.2.1.isWarp hqU hbad hq
      have hqa : a i ∈ q.support := by
        rw [hai]
        exact q.initial_mem_support
      have hbadA : a i ∈ (badPath i).support := by
        rw [support_badPath]
        simp
      exact False.elim (Set.disjoint_left.1 hdis hqa hbadA)
  · intro p hp
    obtain ⟨i, rfl⟩ := (mem_limitPaths_iff p).1 hp
    exact hupper (paths (i + 1)) ⟨i + 1, rfl⟩
      ⟨i, Nat.lt_succ_self i, rfl⟩

/-- The safe candidate chain has no upper bound in the literal-inclusion
order. -/
theorem candidateChain_has_no_safe_upper :
    ¬ ∃ U, IsSafeCandidate web requested U ∧
      ∀ P ∈ candidateChain, P ⊆ U := by
  rintro ⟨U, hU, hupper⟩
  have hEq : U = limitPaths := candidate_eq_limit_of_upper hU hupper
  exact hU.2.2 (hEq ▸ delete_limitPaths_isHindered)

/-- Consequently the literal-inclusion Zorn premise itself is false, even
for a normalized unhindered countable web and a countable requested set. -/
theorem not_safeCandidateChainUpperBounds :
    ¬ SafeCandidateChainUpperBounds web requested := by
  intro hchain
  obtain ⟨U, hU, hupper⟩ :=
    hchain candidateChain candidateChain_subset candidateChain_isChain
  exact candidateChain_has_no_safe_upper ⟨U, hU, hupper⟩

/-- The still more specific literal-union continuity premise also fails. -/
theorem not_safeChainUnionResidualContinuity :
    ¬ SafeChainUnionResidualContinuity web requested := by
  intro hcontinuity
  have hsafe := hcontinuity candidateChain candidateChain_subset
    candidateChain_isChain
  rw [sUnion_candidateChain] at hsafe
  exact hsafe delete_limitPaths_isHindered

theorem normalized_unhindered_Zorn_counterexample :
    web.IsNormalized ∧ web.IsUnhindered ∧
      ¬ SafeCandidateChainUpperBounds web requested :=
  ⟨web_normalized, web_unhindered, not_safeCandidateChainUpperBounds⟩

#print axioms normalized_unhindered_Zorn_counterexample
#print axioms not_safeChainUnionResidualContinuity

end SingularSafeZornCounterexample
end CardinalInduction
end Erdos599
