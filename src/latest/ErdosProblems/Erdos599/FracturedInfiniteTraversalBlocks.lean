/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionInfinite
import ErdosProblems.Erdos599.InfiniteTraceOwnerUniqueness

/-!
# Concrete infinite traversal blocks for fractured projection

This file constructs the connector-deleted omega stream attached to an
infinite alternating path in the occurrence-split web.  Consecutive pairs of
links form the finite blocks.  Pairing is important: one of two consecutive
links is forward, and a forward fragment of an occurrence-lifted active path
contains a genuine projected edge.  Thus every block contributes at least
one edge even when the other (expanded-reference) link consists entirely of
contracted connector steps.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath Alternating
open Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

local instance infiniteTraversalDecidableEq : DecidableEq V := Classical.decEq V

namespace InfiniteTraversalFrontend

variable (Z : FracturedWarp Gamma)

/-! ## Recombined carriers of literal fractured paths -/

/-- A nonempty connected finite walk whose every edge belongs to a warp is
contained in a single member of that warp. -/
theorem exists_warp_carrier_of_consWalk
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {a b c : V} (e : Gamma.graph.Adj a b)
    (q : Walk Gamma.graph b c)
    (hfamily : (Walk.cons e q).edgeSet ⊆ familyEdges W) :
    ∃ p ∈ W, (Walk.cons e q).edgeSet ⊆ p.edgeSet := by
  induction q generalizing a with
  | @nil b₀ =>
      have heFamily : (a, b₀) ∈ familyEdges W := by
        apply hfamily
        simp [Walk.edgeSet]
      simp only [familyEdges, Set.mem_iUnion] at heFamily
      rcases heFamily with ⟨p, hpW, hep⟩
      exact ⟨p, hpW, by simpa [Walk.edgeSet] using hep⟩
  | @cons b d c f r ih =>
      have htail : (Walk.cons f r).edgeSet ⊆ familyEdges W := by
        intro g hg
        apply hfamily
        simp only [Walk.edgeSet_cons, Set.mem_insert_iff]
        exact Or.inr hg
      obtain ⟨p, hpW, hp⟩ := ih f htail
      have heFamily : (a, b) ∈ familyEdges W := by
        apply hfamily
        simp [Walk.edgeSet]
      simp only [familyEdges, Set.mem_iUnion] at heFamily
      rcases heFamily with ⟨s, hsW, hes⟩
      have hfb : (b, d) ∈ p.edgeSet := by
        apply hp
        simp [Walk.edgeSet]
      have hsp : s = p :=
        DWeb.IsWarp.eq_of_mem_support hW hsW hpW
          (s.edgeSet_subset_support_prod hes).2
          (p.edgeSet_subset_support_prod hfb).1
      subst s
      refine ⟨p, hpW, ?_⟩
      intro g hg
      simp only [Walk.edgeSet_cons, Set.mem_insert_iff] at hg
      rcases hg with rfl | hg
      · exact hes
      · exact hp hg

/-- Every active literal member is an edge-subpath of a unique recombined
warp member.  Existence is the only part needed to select forward owners. -/
theorem exists_edgeWarp_carrier_of_activePath
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    {p : Gamma.DPath} (hp : p ∈ activePaths Z) :
    ∃ q ∈ Z.edgeWarp, p.edgeSet ⊆ q.edgeSet := by
  obtain ⟨pf, hpf⟩ := hZfinite hp.1
  subst p
  rcases pf with ⟨a, c, w, hw⟩
  cases w with
  | nil =>
      rcases hp.2 with ⟨x, hx, y, hy, hxy⟩
      have hxa : x = a := by
        simpa [Path.support, FinitePath.support, Walk.support] using hx
      have hya : y = a := by
        simpa [Path.support, FinitePath.support, Walk.support] using hy
      exact (hxy (hxa.trans hya.symm)).elim
  | @cons a b c e q =>
      have hfamily : (Walk.cons e q).edgeSet ⊆ familyEdges Z.edgeWarp := by
        rw [← Z.same_edges]
        intro g hg
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inl ⟨a, c, Walk.cons e q, hw⟩, hp.1, hg⟩
      obtain ⟨r, hr, hsub⟩ :=
        exists_warp_carrier_of_consWalk Z.edgeWarp_isWarp e q hfamily
      exact ⟨r, hr, hsub⟩

/-- One noncontracted upstairs edge, retaining its traversal direction. -/
structure TraversalStep where
  edge : Vertex V × Vertex V
  direction : Direction

namespace TraversalStep

def entry (s : TraversalStep (V := V)) : V :=
  match s.direction with
  | .forward => project s.edge.1
  | .backward => project s.edge.2

def exit (s : TraversalStep (V := V)) : V :=
  match s.direction with
  | .forward => project s.edge.2
  | .backward => project s.edge.1

def forward (e : Vertex V × Vertex V) : TraversalStep (V := V) :=
  ⟨e, .forward⟩

def backward (e : Vertex V × Vertex V) : TraversalStep (V := V) :=
  ⟨e, .backward⟩

@[simp] theorem entry_forward (e : Vertex V × Vertex V) :
    (forward e).entry = project e.1 := rfl

@[simp] theorem exit_forward (e : Vertex V × Vertex V) :
    (forward e).exit = project e.2 := rfl

@[simp] theorem entry_backward (e : Vertex V × Vertex V) :
    (backward e).entry = project e.2 := rfl

@[simp] theorem exit_backward (e : Vertex V × Vertex V) :
    (backward e).exit = project e.1 := rfl

end TraversalStep

/-- A list of projected upstairs steps with matching traversal endpoints. -/
inductive TraversalRunsFromTo : V → V → List (TraversalStep (V := V)) → Prop
  | nil (x : V) : TraversalRunsFromTo x x []
  | cons (s : TraversalStep (V := V)) {z : V}
      {q : List (TraversalStep (V := V))}
      (tail : TraversalRunsFromTo s.exit z q) :
      TraversalRunsFromTo s.entry z (s :: q)

namespace TraversalRunsFromTo

theorem append {x y z : V} {q r : List (TraversalStep (V := V))}
    (hq : TraversalRunsFromTo x y q) (hr : TraversalRunsFromTo y z r) :
    TraversalRunsFromTo x z (q ++ r) := by
  induction hq with
  | nil => simpa using hr
  | cons s tail ih => exact .cons s (ih hr)

theorem nonempty_of_ne {x y : V} {q : List (TraversalStep (V := V))}
    (h : TraversalRunsFromTo x y q) (hxy : x ≠ y) : q ≠ [] := by
  intro hnil
  subst q
  cases h
  exact hxy rfl

theorem vertexChain_getLast {x y : V}
    {q : List (TraversalStep (V := V))}
    (h : TraversalRunsFromTo x y q) :
    (x :: q.map TraversalStep.exit).getLast (by simp) = y := by
  induction h with
  | nil => simp
  | cons s tail ih => simpa using ih

/-- The vertex before step `j` in a traversal chain is its entry. -/
theorem vertexChain_get_entry {x y : V}
    {q : List (TraversalStep (V := V))}
    (h : TraversalRunsFromTo x y q) (j : ℕ) (hj : j < q.length) :
    (x :: q.map TraversalStep.exit).get ⟨j, by simp; omega⟩ =
      (q.get ⟨j, hj⟩).entry := by
  induction h generalizing j with
  | nil => simp at hj
  | @cons s z r tail ih =>
      cases j with
      | zero => rfl
      | succ j =>
          have hj' : j < r.length := by simpa using hj
          simpa using ih j hj'

/-- The vertex after step `j` in a traversal chain is its exit. -/
theorem vertexChain_get_exit {x y : V}
    {q : List (TraversalStep (V := V))}
    (_h : TraversalRunsFromTo x y q) (j : ℕ) (hj : j < q.length) :
    (x :: q.map TraversalStep.exit).get ⟨j + 1, by simp; omega⟩ =
      (q.get ⟨j, hj⟩).exit := by
  simp

end TraversalRunsFromTo

/-- Project a directed walk in forward traversal order, deleting connector
edges whose endpoints have equal projection. -/
def forwardSteps : {a b : Vertex V} → Walk (web Gamma Z).graph a b →
    List (TraversalStep (V := V))
  | _, _, .nil => []
  | _, _, @Walk.cons _ _ a b _ h q =>
      if project a = project b then forwardSteps q
      else TraversalStep.forward (a, b) :: forwardSteps q

/-- Project a directed walk against its orientation. -/
def backwardSteps : {a b : Vertex V} → Walk (web Gamma Z).graph a b →
    List (TraversalStep (V := V))
  | _, _, .nil => []
  | _, _, @Walk.cons _ _ a b _ h q =>
      backwardSteps q ++
        if project a = project b then []
        else [TraversalStep.backward (a, b)]

theorem forwardSteps_runs {a b : Vertex V}
    (q : Walk (web Gamma Z).graph a b) :
    TraversalRunsFromTo (project a) (project b) (forwardSteps Z q) := by
  induction q with
  | nil => exact .nil _
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · simpa [forwardSteps, hab] using ih
      · simpa [forwardSteps, hab] using
          (TraversalRunsFromTo.cons (TraversalStep.forward (a, b)) ih)

theorem backwardSteps_runs {a b : Vertex V}
    (q : Walk (web Gamma Z).graph a b) :
    TraversalRunsFromTo (project b) (project a) (backwardSteps Z q) := by
  induction q with
  | nil => exact .nil _
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · simpa [backwardSteps, hab] using ih
      · have hsingle : TraversalRunsFromTo (project b) (project a)
            [TraversalStep.backward (a, b)] := by
          exact TraversalRunsFromTo.cons (TraversalStep.backward (a, b))
            (TraversalRunsFromTo.nil (project a))
        simpa [backwardSteps, hab] using ih.append hsingle

theorem forwardSteps_mem {a b : Vertex V}
    (q : Walk (web Gamma Z).graph a b) {s : TraversalStep (V := V)}
    (hs : s ∈ forwardSteps Z q) :
    s.direction = .forward ∧ s.edge ∈ q.edgeSet ∧
      project s.edge.1 ≠ project s.edge.2 := by
  induction q with
  | nil => simp [forwardSteps] at hs
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · rcases ih (by simpa [forwardSteps, hab] using hs) with
          ⟨hdir, hedge, hne⟩
        exact ⟨hdir, by
          simp only [Walk.edgeSet_cons]
          exact Or.inr hedge, hne⟩
      · simp only [forwardSteps, hab, ↓reduceIte, List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact ⟨rfl, by
            simp only [TraversalStep.forward, Walk.edgeSet_cons]
            exact Or.inl rfl, hab⟩
        · rcases ih hs with ⟨hdir, hedge, hne⟩
          exact ⟨hdir, by
            simp only [Walk.edgeSet_cons]
            exact Or.inr hedge, hne⟩

theorem backwardSteps_mem {a b : Vertex V}
    (q : Walk (web Gamma Z).graph a b) {s : TraversalStep (V := V)}
    (hs : s ∈ backwardSteps Z q) :
    s.direction = .backward ∧ s.edge ∈ q.edgeSet ∧
      project s.edge.1 ≠ project s.edge.2 := by
  induction q with
  | nil => simp [backwardSteps] at hs
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · rcases ih (by simpa [backwardSteps, hab] using hs) with
          ⟨hdir, hedge, hne⟩
        exact ⟨hdir, by
          simp only [Walk.edgeSet_cons]
          exact Or.inr hedge, hne⟩
      · simp only [backwardSteps, hab, ↓reduceIte,
          List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · rcases ih hs with ⟨hdir, hedge, hne⟩
          exact ⟨hdir, by
            simp only [Walk.edgeSet_cons]
            exact Or.inr hedge, hne⟩
        · exact ⟨rfl, by
            simp only [TraversalStep.backward, Walk.edgeSet_cons]
            exact Or.inl rfl, hab⟩

/-- Connector-deleted traversal of one alternating link. -/
def linkSteps (l : Link (web Gamma Z).graph) :
    List (TraversalStep (V := V)) :=
  match l.direction with
  | .forward => forwardSteps Z l.path.walk
  | .backward => backwardSteps Z l.path.walk

theorem linkSteps_runs (l : Link (web Gamma Z).graph) :
    TraversalRunsFromTo (project l.entry) (project l.exit)
      (linkSteps Z l) := by
  cases hdir : l.direction with
  | forward =>
      simpa [linkSteps, Link.entry, Link.exit, hdir] using
        forwardSteps_runs Z l.path.walk
  | backward =>
      simpa [linkSteps, Link.entry, Link.exit, hdir] using
        backwardSteps_runs Z l.path.walk

theorem linkSteps_mem (l : Link (web Gamma Z).graph)
    {s : TraversalStep (V := V)} (hs : s ∈ linkSteps Z l) :
    s.direction = l.direction ∧ s.edge ∈ l.path.edgeSet ∧
      project s.edge.1 ≠ project s.edge.2 := by
  cases hdir : l.direction with
  | forward =>
      rw [linkSteps, hdir] at hs
      simpa only [hdir, FinitePath.edgeSet] using
        forwardSteps_mem Z l.path.walk hs
  | backward =>
      rw [linkSteps, hdir] at hs
      simpa only [hdir, FinitePath.edgeSet] using
        backwardSteps_mem Z l.path.walk hs

/-- The two upstairs links placed in block `n`. -/
def pairLinks (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) :
    List (Link (web Gamma Z).graph) :=
  [R.link (2 * n), R.link (2 * n + 1)]

/-- Connector-deleted signed steps in the `n`th pair of links. -/
def pairSteps (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) :
    List (TraversalStep (V := V)) :=
  linkSteps Z (R.link (2 * n)) ++
    linkSteps Z (R.link (2 * n + 1))

/-- The projected vertex block traversed by a pair of upstairs links. -/
def pairBlock (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) : List V :=
  project (R.link (2 * n)).entry ::
    (pairSteps Z R n).map TraversalStep.exit

theorem pairSteps_runs (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) :
    TraversalRunsFromTo (project (R.link (2 * n)).entry)
      (project (R.link (2 * n + 1)).exit) (pairSteps Z R n) := by
  apply (linkSteps_runs Z (R.link (2 * n))).append
  rw [R.joins (2 * n)]
  exact linkSteps_runs Z (R.link (2 * n + 1))

@[simp] theorem pairBlock_length
    (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) :
    (pairBlock Z R n).length = (pairSteps Z R n).length + 1 := by
  simp [pairBlock]

@[simp] theorem pairBlock_head
    (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) :
    (pairBlock Z R n).head (by simp [pairBlock]) =
      project (R.link (2 * n)).entry := by
  rfl

theorem pairBlock_getLast
    (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) :
    (pairBlock Z R n).getLast (by simp [pairBlock]) =
      project (R.link (2 * n + 1)).exit := by
  exact (pairSteps_runs Z R n).vertexChain_getLast

/-- Pair blocks meet after projection because the upstairs trace joins at
the intervening odd link and then at the next even link. -/
theorem pairBlock_joins (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) :
    (pairBlock Z R n).getLast (by simp [pairBlock]) =
      (pairBlock Z R (n + 1)).head
        (by simp [pairBlock]) := by
  rw [pairBlock_getLast, pairBlock_head]
  have h := congrArg project (R.joins (2 * n + 1))
  simpa only [Nat.mul_add, Nat.mul_one] using h

/-- A forward fragment of an occurrence-lifted active path has different
projected endpoints. -/
theorem project_entry_ne_exit_of_forward
    {R : InfiniteTrace (web Gamma Z).graph} {i : ℕ}
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hdir : (R.link i).direction = .forward) :
    project (R.link i).entry ≠ project (R.link i).exit := by
  intro heq
  have hlink : R.link i ∈ (AltPath.infinite R).links := ⟨i, rfl⟩
  rcases hbracket.isBracketAlternating.2 (R.link i) hlink hdir with
    ⟨P, ⟨p, hp, rfl⟩, hsub⟩
  have hentry : (R.link i).entry ∈ (liftPath Z p).support :=
    hsub.1 (R.link i).entry_mem_support
  have hexit : (R.link i).exit ∈ (liftPath Z p).support :=
    hsub.1 (R.link i).exit_mem_support
  rcases (mem_support_liftPath Z p (R.link i).entry).1 hentry with
    ⟨x, _hx, hxe⟩
  rcases (mem_support_liftPath Z p (R.link i).exit).1 hexit with
    ⟨y, _hy, hye⟩
  have hxy : x = y := by
    have hx : x = project (R.link i).entry := by
      simpa only [project_occurrence] using congrArg project hxe
    have hy : y = project (R.link i).exit := by
      simpa only [project_occurrence] using congrArg project hye
    exact hx.trans (heq.trans hy.symm)
  subst y
  exact (R.link i).entry_ne_exit (hxe.symm.trans hye)

theorem linkSteps_ne_nil_of_forward
    {R : InfiniteTrace (web Gamma Z).graph} {i : ℕ}
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hdir : (R.link i).direction = .forward) :
    linkSteps Z (R.link i) ≠ [] := by
  apply (linkSteps_runs Z (R.link i)).nonempty_of_ne
  exact project_entry_ne_exit_of_forward Z hbracket hdir

/-- Every pair contains exactly one forward link, so its projected step list
is nonempty. -/
theorem pairSteps_ne_nil
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (n : ℕ) : pairSteps Z R n ≠ [] := by
  have halt := R.alternates (2 * n)
  cases h0 : (R.link (2 * n)).direction with
  | forward =>
      exact List.append_ne_nil_of_left_ne_nil
        (linkSteps_ne_nil_of_forward Z hbracket h0) _
  | backward =>
      have h1 : (R.link (2 * n + 1)).direction = .forward := by
        cases h : (R.link (2 * n + 1)).direction
        · rfl
        · exact (halt (h0.trans h.symm)).elim
      exact List.append_ne_nil_of_right_ne_nil _
        (linkSteps_ne_nil_of_forward Z hbracket h1)

theorem pairBlock_length_pos
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (n : ℕ) : 2 ≤ (pairBlock Z R n).length := by
  rw [pairBlock_length]
  have := List.length_pos_iff_ne_nil.2 (pairSteps_ne_nil Z R hbracket n)
  omega

/-- The concrete omega block stream before owner tags are attached. -/
def omegaBlocks
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R)) :
    OmegaBlocks V where
  block := pairBlock Z R
  length_pos := pairBlock_length_pos Z R hbracket
  joins := pairBlock_joins Z R

@[simp] theorem omegaBlocks_edgeLength
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (n : ℕ) :
    (omegaBlocks Z R hbracket).edgeLength n = (pairSteps Z R n).length := by
  simp [OmegaBlocks.edgeLength, omegaBlocks, pairBlock_length]

/-! ## Recovering the upstairs edge at every raw edge index -/

/-- The retained upstairs step at raw edge index `k`. -/
noncomputable def rawStep
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (k : ℕ) : TraversalStep (V := V) :=
  let B := omegaBlocks Z R hbracket
  (pairSteps Z R (B.locateBlock k)).get
    ⟨B.blockOffset k, by
      rw [← omegaBlocks_edgeLength (Y := Y) Z R hbracket]
      exact B.blockOffset_lt_edgeLength k⟩

/-- Raw vertices immediately before and after `k` are exactly the entry and
exit of `rawStep k`. -/
theorem rawVertex_eq_rawStep
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (k : ℕ) :
    (omegaBlocks Z R hbracket).rawVertex k =
        (rawStep Z R hbracket k).entry ∧
      (omegaBlocks Z R hbracket).rawVertex (k + 1) =
        (rawStep Z R hbracket k).exit := by
  let B := omegaBlocks Z R hbracket
  let n := B.locateBlock k
  let j := B.blockOffset k
  have hj : j < B.edgeLength n := B.blockOffset_lt_edgeLength k
  have hk : B.boundary n + j = k := B.boundary_add_blockOffset k
  have hleft := B.rawVertex_boundary_add_of_lt n j hj
  have hright := B.rawVertex_boundary_add n (j + 1) (by omega)
  have hruns := pairSteps_runs Z R n
  have hjsteps : j < (pairSteps Z R n).length := by
    rw [← omegaBlocks_edgeLength (Y := Y) Z R hbracket]
    exact hj
  constructor
  · rw [hk] at hleft
    rw [hleft]
    exact hruns.vertexChain_get_entry j hjsteps
  · have hkj : B.boundary n + (j + 1) = k + 1 := by omega
    rw [hkj] at hright
    rw [hright]
    exact hruns.vertexChain_get_exit j hjsteps

/-! ## Local finiteness of the concrete blocks -/

/-- Three distinct same-colour links in an infinite trace cannot all pass
through the same vertex.  Pairwise compatibility would force the common
vertex to alternate between the two endpoints of all three links. -/
theorem no_three_same_direction_links_at_vertex
    {D : Digraph (Vertex V)} (R : InfiniteTrace D)
    {i j k : ℕ} (hij : i < j) (hjk : j < k)
    {d : Direction}
    (hi : (R.link i).direction = d)
    (hj : (R.link j).direction = d)
    (hk : (R.link k).direction = d)
    {z : Vertex V}
    (hzi : z ∈ (R.link i).path.support)
    (hzj : z ∈ (R.link j).path.support)
    (hzk : z ∈ (R.link k).path.support) : False := by
  have cij := R.compatible i j hij
  have cjk := R.compatible j k hjk
  have cik := R.compatible i k (hij.trans hjk)
  cases d <;>
    simp only [CompatibleInOrder, hi, hj, hk] at cij cjk cik
  all_goals
    rcases cij hzi hzj with hij₁ | hij₂
    · rcases cjk hzj hzk with hjk₁ | hjk₂
      · exact (R.link j).entry_ne_exit
          (hjk₁.1.symm.trans hij₁.2)
      · rcases cik hzi hzk with hik₁ | hik₂
        · exact (R.link k).entry_ne_exit
            (hjk₂.2.symm.trans hik₁.2)
        · exact (R.link i).entry_ne_exit
            (hij₁.1.symm.trans hik₂.1)
    · rcases cjk hzj hzk with hjk₁ | hjk₂
      · rcases cik hzi hzk with hik₁ | hik₂
        · exact (R.link i).entry_ne_exit
            (hik₁.1.symm.trans hij₂.1)
        · exact (R.link k).entry_ne_exit
            (hik₂.2.symm.trans hjk₁.2)
      · exact (R.link j).entry_ne_exit
          (hij₂.2.symm.trans hjk₂.1)

/-- For one upstairs vertex and one direction, only finitely many links of
an infinite trace contain that vertex (in fact, at most two). -/
theorem link_indices_finite_of_direction
    {D : Digraph (Vertex V)} (R : InfiniteTrace D)
    (z : Vertex V) (d : Direction) :
    {i | (R.link i).direction = d ∧
      z ∈ (R.link i).path.support}.Finite := by
  apply OmegaBlocks.finite_of_triple_eq
  intro i hi j hj k hk
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hik : i = k
  · exact Or.inr (Or.inl hik)
  by_cases hjk : j = k
  · exact Or.inr (Or.inr hjk)
  exfalso
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
    · exact no_three_same_direction_links_at_vertex R hijlt hjklt
        hi.1 hj.1 hk.1 hi.2 hj.2 hk.2
    · rcases lt_or_gt_of_ne hik with hiklt | hkilt
      · exact no_three_same_direction_links_at_vertex R hiklt hkjlt
          hi.1 hk.1 hj.1 hi.2 hk.2 hj.2
      · exact no_three_same_direction_links_at_vertex R hkilt hijlt
          hk.1 hi.1 hj.1 hk.2 hi.2 hj.2
  · rcases lt_or_gt_of_ne hik with hiklt | hkilt
    · exact no_three_same_direction_links_at_vertex R hjilt hiklt
        hj.1 hi.1 hk.1 hj.2 hi.2 hk.2
    · rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
      · exact no_three_same_direction_links_at_vertex R hjklt hkilt
          hj.1 hk.1 hi.1 hj.2 hk.2 hi.2
      · exact no_three_same_direction_links_at_vertex R hkjlt hjilt
          hk.1 hj.1 hi.1 hk.2 hj.2 hi.2

/-- Every fixed upstairs vertex occurs in only finitely many links. -/
theorem link_indices_finite
    {D : Digraph (Vertex V)} (R : InfiniteTrace D) (z : Vertex V) :
    {i | z ∈ (R.link i).path.support}.Finite := by
  apply ((link_indices_finite_of_direction R z .forward).union
    (link_indices_finite_of_direction R z .backward)).subset
  intro i hi
  cases hdir : (R.link i).direction with
  | forward => exact Or.inl ⟨hdir, hi⟩
  | backward => exact Or.inr ⟨hdir, hi⟩

/-- Every vertex written in a pair block is the projection of a vertex on
one of its two upstairs links. -/
theorem pairBlock_mem_projects_link_support
    (R : InfiniteTrace (web Gamma Z).graph) (n : ℕ) {x : V}
    (hx : x ∈ pairBlock Z R n) :
    ∃ i, (i = 2 * n ∨ i = 2 * n + 1) ∧
      ∃ z ∈ (R.link i).path.support, project z = x := by
  simp only [pairBlock, List.mem_cons, List.mem_map] at hx
  rcases hx with hx | ⟨s, hs, hsx⟩
  · refine ⟨2 * n, Or.inl rfl, (R.link (2 * n)).entry,
      (R.link (2 * n)).entry_mem_support, ?_⟩
    exact hx.symm
  · simp only [pairSteps, List.mem_append] at hs
    rcases hs with hs | hs
    · have hm := linkSteps_mem Z (R.link (2 * n)) hs
      refine ⟨2 * n, Or.inl rfl, ?_⟩
      cases hdir : s.direction with
      | forward =>
          refine ⟨s.edge.2,
            ((R.link (2 * n)).path.edgeSet_subset_support_prod hm.2.1).2, ?_⟩
          simpa [TraversalStep.exit, hdir] using hsx
      | backward =>
          refine ⟨s.edge.1,
            ((R.link (2 * n)).path.edgeSet_subset_support_prod hm.2.1).1, ?_⟩
          simpa [TraversalStep.exit, hdir] using hsx
    · have hm := linkSteps_mem Z (R.link (2 * n + 1)) hs
      refine ⟨2 * n + 1, Or.inr rfl, ?_⟩
      cases hdir : s.direction with
      | forward =>
          refine ⟨s.edge.2,
            ((R.link (2 * n + 1)).path.edgeSet_subset_support_prod hm.2.1).2, ?_⟩
          simpa [TraversalStep.exit, hdir] using hsx
      | backward =>
          refine ⟨s.edge.1,
            ((R.link (2 * n + 1)).path.edgeSet_subset_support_prod hm.2.1).1, ?_⟩
          simpa [TraversalStep.exit, hdir] using hsx

/-- Only finitely many links contain a lift of one fixed projected vertex. -/
theorem projected_link_indices_finite
    (R : InfiniteTrace (web Gamma Z).graph) (x : V) :
    {i | ∃ z ∈ (R.link i).path.support, project z = x}.Finite := by
  let S : Set ℕ :=
    {i | plain x ∈ (R.link i).path.support} ∪
      ({i | incoming x ∈ (R.link i).path.support} ∪
        {i | outgoing x ∈ (R.link i).path.support})
  have hS : S.Finite :=
    (link_indices_finite R (plain x)).union
      ((link_indices_finite R (incoming x)).union
        (link_indices_finite R (outgoing x)))
  apply hS.subset
  intro i hi
  rcases hi with ⟨z, hz, hzx⟩
  change i ∈ S
  rcases z with ⟨y, r⟩
  change y = x at hzx
  subst y
  cases r with
  | plain => exact Or.inl hz
  | incoming => exact Or.inr (Or.inl hz)
  | outgoing => exact Or.inr (Or.inr hz)

/-- A projected vertex belongs to only finitely many pair blocks. -/
theorem pairBlock_indices_finite
    (R : InfiniteTrace (web Gamma Z).graph) (x : V) :
    {n | x ∈ pairBlock Z R n}.Finite := by
  let S : Set ℕ :=
    {i | ∃ z ∈ (R.link i).path.support, project z = x}
  have hS : S.Finite := projected_link_indices_finite Z R x
  have heven : ((fun n : ℕ ↦ 2 * n) ⁻¹' S).Finite := by
    apply hS.preimage
    intro a _ b _ hab
    change 2 * a = 2 * b at hab
    omega
  have hodd : ((fun n : ℕ ↦ 2 * n + 1) ⁻¹' S).Finite := by
    apply hS.preimage
    intro a _ b _ hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  apply (heven.union hodd).subset
  intro n hn
  rcases pairBlock_mem_projects_link_support Z R n hn with
    ⟨i, rfl | rfl, z, hz, hzx⟩
  · exact Or.inl ⟨z, hz, hzx⟩
  · exact Or.inr ⟨z, hz, hzx⟩

/-- The projected omega stream is locally finite, as required by
chronological loop erasure. -/
theorem omegaBlocks_vertex_finite
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (n : ℕ) :
    (occurrenceFiber (omegaBlocks Z R hbracket).rawVertex n).Finite := by
  change {k | (omegaBlocks Z R hbracket).rawVertex k =
    (omegaBlocks Z R hbracket).rawVertex n}.Finite
  apply (omegaBlocks Z R hbracket).rawVertex_fiber_finite
  exact pairBlock_indices_finite Z R

/-! ## Canonical owner of each upstairs link -/

private theorem mem_mapWalk_edgeSet_projects
    {A B : Type u} {D : Digraph A} {E : Digraph B}
    (f : A → B) (g : B → A) (hgf : ∀ x, g (f x) = x)
    (hf : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    {a b : A} (q : Walk D a b) {e : B × B}
    (he : e ∈ (FracturedDuplication.mapWalk f hf q).edgeSet) :
    (g e.1, g e.2) ∈ q.edgeSet := by
  induction q with
  | nil => simp [FracturedDuplication.mapWalk, Walk.edgeSet] at he
  | @cons a b c h q ih =>
      simp only [FracturedDuplication.mapWalk, Walk.edgeSet_cons,
        Set.mem_union, Set.mem_singleton_iff] at he ⊢
      rcases he with rfl | he
      · left
        simp [hgf]
      · exact Or.inr (ih he)

/-- Every occurrence-lifted edge projects to its original fractured edge. -/
theorem projected_edge_mem_of_mem_liftPath
    (p : Gamma.DPath) {e : Vertex V × Vertex V}
    (he : e ∈ (liftPath Z p).edgeSet) :
    (project e.1, project e.2) ∈ p.edgeSet := by
  rcases p with p | r
  · exact mem_mapWalk_edgeSet_projects
      (occurrence Z (Sum.inl p)) project
      (project_occurrence Z (Sum.inl p))
      (web_adj_occurrence Z (Sum.inl p)) p.walk he
  · rcases he with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [liftPath, FracturedDuplication.mapPath,
      FracturedDuplication.mapRay] using congrArg
        (fun e : Vertex V × Vertex V ↦ (project e.1, project e.2)) hn

private theorem vertexWalk_edges_contract
    (x : V) {e : Vertex V × Vertex V}
    (he : e ∈ (vertexWalk Z x).edgeSet) : project e.1 = project e.2 := by
  have hs := (vertexWalk Z x).edgeSet_subset_support_prod he
  rw [support_vertexWalk] at hs
  exact (mem_vertexBlock_project Z hs.1).trans
    (mem_vertexBlock_project Z hs.2).symm

private theorem projected_edge_mem_of_mem_expandWalk
    {a b : V} (q : Walk Gamma.graph a b)
    {e : Vertex V × Vertex V} (he : e ∈ (expandWalk Z q).edgeSet)
    (hne : project e.1 ≠ project e.2) :
    (project e.1, project e.2) ∈ q.edgeSet := by
  induction q with
  | nil => exact False.elim (hne (vertexWalk_edges_contract Z _ he))
  | @cons a b c h q ih =>
      rw [expandWalk, Alternating.RunCompressor.walk_edgeSet_append] at he
      rcases he with hblock | hrest
      · exact False.elim (hne (vertexWalk_edges_contract Z _ hblock))
      · simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at hrest ⊢
        rcases hrest with rfl | htail
        · left
          rfl
        · exact Or.inr (ih htail)

/-- Every nonconnector expanded-reference edge projects to its original
reference edge. -/
theorem projected_edge_mem_of_mem_expandFinitePath
    (p : FinitePath Gamma.graph) {e : Vertex V × Vertex V}
    (he : e ∈ (expandFinitePath Z p).edgeSet)
    (hne : project e.1 ≠ project e.2) :
    (project e.1, project e.2) ∈ p.edgeSet :=
  projected_edge_mem_of_mem_expandWalk Z p.walk he hne

/-- A downstairs owner for one upstairs link, including the exact subpath
certificate needed to prove backward owner uniqueness. -/
structure LinkCarrierData
    (R : InfiniteTrace (web Gamma Z).graph) (i : ℕ) where
  carrier : Gamma.DPath
  carrier_mem_forward : (R.link i).direction = .forward →
    carrier ∈ Z.edgeWarp
  carrier_mem_backward : (R.link i).direction = .backward →
    carrier ∈ activeReference Z Y
  projected_edge_mem_forward : ∀ {e},
    (R.link i).direction = .forward → e ∈ (R.link i).path.edgeSet →
      (project e.1, project e.2) ∈ carrier.edgeSet
  projected_edge_mem_backward : ∀ {e},
    (R.link i).direction = .backward → e ∈ (R.link i).path.edgeSet →
      project e.1 ≠ project e.2 →
      (project e.1, project e.2) ∈ carrier.edgeSet
  backward_expanded_subpath : (hdir : (R.link i).direction = .backward) →
    ∃ p : FinitePath Gamma.graph,
      carrier = Sum.inl p ∧
        (R.link i).path.IsSubpathOf
          (Sum.inl (expandFinitePath Z p) : (web Gamma Z).DPath)

/-- Bracket provenance supplies an owner for every link; forward literal
owners are enlarged to their unique recombined edge-warp member. -/
theorem exists_linkCarrierData
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) (i : ℕ) :
    Nonempty (LinkCarrierData (Y := Y) Z R i) := by
  have hlink : R.link i ∈ (AltPath.infinite R).links := ⟨i, rfl⟩
  cases hdir : (R.link i).direction with
  | forward =>
      rcases hbracket.isBracketAlternating.2 (R.link i) hlink hdir with
        ⟨P, ⟨p, hp, rfl⟩, hsub⟩
      rcases exists_edgeWarp_carrier_of_activePath Z hZfinite hp with
        ⟨q, hq, hpq⟩
      refine ⟨{
        carrier := q
        carrier_mem_forward := fun _ ↦ hq
        carrier_mem_backward := fun h ↦ (Direction.noConfusion (hdir.symm.trans h))
        projected_edge_mem_forward := ?_
        projected_edge_mem_backward := fun h ↦
          Direction.noConfusion (hdir.symm.trans h)
        backward_expanded_subpath := fun h ↦
          Direction.noConfusion (hdir.symm.trans h) }⟩
      intro e _ he
      exact hpq (projected_edge_mem_of_mem_liftPath Z p (hsub.2 he))
  | backward =>
      rcases hbracket.isAlternating.2.1 (R.link i) hlink hdir with
        ⟨P, ⟨p, hp, hP⟩, hsub⟩
      subst P
      refine ⟨{
        carrier := Sum.inl p
        carrier_mem_forward := fun h ↦
          Direction.noConfusion (hdir.symm.trans h)
        carrier_mem_backward := fun _ ↦ hp
        projected_edge_mem_forward := fun h ↦
          Direction.noConfusion (hdir.symm.trans h)
        projected_edge_mem_backward := ?_
        backward_expanded_subpath := fun _ ↦ ⟨p, rfl, hsub⟩ }⟩
      intro e _ he hne
      exact projected_edge_mem_of_mem_expandFinitePath Z p (hsub.2 he) hne

/-- The canonical (choice-independent downstream) carrier data of link `i`. -/
noncomputable def linkCarrierData
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) (i : ℕ) :
    LinkCarrierData (Y := Y) Z R i :=
  Classical.choice (exists_linkCarrierData Z R hbracket hZfinite i)

/-! ## Convex link-occurrence tags -/

/-- The two link occurrences inside one paired block. -/
abbrev EdgeTag := Sum ℕ ℕ

/-- Raw edge tag: block number plus the side of the split between its two
links. -/
noncomputable def rawEdgeTag
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (k : ℕ) : EdgeTag :=
  let B := omegaBlocks Z R hbracket
  let n := B.locateBlock k
  if B.blockOffset k < (linkSteps Z (R.link (2 * n))).length
  then .inl n else .inr n

/-- The upstairs link index named by a tag. -/
def tagLinkIndex : EdgeTag → ℕ
  | .inl n => 2 * n
  | .inr n => 2 * n + 1

def tagColour (R : InfiniteTrace (web Gamma Z).graph) (a : EdgeTag) :
    Direction :=
  (R.link (tagLinkIndex a)).direction

noncomputable def tagCarrier
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) (a : EdgeTag) :
    Gamma.DPath :=
  (linkCarrierData Z R hbracket hZfinite (tagLinkIndex a)).carrier

theorem rawEdgeBlock_mono
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    {i j : ℕ} (hij : i ≤ j) :
    (omegaBlocks Z R hbracket).locateBlock i ≤
      (omegaBlocks Z R hbracket).locateBlock j := by
  let B := omegaBlocks Z R hbracket
  change B.locateBlock i ≤ B.locateBlock j
  by_contra hnot
  have hi := B.boundary_locateBlock_le i
  have hj := B.lt_boundary_succ_locateBlock j
  have hblock : B.locateBlock j + 1 ≤ B.locateBlock i := by omega
  have hb := B.boundary_strictMono.monotone hblock
  exact (Nat.not_lt_of_ge ((hb.trans hi).trans hij)) hj

/-- Each link-occurrence tag occupies one convex raw interval. -/
theorem rawEdgeTag_convex
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hik : rawEdgeTag Z R hbracket i = rawEdgeTag Z R hbracket k) :
    rawEdgeTag Z R hbracket j = rawEdgeTag Z R hbracket i := by
  let B := omegaBlocks Z R hbracket
  let bi := B.locateBlock i
  let bj := B.locateBlock j
  let bk := B.locateBlock k
  let oi := B.blockOffset i
  let oj := B.blockOffset j
  let ok := B.blockOffset k
  have hbik : bi = bk := by
    dsimp only [rawEdgeTag] at hik
    split at hik <;> split at hik <;> simp_all [bi, bk, B]
  have hbij : bi = bj := by
    apply Nat.le_antisymm
    · exact rawEdgeBlock_mono Z R hbracket hij
    · rw [hbik]
      exact rawEdgeBlock_mono Z R hbracket hjk
  have hoffij : oi ≤ oj := by
    have hi := B.boundary_add_blockOffset i
    have hj := B.boundary_add_blockOffset j
    change B.boundary bi + oi = i at hi
    change B.boundary bj + oj = j at hj
    rw [← hbij] at hj
    omega
  have hoffjk : oj ≤ ok := by
    have hj := B.boundary_add_blockOffset j
    have hk := B.boundary_add_blockOffset k
    change B.boundary bj + oj = j at hj
    change B.boundary bk + ok = k at hk
    rw [← hbik, hbij] at hk
    omega
  dsimp only [rawEdgeTag] at hik ⊢
  change (if oi < (linkSteps Z (R.link (2 * bi))).length
      then Sum.inl bi else Sum.inr bi) =
    (if ok < (linkSteps Z (R.link (2 * bk))).length
      then Sum.inl bk else Sum.inr bk) at hik
  change (if oj < (linkSteps Z (R.link (2 * bj))).length
      then Sum.inl bj else Sum.inr bj) =
    (if oi < (linkSteps Z (R.link (2 * bi))).length
      then Sum.inl bi else Sum.inr bi)
  rw [← hbik] at hik
  rw [← hbij]
  by_cases hi : oi < (linkSteps Z (R.link (2 * bi))).length
  · have hk : ok < (linkSteps Z (R.link (2 * bi))).length := by
      by_contra hk
      simp [hi, hk] at hik
    have hj : oj < (linkSteps Z (R.link (2 * bi))).length := by omega
    simp [hi, hj]
  · have hk : ¬ok < (linkSteps Z (R.link (2 * bi))).length := by
      intro hk
      simp [hi, hk] at hik
    have hj : ¬oj < (linkSteps Z (R.link (2 * bi))).length := by omega
    simp [hi, hj]

/-- The raw step selected at `k` belongs to the upstairs link named by its
convex tag. -/
theorem rawStep_mem_tagLink
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (k : ℕ) :
    rawStep Z R hbracket k ∈
      linkSteps Z (R.link (tagLinkIndex (rawEdgeTag Z R hbracket k))) := by
  let B := omegaBlocks Z R hbracket
  let n := B.locateBlock k
  let j := B.blockOffset k
  have hjpair : j < (pairSteps Z R n).length := by
    rw [← omegaBlocks_edgeLength (Y := Y) Z R hbracket]
    exact B.blockOffset_lt_edgeLength k
  by_cases hfirst : j < (linkSteps Z (R.link (2 * n))).length
  · have htag : rawEdgeTag Z R hbracket k = Sum.inl n := by
      simp [rawEdgeTag, B, n, j, hfirst]
    rw [htag]
    change rawStep Z R hbracket k ∈ linkSteps Z (R.link (2 * n))
    have heq : rawStep Z R hbracket k =
        (linkSteps Z (R.link (2 * n))).get ⟨j, hfirst⟩ := by
      unfold rawStep
      simp only [pairSteps, List.get_eq_getElem]
      exact List.getElem_append_left hfirst
    rw [heq]
    exact List.get_mem _ _
  · have htag : rawEdgeTag Z R hbracket k = Sum.inr n := by
      simp [rawEdgeTag, B, n, j, hfirst]
    rw [htag]
    change rawStep Z R hbracket k ∈ linkSteps Z (R.link (2 * n + 1))
    have hjright :
        j - (linkSteps Z (R.link (2 * n))).length <
          (linkSteps Z (R.link (2 * n + 1))).length := by
      rw [pairSteps, List.length_append] at hjpair
      omega
    have heq : rawStep Z R hbracket k =
        (linkSteps Z (R.link (2 * n + 1))).get
          ⟨j - (linkSteps Z (R.link (2 * n))).length, hjright⟩ := by
      unfold rawStep
      simp only [pairSteps, List.get_eq_getElem]
      exact List.getElem_append_right (Nat.le_of_not_gt hfirst)
    rw [heq]
    exact List.get_mem _ _

theorem tagLinkIndex_injective :
    Function.Injective (tagLinkIndex : EdgeTag → ℕ) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [tagLinkIndex, Sum.inl.injEq, Sum.inr.injEq] at hab ⊢ <;>
    omega

/-- Exact edge provenance of the connector-deleted omega stream. -/
noncomputable def edgeProvenance
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) :
    FracturedEdgeProvenance (omegaBlocks Z R hbracket)
      Z.edgeWarp (activeReference Z Y) EdgeTag where
  member := rawEdgeTag Z R hbracket
  colour := tagColour Z R
  carrier := tagCarrier Z R hbracket hZfinite
  carrier_injective_on_backward := by
    intro a b ha hb hab
    let ia := tagLinkIndex a
    let ib := tagLinkIndex b
    let A := linkCarrierData Z R hbracket hZfinite ia
    let C := linkCarrierData Z R hbracket hZfinite ib
    have ha' : (R.link ia).direction = .backward := ha
    have hb' : (R.link ib).direction = .backward := hb
    rcases A.backward_expanded_subpath ha' with ⟨p, hAp, hsuba⟩
    rcases C.backward_expanded_subpath hb' with ⟨q, hCq, hsubb⟩
    have hpq : p = q := by
      apply Sum.inl.inj
      exact hAp.symm.trans (hab.trans hCq)
    subst q
    have hp : (Sum.inl p : Gamma.DPath) ∈ activeReference Z Y := by
      rw [← hAp]
      exact A.carrier_mem_backward ha'
    have hi : ia = ib :=
      R.backward_indices_eq_of_common_owner hbracket.isSafe
        (liftedReference_hasFiniteCharacter Z (activeReference Z Y))
        ha' hb' ⟨p, hp, rfl⟩ hsuba hsubb
    exact tagLinkIndex_injective hi
  carrier_mem_forward := by
    intro a ha
    exact (linkCarrierData Z R hbracket hZfinite (tagLinkIndex a)).carrier_mem_forward ha
  carrier_mem_backward := by
    intro a ha
    exact (linkCarrierData Z R hbracket hZfinite (tagLinkIndex a)).carrier_mem_backward ha
  edge_mem_forward := by
    intro k hk
    let a := rawEdgeTag Z R hbracket k
    let i := tagLinkIndex a
    let s := rawStep Z R hbracket k
    have hs := linkSteps_mem Z (R.link i)
      (rawStep_mem_tagLink Z R hbracket k)
    have hsdir : s.direction = .forward := hs.1.trans hk
    have hedge :=
      (linkCarrierData Z R hbracket hZfinite i).projected_edge_mem_forward
        hk hs.2.1
    have hv := rawVertex_eq_rawStep Z R hbracket k
    change ((omegaBlocks Z R hbracket).rawVertex k,
      (omegaBlocks Z R hbracket).rawVertex (k + 1)) ∈
        (tagCarrier Z R hbracket hZfinite a).edgeSet
    rw [hv.1, hv.2]
    change (s.entry, s.exit) ∈
      (linkCarrierData Z R hbracket hZfinite i).carrier.edgeSet
    simpa [s, TraversalStep.entry, TraversalStep.exit, hsdir] using hedge
  edge_mem_backward := by
    intro k hk
    let a := rawEdgeTag Z R hbracket k
    let i := tagLinkIndex a
    let s := rawStep Z R hbracket k
    have hs := linkSteps_mem Z (R.link i)
      (rawStep_mem_tagLink Z R hbracket k)
    have hsdir : s.direction = .backward := hs.1.trans hk
    have hedge :=
      (linkCarrierData Z R hbracket hZfinite i).projected_edge_mem_backward
        hk hs.2.1 hs.2.2
    have hv := rawVertex_eq_rawStep Z R hbracket k
    change ((omegaBlocks Z R hbracket).rawVertex (k + 1),
      (omegaBlocks Z R hbracket).rawVertex k) ∈
        (tagCarrier Z R hbracket hZfinite a).edgeSet
    rw [hv.1, hv.2]
    change (s.exit, s.entry) ∈
      (linkCarrierData Z R hbracket hZfinite i).carrier.edgeSet
    simpa [s, TraversalStep.entry, TraversalStep.exit, hsdir] using hedge
  member_convex := rawEdgeTag_convex Z R hbracket

/-- Finite character of the two downstairs owner families, together with
local finiteness of the raw vertex stream, makes every carrier fibre finite. -/
theorem edgeProvenance_carrier_finite
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (p : Gamma.DPath) :
    {k | (edgeProvenance Z R hbracket hZfinite).carrier
      ((edgeProvenance Z R hbracket hZfinite).member k) = p}.Finite := by
  let B := omegaBlocks Z R hbracket
  let P := edgeProvenance Z R hbracket hZfinite
  by_cases hex : ∃ k, P.carrier (P.member k) = p
  · rcases hex with ⟨k₀, hk₀⟩
    have hpFinite : ∃ q : FinitePath Gamma.graph, p = Sum.inl q := by
      cases hdir : P.colour (P.member k₀) with
      | forward =>
          obtain ⟨q, hq⟩ := hZedgeFinite (P.carrier_mem_forward _ hdir)
          exact ⟨q, hk₀.symm.trans hq⟩
      | backward =>
          obtain ⟨q, hq⟩ :=
            activeReference_hasFiniteCharacter Z hYfinite
              (P.carrier_mem_backward _ hdir)
          exact ⟨q, hk₀.symm.trans hq⟩
    rcases hpFinite with ⟨q, rfl⟩
    let U : Set ℕ := ⋃ x ∈ q.support, {k | B.rawVertex k = x}
    have hU : U.Finite := by
      apply q.support_finite.biUnion
      intro x _
      exact B.rawVertex_fiber_finite (pairBlock_indices_finite Z R) x
    apply hU.subset
    intro k hk
    have hvertex : B.rawVertex k ∈ q.support := by
      cases hdir : P.colour (P.member k) with
      | forward =>
          have he := P.edge_mem_forward k hdir
          rw [hk] at he
          have he' : (B.rawVertex k, B.rawVertex (k + 1)) ∈
              q.edgeSet := by simpa [Path.edgeSet] using he
          exact (q.edgeSet_subset_support_prod he').1
      | backward =>
          have he := P.edge_mem_backward k hdir
          rw [hk] at he
          have he' : (B.rawVertex (k + 1), B.rawVertex k) ∈
              q.edgeSet := by simpa [Path.edgeSet] using he
          exact (q.edgeSet_subset_support_prod he').2
    exact Set.mem_iUnion.2 ⟨B.rawVertex k,
      Set.mem_iUnion.2 ⟨hvertex, rfl⟩⟩
  · have hempty : {k | P.carrier (P.member k) = p} = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.mpr fun k hk ↦ hex ⟨k, hk⟩
    rw [hempty]
    exact Set.finite_empty

/-- The first raw vertex is the projection of the first upstairs link. -/
theorem omegaBlocks_rawVertex_zero_eq_project_initial
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R)) :
    (omegaBlocks Z R hbracket).rawVertex 0 =
      project (AltPath.infinite R).initial := by
  let B := omegaBlocks Z R hbracket
  change B.rawVertex 0 = _
  rw [← B.boundary_zero, B.rawVertex_boundary]
  rfl

/-- Automatic connector-deletion frontend for every bracket-safe infinite
upstairs trace.  This is the concrete input consumed by
`InfiniteTraversalBlocks.compile`. -/
noncomputable def infiniteTraversalBlocks
    (R : InfiniteTrace (web Gamma Z).graph)
    (hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R))
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : project (AltPath.infinite R).initial ∉
      Gamma.vertexSet Y) :
    InfiniteTraversalBlocks (Y := Y) Z (.infinite R) EdgeTag where
  upstairs_infinite := by simp [AltPath.IsInfinite]
  upstairs_bracket := hbracket
  blocks := omegaBlocks Z R hbracket
  provenance := edgeProvenance Z R hbracket hZfinite
  rawVertex_zero_eq_project_initial :=
    omegaBlocks_rawVertex_zero_eq_project_initial Z R hbracket
  vertex_finite := omegaBlocks_vertex_finite Z R hbracket
  carrier_finite :=
    edgeProvenance_carrier_finite Z R hbracket hZfinite
      hZedgeFinite hYfinite
  initial_outside := by
    rw [omegaBlocks_rawVertex_zero_eq_project_initial Z R hbracket]
    intro hactive
    apply hinitial
    rcases hactive with ⟨p, hp, hpx⟩
    exact ⟨p, activeReference_subset Z Y hp, hpx⟩

end InfiniteTraversalFrontend

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
