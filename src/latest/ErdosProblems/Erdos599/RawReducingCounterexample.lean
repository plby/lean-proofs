/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CountableAssignment

/-!
# The raw reducing-switch rule is false

This file records the six-vertex crossing obstruction to applying a raw
`[Y,Z]`-alternating trace as a linkage exchange.  A forward link may cross an
unused member of `Z`; after the requested endpoint deletion that crossing can
be a one-vertex bottleneck for two surviving paths.
-/

namespace Erdos599.Alternating.RawReducingCounterexample

open Set DirectedPath

inductive Vertex
  | a | v | u | b | z | x | w
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj p q :=
    (p = a ∧ q = v) ∨ (p = u ∧ q = b) ∨ (p = z ∧ q = x) ∨
      (p = x ∧ q = w) ∨ (p = a ∧ q = x) ∨ (p = x ∧ q = b)

@[simp] theorem graph_adj (p q : Vertex) :
    graph.Adj p q ↔
      (p = a ∧ q = v) ∨ (p = u ∧ q = b) ∨ (p = z ∧ q = x) ∨
        (p = x ∧ q = w) ∨ (p = a ∧ q = x) ∨ (p = x ∧ q = b) :=
  Iff.rfl

def av : FinitePath graph where
  start := a
  finish := v
  walk := Walk.cons (u := a) (v := v) (w := v) (by simp [graph]) Walk.nil
  isPath := by
    change [a, v].Nodup
    simp

def ub : FinitePath graph where
  start := u
  finish := b
  walk := Walk.cons (u := u) (v := b) (w := b) (by simp [graph]) Walk.nil
  isPath := by
    change [u, b].Nodup
    simp

def zx : FinitePath graph where
  start := z
  finish := w
  walk := Walk.cons (u := z) (v := x) (w := w) (by simp [graph])
    (Walk.cons (u := x) (v := w) (w := w) (by simp [graph]) Walk.nil)
  isPath := by
    change [z, x, w].Nodup
    simp

def axb : FinitePath graph where
  start := a
  finish := b
  walk := Walk.cons (u := a) (v := x) (w := b) (by simp [graph])
    (Walk.cons (u := x) (v := b) (w := b) (by simp [graph]) Walk.nil)
  isPath := by
    change [a, x, b].Nodup
    simp

@[simp] theorem support_av : av.support = {a, v} := by
  ext w
  change w ∈ [a, v] ↔ _
  simp

@[simp] theorem support_ub : ub.support = {u, b} := by
  ext w
  change w ∈ [u, b] ↔ _
  simp

@[simp] theorem support_zx : zx.support = {z, x, w} := by
  ext w
  change w ∈ [z, x, Vertex.w] ↔ _
  simp

@[simp] theorem support_axb : axb.support = {a, x, b} := by
  ext w
  change w ∈ [a, x, b] ↔ _
  simp

@[simp] theorem start_av : av.start = a := rfl
@[simp] theorem finish_av : av.finish = v := rfl
@[simp] theorem start_ub : ub.start = u := rfl
@[simp] theorem finish_ub : ub.finish = b := rfl
@[simp] theorem start_zx : zx.start = z := rfl
@[simp] theorem finish_zx : zx.finish = w := rfl
@[simp] theorem start_axb : axb.start = a := rfl
@[simp] theorem finish_axb : axb.finish = b := rfl

def web : DWeb Vertex where
  graph := graph
  source := {a, u, z}
  target := {v, b, w}

def Z : Set web.DPath := {Sum.inl av, Sum.inl ub, Sum.inl zx}
def Y : Set web.DPath := {Sum.inl axb}

theorem web_normalized : web.IsNormalized := by
  intro p q hpq
  change graph.Adj p q at hpq
  simp only [graph_adj] at hpq
  rcases hpq with hpq | hpq | hpq | hpq | hpq | hpq
  all_goals rcases hpq with ⟨rfl, rfl⟩ <;> simp [web]

def first : Link graph where
  path := av
  direction := .backward
  nontrivial := by simp [av]

def middle : Link graph where
  path := axb
  direction := .forward
  nontrivial := by simp [axb]

def last : Link graph where
  path := ub
  direction := .backward
  nontrivial := by simp [ub]

private theorem compatible_first_middle (P : Prop) (hP : P) :
    CompatibleInOrder P first middle := by
  simp only [CompatibleInOrder, first, middle]
  constructor
  · intro _ w hw₁ hw₂
    rw [support_av] at hw₁
    rw [support_axb] at hw₂
    have : w = a := by
      cases w <;> simp_all
    left
    subst w
    rfl
  · intro hn
    exact (hn hP).elim

private theorem compatible_middle_last (P : Prop) (hP : P) :
    CompatibleInOrder P middle last := by
  simp only [CompatibleInOrder, middle, last]
  constructor
  · intro _
    change axb.support ∩ ub.support = {b}
    rw [support_axb, support_ub]
    ext w
    cases w <;> simp
  · intro hn
    exact (hn hP).elim

private theorem compatible_first_last (P : Prop) :
    CompatibleInOrder P first last := by
  simp [CompatibleInOrder, first, last, Link.exit, Link.entry]

private def traceLink (i : Fin 3) : Link graph :=
  if i.1 = 0 then first else if i.1 = 1 then middle else last

@[simp] private theorem traceLink_zero : traceLink 0 = first := by
  simp [traceLink]

@[simp] private theorem traceLink_one : traceLink 1 = middle := by
  simp [traceLink]

@[simp] private theorem traceLink_two : traceLink 2 = last := by
  simp [traceLink]

def trace : FiniteTrace graph :=
  { lastIndex := 2
    link := traceLink
    joins := by
      intro i
      have hi : i.1 = 0 ∨ i.1 = 1 := by omega
      rcases hi with hi | hi
      · have hieq : i = (0 : Fin 2) := Fin.ext hi
        subst i
        simp [traceLink, first, middle, Link.exit, Link.entry]
      · have hieq : i = (1 : Fin 2) := Fin.ext hi
        subst i
        simp [traceLink, middle, last, Link.exit, Link.entry]
    alternates := by
      intro i
      have hi : i.1 = 0 ∨ i.1 = 1 := by omega
      rcases hi with hi | hi
      · have hieq : i = (0 : Fin 2) := Fin.ext hi
        subst i
        simp [traceLink, first, middle]
      · have hieq : i = (1 : Fin 2) := Fin.ext hi
        subst i
        simp [traceLink, middle, last]
    compatible := by
      intro i j hij
      have hpairs :
          (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 0 ∧ j.1 = 2) ∨
            (i.1 = 1 ∧ j.1 = 2) := by omega
      rcases hpairs with hp | hp | hp
      · have hi : i = (0 : Fin 3) := Fin.ext hp.1
        have hj : j = (1 : Fin 3) := Fin.ext hp.2
        subst i
        subst j
        simp only [traceLink_zero, traceLink_one]
        exact compatible_first_middle _ (by omega)
      · have hi : i = (0 : Fin 3) := Fin.ext hp.1
        have hj : j = (2 : Fin 3) := Fin.ext hp.2
        subst i
        subst j
        simp only [traceLink_zero, traceLink_two]
        exact compatible_first_last _
      · have hi : i = (1 : Fin 3) := Fin.ext hp.1
        have hj : j = (2 : Fin 3) := Fin.ext hp.2
        subst i
        subst j
        simp only [traceLink_one, traceLink_two]
        exact compatible_middle_last _ (by omega) }

def T : AltPath web.graph := .finite trace

@[simp] theorem T_initial : T.initial = v := by
  rfl

@[simp] theorem T_terminal : T.terminal? = some u := by
  rfl

@[simp] theorem T_firstDirection : T.firstDirection? = some .backward := by
  rfl

@[simp] theorem T_lastDirection : T.lastDirection? = some .backward := by
  rfl

private theorem mem_T_links_iff {l : Link web.graph} :
    l ∈ T.links ↔ l = first ∨ l = middle ∨ l = last := by
  constructor
  · rintro ⟨i, rfl⟩
    change Fin 3 at i
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
    rcases hi with hi | hi | hi
    · have hieq : i = (0 : Fin 3) := Fin.ext hi
      subst i
      change first = first ∨ first = middle ∨ first = last
      exact Or.inl rfl
    · have hieq : i = (1 : Fin 3) := Fin.ext hi
      subst i
      change middle = first ∨ middle = middle ∨ middle = last
      exact Or.inr (Or.inl rfl)
    · have hieq : i = (2 : Fin 3) := Fin.ext hi
      subst i
      change last = first ∨ last = middle ∨ last = last
      exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨(0 : Fin 3), rfl⟩
    · exact ⟨(1 : Fin 3), rfl⟩
    · exact ⟨(2 : Fin 3), rfl⟩

private theorem av_mem_Z : (Sum.inl av : web.DPath) ∈ Z := by
  change Sum.inl av = Sum.inl av ∨
    Sum.inl av = Sum.inl ub ∨ Sum.inl av = Sum.inl zx
  exact Or.inl rfl

private theorem ub_mem_Z : (Sum.inl ub : web.DPath) ∈ Z := by
  change Sum.inl ub = Sum.inl av ∨
    Sum.inl ub = Sum.inl ub ∨ Sum.inl ub = Sum.inl zx
  exact Or.inr (Or.inl rfl)

private theorem zx_mem_Z : (Sum.inl zx : web.DPath) ∈ Z := by
  change Sum.inl zx = Sum.inl av ∨
    Sum.inl zx = Sum.inl ub ∨ Sum.inl zx = Sum.inl zx
  exact Or.inr (Or.inr rfl)

private theorem axb_mem_Y : (Sum.inl axb : web.DPath) ∈ Y := by
  change Sum.inl axb = Sum.inl axb
  rfl

@[simp] private theorem path_support_av :
    DirectedPath.Path.support (Sum.inl av : web.DPath) = {a, v} := support_av

@[simp] private theorem path_support_ub :
    DirectedPath.Path.support (Sum.inl ub : web.DPath) = {u, b} := support_ub

@[simp] private theorem path_support_zx :
    DirectedPath.Path.support (Sum.inl zx : web.DPath) = {z, x, w} := support_zx

@[simp] private theorem path_support_axb :
    DirectedPath.Path.support (Sum.inl axb : web.DPath) = {a, x, b} := support_axb

theorem Z_isWarp : web.IsWarp Z := by
  intro p hp q hq hpq
  simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl
  · rcases hq with rfl | rfl | rfl
    · exact (hpq rfl).elim
    · change Disjoint av.support ub.support
      rw [support_av, support_ub]
      simp [Set.disjoint_left]
    · change Disjoint av.support zx.support
      rw [support_av, support_zx]
      simp [Set.disjoint_left]
  · rcases hq with rfl | rfl | rfl
    · change Disjoint ub.support av.support
      rw [support_ub, support_av]
      simp [Set.disjoint_left]
    · exact (hpq rfl).elim
    · change Disjoint ub.support zx.support
      rw [support_ub, support_zx]
      simp [Set.disjoint_left]
  · rcases hq with rfl | rfl | rfl
    · change Disjoint zx.support av.support
      rw [support_zx, support_av]
      simp [Set.disjoint_left]
    · change Disjoint zx.support ub.support
      rw [support_zx, support_ub]
      simp [Set.disjoint_left]
    · exact (hpq rfl).elim

theorem Z_finite : web.HasFiniteCharacter Z := by
  intro p hp
  simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨av, rfl⟩
  · exact ⟨ub, rfl⟩
  · exact ⟨zx, rfl⟩

theorem Z_initial_source : web.initialSet Z ⊆ web.source := by
  rintro t ⟨p, hp, rfl⟩
  simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · change av.start ∈ ({a, u, z} : Set Vertex)
    simp
  · change ub.start ∈ ({a, u, z} : Set Vertex)
    simp
  · change zx.start ∈ ({a, u, z} : Set Vertex)
    simp

theorem Z_terminal_target : web.terminalFrontier Z ⊆ web.target := by
  rintro t ⟨p, hp, hpt⟩
  simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · change some v = some t at hpt
    have ht : t = v := Option.some.inj hpt.symm
    subst t
    simp [web]
  · change some b = some t at hpt
    have ht : t = b := Option.some.inj hpt.symm
    subst t
    simp [web]
  · change some w = some t at hpt
    have ht : t = w := Option.some.inj hpt.symm
    subst t
    simp [web]

theorem Y_isWarp : web.IsWarp Y := by
  intro p hp q hq hpq
  change p = Sum.inl axb at hp
  change q = Sum.inl axb at hq
  have hp' : p = Sum.inl axb := hp
  have hq' : q = Sum.inl axb := hq
  exact (hpq (hp'.trans hq'.symm)).elim

theorem Y_finite : web.HasFiniteCharacter Y := by
  intro p hp
  change p = Sum.inl axb at hp
  have hp' : p = Sum.inl axb := hp
  subst p
  exact ⟨axb, rfl⟩

theorem Y_initial_subset_Z : web.initialSet Y ⊆ web.initialSet Z := by
  rintro t ⟨p, hp, hpt⟩
  change p = Sum.inl axb at hp
  subst p
  change axb.start = t at hpt
  subst t
  exact ⟨Sum.inl av, av_mem_Z, rfl⟩

theorem T_isBracketAlternating : IsBracketAlternating Y Z T := by
  constructor
  · refine ⟨Z_isWarp, ?_, ?_, ?_⟩
    · intro l hl hback
      rw [mem_T_links_iff] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨Sum.inl av, av_mem_Z, av.isSubpathOf_self⟩
      · simp [middle] at hback
      · exact ⟨Sum.inl ub, ub_mem_Z, ub.isSubpathOf_self⟩
    · simp
    · intro t ht hdir
      simp at hdir
  · intro l hl hforward
    rw [mem_T_links_iff] at hl
    rcases hl with rfl | rfl | rfl
    · simp [first] at hforward
    · exact ⟨Sum.inl axb, axb_mem_Y, axb.isSubpathOf_self⟩
    · simp [last] at hforward

theorem u_initial_Z : u ∈ web.initialSet Z :=
  ⟨Sum.inl ub, ub_mem_Z, rfl⟩

theorem v_terminal_Z : v ∈ web.terminalFrontier Z :=
  ⟨Sum.inl av, av_mem_Z, rfl⟩

theorem u_not_vertex_Y : u ∉ web.vertexSet Y := by
  rintro ⟨p, hp, hu⟩
  change p = Sum.inl axb at hp
  have hp' : p = Sum.inl axb := hp
  subst p
  change u ∈ axb.support at hu
  rw [support_axb] at hu
  simp at hu

theorem v_not_vertex_Y : v ∉ web.vertexSet Y := by
  rintro ⟨p, hp, hv⟩
  change p = Sum.inl axb at hp
  have hp' : p = Sum.inl axb := hp
  subst p
  change v ∈ axb.support at hv
  rw [support_axb] at hv
  simp at hv

private theorem walk_from_v_ends_at_v {t : Vertex}
    (q : Walk graph v t) : t = v := by
  cases q with
  | nil => rfl
  | @cons _ y _ h r => simp [graph] at h

/-- The crossing vertex is a one-point cut between either surviving initial
and either surviving terminal. -/
theorem x_mem_support_of_surviving_endpoints
    (p : FinitePath graph) (hs : p.start = a ∨ p.start = z)
    (ht : p.finish = b ∨ p.finish = w) : x ∈ p.support := by
  rcases p with ⟨s, t, w, hw⟩
  dsimp at hs ht ⊢
  rcases hs with rfl | rfl
  · cases w with
    | nil => simp at ht
    | @cons _ y _ h q =>
        have hy : y = v ∨ y = x := by simpa [graph] using h
        rcases hy with rfl | rfl
        · have ht' : t = v := walk_from_v_ends_at_v q
          rcases ht with rfl | rfl <;> simp at ht'
        · simp [FinitePath.support]
  · cases w with
    | nil => simp at ht
    | @cons _ y _ h q =>
        have hy : y = x := by simpa [graph] using h
        subst y
        simp [FinitePath.support]

private theorem terminalFrontier_Z_iff {t : Vertex} :
    t ∈ web.terminalFrontier Z ↔ t = v ∨ t = b ∨ t = w := by
  constructor
  · rintro ⟨p, hp, hpt⟩
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · left
      simpa using Option.some.inj hpt.symm
    · right; left
      simpa using Option.some.inj hpt.symm
    · right; right
      simpa using Option.some.inj hpt.symm
  · rintro (rfl | rfl | rfl)
    · exact v_terminal_Z
    · exact ⟨Sum.inl ub, ub_mem_Z, rfl⟩
    · exact ⟨Sum.inl zx, zx_mem_Z, rfl⟩

private theorem a_initial_Z : a ∈ web.initialSet Z :=
  ⟨Sum.inl av, av_mem_Z, rfl⟩

private theorem z_initial_Z : z ∈ web.initialSet Z :=
  ⟨Sum.inl zx, zx_mem_Z, rfl⟩

/-- The exact rule consumed by the countable assignment cannot be proved
from a raw bracket-alternating trace.  The forward link `a→x→b` crosses
the unused `Z`-path `z→x`; after deleting `u` and `v`, both required
surviving paths must contain `x`. -/
theorem not_reducingSwitchRule : ¬ ReducingSwitchRule web := by
  intro hRule
  obtain ⟨Z', hZ'warp, hZ'finite, hinit, hterminal, _hvertices⟩ :=
    hRule Z Y u v T Z_isWarp Z_finite Y_isWarp Y_finite
      u_initial_Z u_not_vertex_Y v_terminal_Z v_not_vertex_Y
      T_isBracketAlternating T_initial T_terminal (by trivial)
  have haDiff : a ∈ web.initialSet Z \ {u} := ⟨a_initial_Z, by simp⟩
  have hzDiff : z ∈ web.initialSet Z \ {u} := ⟨z_initial_Z, by simp⟩
  have haInit : a ∈ web.initialSet Z' := by
    rw [hinit]
    exact haDiff
  have hzInit : z ∈ web.initialSet Z' := by
    rw [hinit]
    exact hzDiff
  rcases haInit with ⟨pa, hpaZ', hpaInit⟩
  rcases hzInit with ⟨pz, hpzZ', hpzInit⟩
  rcases hZ'finite hpaZ' with ⟨qa, hpa⟩
  rcases hZ'finite hpzZ' with ⟨qz, hpz⟩
  subst pa
  subst pz
  have hqaTerminal' : qa.finish ∈ web.terminalFrontier Z' :=
    ⟨Sum.inl qa, hpaZ', rfl⟩
  have hqzTerminal' : qz.finish ∈ web.terminalFrontier Z' :=
    ⟨Sum.inl qz, hpzZ', rfl⟩
  rw [hterminal] at hqaTerminal' hqzTerminal'
  have hqaEnds : qa.finish = b ∨ qa.finish = w := by
    have hclass := terminalFrontier_Z_iff.mp hqaTerminal'.1
    rcases hclass with h | h | h
    · exact (hqaTerminal'.2 h).elim
    · exact Or.inl h
    · exact Or.inr h
  have hqzEnds : qz.finish = b ∨ qz.finish = w := by
    have hclass := terminalFrontier_Z_iff.mp hqzTerminal'.1
    rcases hclass with h | h | h
    · exact (hqzTerminal'.2 h).elim
    · exact Or.inl h
    · exact Or.inr h
  have hqaStarts : qa.start = a := hpaInit
  have hqzStarts : qz.start = z := hpzInit
  have hxqa : x ∈ qa.support :=
    x_mem_support_of_surviving_endpoints qa (Or.inl hqaStarts) hqaEnds
  have hxqz : x ∈ qz.support :=
    x_mem_support_of_surviving_endpoints qz (Or.inr hqzStarts) hqzEnds
  have hne : (Sum.inl qa : web.DPath) ≠ Sum.inl qz := by
    intro heq
    have hi := congrArg DirectedPath.Path.initial heq
    change qa.start = qz.start at hi
    rw [hqaStarts, hqzStarts] at hi
    contradiction
  exact Set.disjoint_left.1 (hZ'warp hpaZ' hpzZ' hne) hxqa hxqz

end Erdos599.Alternating.RawReducingCounterexample
