/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingDichotomy
import ErdosProblems.Erdos599.BoundarySimultaneousAssignment
import ErdosProblems.Erdos599.HalfwayClosedEndpointPairing
import ErdosProblems.Erdos599.HalfwayCutConstruction

/-!
# Audit of the endpoint-cleaning step in Assertion 9.31

Closure under the reference warp does not make a safe alternating path
internally disjoint from the closing set.  The finite example below is the
smallest obstruction relevant to the printed proof.  A single later linkage
path crosses `X`, and the reference path runs in the opposite direction
between the two consecutive contacts.  The resulting safe alternating path
uses two literal holes and one backward reference block contained in `X`.

This file deliberately records only the facts needed to reject the tempting
"truncate at the first/last `X` contact" inference.  It does not assert that
the Aharoni--Berger theorem is false; a correct completion must use additional
structure of the selected linkage or a different simultaneous construction.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.EndpointCleanAudit

open Set DirectedPath Alternating

inductive Vertex
  | s | c | a | b | d | t
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj x y :=
    (x = s ∧ y = c) ∨ (x = c ∧ y = a) ∨
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨
    (x = b ∧ y = d) ∨ (x = d ∧ y = t)

@[simp] theorem graph_adj (x y : Vertex) :
    graph.Adj x y ↔
      (x = s ∧ y = c) ∨ (x = c ∧ y = a) ∨
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨
      (x = b ∧ y = d) ∨ (x = d ∧ y = t) :=
  Iff.rfl

def web : DWeb Vertex where
  graph := graph
  source := {s, b}
  target := {a, t}

def sca : FinitePath web.graph where
  start := s
  finish := a
  walk := Walk.cons (u := s) (v := c) (w := a) (by simp [web, graph])
    (Walk.cons (u := c) (v := a) (w := a) (by simp [web, graph]) Walk.nil)
  isPath := by
    change [s, c, a].Nodup
    simp

def ab : FinitePath web.graph where
  start := a
  finish := b
  walk := Walk.cons (u := a) (v := b) (w := b) (by simp [web, graph]) Walk.nil
  isPath := by
    change [a, b].Nodup
    simp

def ba : FinitePath web.graph where
  start := b
  finish := a
  walk := Walk.cons (u := b) (v := a) (w := a) (by simp [web, graph]) Walk.nil
  isPath := by
    change [b, a].Nodup
    simp

def bdt : FinitePath web.graph where
  start := b
  finish := t
  walk := Walk.cons (u := b) (v := d) (w := t) (by simp [web, graph])
    (Walk.cons (u := d) (v := t) (w := t) (by simp [web, graph]) Walk.nil)
  isPath := by
    change [b, d, t].Nodup
    simp

def Wpath : FinitePath web.graph where
  start := s
  finish := t
  walk := Walk.cons (u := s) (v := c) (w := t) (by simp [web, graph])
    (Walk.cons (u := c) (v := a) (w := t) (by simp [web, graph])
      (Walk.cons (u := a) (v := b) (w := t) (by simp [web, graph])
        (Walk.cons (u := b) (v := d) (w := t) (by simp [web, graph])
          (Walk.cons (u := d) (v := t) (w := t) (by simp [web, graph]) Walk.nil))))
  isPath := by
    change [s, c, a, b, d, t].Nodup
    simp

def Z : Set web.DPath := {Sum.inl sca, Sum.inl bdt}
def Y : Set web.DPath := {Sum.inl ba}
def W : Set web.DPath := {Sum.inl Wpath}
def X : Set Vertex := {s, a, b, t}

@[simp] theorem support_sca : sca.support = {s, c, a} := by
  ext x
  change x ∈ [s, c, a] ↔ _
  simp

@[simp] theorem support_ab : ab.support = {a, b} := by
  ext x
  change x ∈ [a, b] ↔ _
  simp

@[simp] theorem support_ba : ba.support = {b, a} := by
  ext x
  change x ∈ [b, a] ↔ _
  simp

@[simp] theorem support_bdt : bdt.support = {b, d, t} := by
  ext x
  change x ∈ [b, d, t] ↔ _
  simp

@[simp] theorem support_Wpath : Wpath.support = {s, c, a, b, d, t} := by
  ext x
  change x ∈ [s, c, a, b, d, t] ↔ _
  simp

theorem Z_isWarp : web.IsWarp Z := by
  intro p hp q hq hpq
  simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint sca.support bdt.support
    rw [support_sca, support_bdt]
    simp [Set.disjoint_left]
  · change Disjoint bdt.support sca.support
    rw [support_bdt, support_sca]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim

theorem Y_isWarp : web.IsWarp Y := by
  intro p hp q hq hpq
  change p = Sum.inl ba at hp
  change q = Sum.inl ba at hq
  exact (hpq (hp.trans hq.symm)).elim

theorem W_isWarp : web.IsWarp W := by
  intro p hp q hq hpq
  change p = Sum.inl Wpath at hp
  change q = Sum.inl Wpath at hq
  exact (hpq (hp.trans hq.symm)).elim

theorem Z_finite : web.HasFiniteCharacter Z := by
  intro p hp
  simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨sca, rfl⟩
  · exact ⟨bdt, rfl⟩

theorem Y_finite : web.HasFiniteCharacter Y := by
  intro p hp
  change p = Sum.inl ba at hp
  subst p
  exact ⟨ba, rfl⟩

theorem W_finite : web.HasFiniteCharacter W := by
  intro p hp
  change p = Sum.inl Wpath at hp
  subst p
  exact ⟨Wpath, rfl⟩

/-- Restoring literal global inclusion-minimality of the source--target
separator does not remove the example: the ambient target itself is an
inclusion-minimal separator for the two displayed sources. -/
theorem target_isMinimalSeparatorFrom_source :
    CardinalInduction.IsMinimalSeparatorFrom web web.source web.target := by
  constructor
  · intro x hx p hp
    exact ⟨p.finish, p.finish_mem_support, hp.2⟩
  · intro D hDsep hDsub x hxTarget
    rcases hxTarget with (rfl | rfl)
    · have hbSource : b ∈ web.source := by simp [web]
      have hbRoof := hDsep hbSource
      have hbaTarget : web.IsTargetPathFrom b ba := by
        refine ⟨rfl, ?_⟩
        change a = a ∨ a = t
        exact Or.inl rfl
      obtain ⟨v, hvba, hvD⟩ := hbRoof ba hbaTarget
      rw [support_ba] at hvba
      rcases hvba with rfl | rfl
      · have := hDsub hvD
        simp [web] at this
      · exact hvD
    · have hbSource : b ∈ web.source := by simp [web]
      have hbRoof := hDsep hbSource
      have hbdtTarget : web.IsTargetPathFrom b bdt := by
        refine ⟨rfl, ?_⟩
        change t = a ∨ t = t
        exact Or.inr rfl
      obtain ⟨v, hvbdt, hvD⟩ := hbRoof bdt hbdtTarget
      rw [support_bdt] at hvbdt
      rcases hvbdt with rfl | rfl | rfl
      · have := hDsub hvD
        simp [web] at this
      · have := hDsub hvD
        simp [web] at this
      · exact hvD

/-- The displayed pair really is the edge family obtained by deleting the
single `X`-internal edge of the one later linkage path. -/
theorem familyEdges_Z_eq_outsideFamilyEdges_W_X :
    familyEdges Z = outsideFamilyEdges W X := by
  ext e
  rcases e with ⟨x, y⟩
  cases x <;> cases y <;>
    simp [familyEdges, Z, W, X, outsideFamilyEdges, sca, bdt, Wpath,
      FinitePath.edgeSet, Walk.edgeSet]

/-- The printed closure premise holds: the only reference member lies wholly
inside `X`. -/
theorem Y_closedUnderPaths_X : ClosedUnderPaths web Y X := by
  intro p hp _hmeet
  change p = Sum.inl ba at hp
  subst p
  intro x hx
  change x ∈ ba.support at hx
  rw [support_ba] at hx
  rcases hx with rfl | rfl
  · simp [X]
  · simp [X]

def first : Link web.graph where
  path := sca
  direction := .forward
  nontrivial := by simp [sca]

def middle : Link web.graph where
  path := ba
  direction := .backward
  nontrivial := by simp [ba]

def last : Link web.graph where
  path := bdt
  direction := .forward
  nontrivial := by simp [bdt]

private theorem compatible_first_middle (P : Prop) (hP : P) :
    CompatibleInOrder P first middle := by
  simp only [CompatibleInOrder, first, middle]
  constructor
  · intro _
    change sca.support ∩ ba.support = {a}
    rw [support_sca, support_ba]
    ext x
    cases x <;> simp
  · intro hn
    exact (hn hP).elim

private theorem compatible_middle_last (P : Prop) (hP : P) :
    CompatibleInOrder P middle last := by
  simp only [CompatibleInOrder, middle, last]
  constructor
  · intro _ x hx₁ hx₂
    rw [support_ba] at hx₁
    rw [support_bdt] at hx₂
    have : x = b := by cases x <;> simp_all
    left
    subst x
    rfl
  · intro hn
    exact (hn hP).elim

private theorem compatible_first_last (P : Prop) :
    CompatibleInOrder P first last := by
  simp only [CompatibleInOrder, first, last]
  intro x hx₁ hx₂
  rw [support_sca] at hx₁
  rw [support_bdt] at hx₂
  cases x <;> simp_all

private def traceLink (i : Fin 3) : Link web.graph :=
  if i.1 = 0 then first else if i.1 = 1 then middle else last

@[simp] private theorem traceLink_zero : traceLink 0 = first := by
  simp [traceLink]

@[simp] private theorem traceLink_one : traceLink 1 = middle := by
  simp [traceLink]

@[simp] private theorem traceLink_two : traceLink 2 = last := by
  simp [traceLink]

def trace : FiniteTrace web.graph :=
  { lastIndex := 2
    link := traceLink
    joins := by
      intro i
      have hi : i.1 = 0 ∨ i.1 = 1 := by omega
      rcases hi with hi | hi
      · have hieq : i = (0 : Fin 2) := Fin.ext hi
        subst i
        change sca.finish = ba.finish
        rfl
      · have hieq : i = (1 : Fin 2) := Fin.ext hi
        subst i
        change ba.start = bdt.start
        rfl
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

def Q : AltPath web.graph := .finite trace

@[simp] theorem Q_initial : Q.initial = s := rfl
@[simp] theorem Q_terminal : Q.terminal? = some t := rfl

private theorem sca_mem_Z : (Sum.inl sca : web.DPath) ∈ Z := by
  change Sum.inl sca = Sum.inl sca ∨ Sum.inl sca = Sum.inl bdt
  exact Or.inl rfl

private theorem bdt_mem_Z : (Sum.inl bdt : web.DPath) ∈ Z := by
  change Sum.inl bdt = Sum.inl sca ∨ Sum.inl bdt = Sum.inl bdt
  exact Or.inr rfl

private theorem ba_mem_Y : (Sum.inl ba : web.DPath) ∈ Y := by
  change Sum.inl ba = Sum.inl ba
  rfl

private theorem mem_Q_links_iff {l : Link web.graph} :
    l ∈ Q.links ↔ l = first ∨ l = middle ∨ l = last := by
  constructor
  · rintro ⟨i, rfl⟩
    change Fin 3 at i
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
    rcases hi with hi | hi | hi
    · have hieq : i = (0 : Fin 3) := Fin.ext hi
      subst i
      exact Or.inl traceLink_zero
    · have hieq : i = (1 : Fin 3) := Fin.ext hi
      subst i
      exact Or.inr (Or.inl traceLink_one)
    · have hieq : i = (2 : Fin 3) := Fin.ext hi
      subst i
      exact Or.inr (Or.inr traceLink_two)
  · rintro (rfl | rfl | rfl)
    · exact ⟨(0 : Fin 3), traceLink_zero⟩
    · exact ⟨(1 : Fin 3), traceLink_one⟩
    · exact ⟨(2 : Fin 3), traceLink_two⟩

theorem t_not_vertexSet_Y : t ∉ web.vertexSet Y := by
  rintro ⟨p, hp, ht⟩
  change p = Sum.inl ba at hp
  subst p
  change t ∈ ba.support at ht
  rw [support_ba] at ht
  simp at ht

theorem s_not_vertexSet_Y : s ∉ web.vertexSet Y := by
  rintro ⟨p, hp, hs⟩
  change p = Sum.inl ba at hp
  subst p
  change s ∈ ba.support at hs
  rw [support_ba] at hs
  simp at hs

theorem Q_isBracketAlternating : IsBracketAlternating Z Y Q := by
  constructor
  · refine ⟨Y_isWarp, ?_, ?_, ?_⟩
    · intro l hl hback
      rw [mem_Q_links_iff] at hl
      rcases hl with rfl | rfl | rfl
      · simp [first] at hback
      · exact ⟨Sum.inl ba, ba_mem_Y, ba.isSubpathOf_self⟩
      · simp [last] at hback
    · intro _hforward
      exact s_not_vertexSet_Y
    · intro v hv _hforward
      rw [Q_terminal] at hv
      have hvt : v = t := (Option.some.inj hv).symm
      subst v
      exact t_not_vertexSet_Y
  · intro l hl hforward
    rw [mem_Q_links_iff] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨Sum.inl sca, sca_mem_Z, sca.isSubpathOf_self⟩
    · simp [middle] at hforward
    · exact ⟨Sum.inl bdt, bdt_mem_Z, bdt.isSubpathOf_self⟩

private theorem Q_backwardEdges :
    Q.directionEdges .backward = ba.edgeSet := by
  ext e
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨l, hl, hback, he⟩
    rw [mem_Q_links_iff] at hl
    rcases hl with rfl | rfl | rfl
    · simp [first] at hback
    · exact he
    · simp [last] at hback
  · intro he
    exact ⟨middle, by
      rw [mem_Q_links_iff]
      exact Or.inr (Or.inl rfl), rfl, he⟩

/-- The displayed route is a genuine safe `[Z,Y]`-alternating path, not
merely an arbitrary three-link trace. -/
theorem Q_isBracketSafe : IsBracketSafe Z Y Q := by
  apply isBracketSafe_of_intervals Z_isWarp Z_finite Q_isBracketAlternating
  intro p hpY
  rw [Q_backwardEdges]
  exact fragment_inter_isEdgeInterval Y_isWarp ba
    ⟨Sum.inl ba, ba_mem_Y, ba.isSubpathOf_self⟩ p hpY

/-- Both vertices traversed by the backward reference block are internal
closed-set contacts of the safe route. -/
theorem a_mem_Q_interior_X :
    a ∈ hammockInterior s (.vertex t) Q ∩ X := by
  constructor
  · constructor
    · change a ∈ trace.vertexSet
      exact Set.mem_iUnion.2 ⟨(0 : Fin 3), by
        change a ∈ (traceLink 0).path.support
        rw [traceLink_zero]
        change a ∈ sca.support
        rw [support_sca]
        simp⟩
    · simp [hammockEndpoints]
  · simp [X]

theorem b_mem_Q_interior_X :
    b ∈ hammockInterior s (.vertex t) Q ∩ X := by
  constructor
  · constructor
    · change b ∈ trace.vertexSet
      exact Set.mem_iUnion.2 ⟨(1 : Fin 3), by
        change b ∈ (traceLink 1).path.support
        rw [traceLink_one]
        change b ∈ ba.support
        rw [support_ba]
        simp⟩
    · simp [hammockEndpoints]
  · simp [X]

/-- Reference-path closure therefore does not imply the interior-disjointness
premise of Claim 2, even for the safe route selected above. -/
theorem Q_not_interiorDisjoint_X :
    ¬ Disjoint (hammockInterior s (.vertex t) Q) X := by
  rw [Set.not_disjoint_iff]
  exact ⟨a, a_mem_Q_interior_X.1, a_mem_Q_interior_X.2⟩

theorem Y_initial_subset_Z : web.initialSet Y ⊆ web.initialSet Z := by
  rintro x ⟨p, hp, hpx⟩
  change p = Sum.inl ba at hp
  subst p
  have hxb : x = b := hpx.symm
  subst x
  exact ⟨Sum.inl bdt, bdt_mem_Z, rfl⟩

/-- The two ordinary boundary conditions used by the internal-cut version of
Theorem 4.12 both hold in the example. -/
theorem Z_boundaryAligned_Y : BoundaryAligned Z Y := by
  constructor
  · rintro x ⟨⟨p, hp, hpx⟩, ⟨q, hq, hxq⟩⟩
    change q = Sum.inl ba at hq
    subst q
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · change sca.start = x at hpx
      subst x
      change s ∈ ba.support at hxq
      rw [support_ba] at hxq
      simp at hxq
    · change bdt.start = x at hpx
      subst x
      exact ⟨Sum.inl ba, ba_mem_Y, rfl⟩
  · rintro x ⟨⟨p, hp, hpx⟩, ⟨q, hq, hxq⟩⟩
    change q = Sum.inl ba at hq
    subst q
    simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · change some sca.finish = some x at hpx
      have hxa : x = a := (Option.some.inj hpx).symm
      subst x
      exact ⟨Sum.inl ba, ba_mem_Y, rfl⟩
    · change some bdt.finish = some x at hpx
      have hxt : x = t := (Option.some.inj hpx).symm
      subst x
      change t ∈ ba.support at hxq
      rw [support_ba] at hxq
      simp at hxq

theorem s_initial_Z : s ∈ web.initialSet Z :=
  ⟨Sum.inl sca, sca_mem_Z, rfl⟩

theorem s_not_initial_Y : s ∉ web.initialSet Y := by
  rintro ⟨p, hp, hps⟩
  change p = Sum.inl ba at hp
  subst p
  change b = s at hps
  cases hps

theorem t_terminal_Z : t ∈ web.terminalFrontier Z :=
  ⟨Sum.inl bdt, bdt_mem_Z, rfl⟩

private theorem uncovered_initial_eq_s
    (z : {x // x ∈ web.initialSet Z \ web.initialSet Y}) : z.1 = s := by
  rcases z.property.1 with ⟨p, hp, hpz⟩
  simp only [Z, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact hpz.symm
  · exfalso
    apply z.property.2
    have hzb : z.1 = b := hpz.symm
    exact ⟨Sum.inl ba, ba_mem_Y, hzb.symm⟩

/-- Thus the bad route is itself a perfectly valid possible output of the
simultaneous-assignment theorem.  Terminal injectivity is vacuous because
there is one uncovered source. -/
noncomputable def assignment : SimultaneousAssignment Z Y where
  assigned _ := Q
  starts_at z := by simpa using (uncovered_initial_eq_s z).symm
  safe _ := Q_isBracketSafe.isSafe
  leaving _ := Or.inr ⟨t, Q_terminal, t_not_vertexSet_Y⟩
  maximal _ := Or.inr ⟨t, ⟨t_terminal_Z, t_not_vertexSet_Y⟩, Q_terminal⟩
  finite_terminals_injective := by
    intro z₁ z₂ _v _h₁ _h₂
    apply Subtype.ext
    exact (uncovered_initial_eq_s z₁).trans
      (uncovered_initial_eq_s z₂).symm

/-- Consequently `ClosedUnderPaths web Y X`, boundary alignment, finite
character, and a valid Theorem-4.12 assignment do not imply the Claim-2
closure context for that assignment. -/
theorem assignment_has_no_Claim2_closureContext
    (before innerRoof outerRoof : Set Vertex) :
    ¬ AssignmentClosureContext assignment X before innerRoof outerRoof := by
  intro h
  let source : {x // x ∈ web.initialSet Z \ web.initialSet Y} :=
    ⟨s, s_initial_Z, s_not_initial_Y⟩
  have hterm : (assignment.assigned source).terminal? = some t := Q_terminal
  have hdisjoint := h.interior_disjoint_finite source t hterm
  apply Q_not_interiorDisjoint_X
  simpa [assignment, source] using hdisjoint

end Erdos599.Blueprint.LinkageBlueprint.EndpointCleanAudit
