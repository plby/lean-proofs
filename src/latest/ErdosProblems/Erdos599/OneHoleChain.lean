/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleSearch
import Mathlib.Data.List.Duplicate

/-!
# Loop erasure for finite residual chains

The contact-marked residual search is expressed with
`Relation.ReflTransGen`.  This file supplies a reusable directed loop-erasure
lemma: every finite reflexive-transitive chain has a vertex-simple list
representative with the same ordered endpoints.  No symmetry of the relation
is assumed.
-/

namespace Erdos599
namespace DWeb

open Alternating

universe u

/-- Endpoint-aware list representation of a finite directed chain. -/
def ChainEndpoints {alpha : Type u} (r : alpha → alpha → Prop)
    (a b : alpha) (l : List alpha) : Prop :=
  l ≠ [] ∧ l.IsChain r ∧ l.head? = some a ∧ l.getLast? = some b

/-- A chain has no forward chord when no relation edge can skip a nonempty
block of intermediate vertices.  This is the normalization supplied by a
shortest list realization of reflexive-transitive reachability. -/
def ChainHasNoForwardChord {alpha : Type u}
    (r : alpha → alpha → Prop) (l : List alpha) : Prop :=
  ∀ (pre mid post : List alpha) (x y : alpha),
    l = pre ++ x :: mid ++ y :: post → mid ≠ [] → ¬ r x y

/-- A forward chord produces a strictly shorter chain with the same ordered
endpoints. -/
theorem exists_shorter_chain_of_forwardChord
    {alpha : Type u} {r : alpha → alpha → Prop}
    {l pre mid post : List alpha} {x y : alpha}
    (hl : l = pre ++ x :: mid ++ y :: post)
    (hchain : l.IsChain r) (hmid : mid ≠ []) (hxy : r x y) :
    ∃ l' : List alpha, l' ≠ [] ∧ l'.IsChain r ∧
      l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧
      l'.length < l.length := by
  let l' := pre ++ x :: y :: post
  have horig : (pre ++ x :: mid ++ y :: post).IsChain r := hl ▸ hchain
  have hleft : (pre ++ [x]).IsChain r := by
    have h := horig
    rw [show pre ++ x :: mid ++ y :: post =
      (pre ++ [x]) ++ (mid ++ y :: post) by simp] at h
    exact h.left_of_append
  have hright : (y :: post).IsChain r := by
    have h := horig
    rw [show pre ++ x :: mid ++ y :: post =
      (pre ++ x :: mid) ++ (y :: post) by simp] at h
    exact h.right_of_append
  refine ⟨l', ?_, ?_, ?_, ?_, ?_⟩
  · simp [l']
  · simpa [l'] using
      (List.isChain_append_cons_cons.mpr ⟨hleft, hxy, hright⟩)
  · rw [hl]
    cases pre <;> simp [l']
  · rw [hl]
    rw [show l' = (pre ++ [x]) ++ (y :: post) by simp [l'],
      show pre ++ x :: mid ++ y :: post =
        (pre ++ x :: mid) ++ (y :: post) by simp,
      List.getLast?_append_of_ne_nil (pre ++ [x])
        (by simp : y :: post ≠ []),
      List.getLast?_append_of_ne_nil (pre ++ x :: mid)
        (by simp : y :: post ≠ [])]
  · rw [hl]
    have hmidpos : 0 < mid.length := by
      have hne : mid.length ≠ 0 := by
        simpa using hmid
      omega
    simp only [l', List.length_append, List.length_cons]
    omega

/-- Removing a loop from a directed chain preserves both endpoints and
strictly decreases its length. -/
theorem exists_shorter_chain_of_duplicate
    {alpha : Type u} {r : alpha → alpha → Prop}
    {x : alpha} {l : List alpha}
    (hdup : List.Duplicate x l) (hchain : l.IsChain r) :
    ∃ l' : List alpha, l' ≠ [] ∧ l'.IsChain r ∧
      l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧
      l'.length < l.length := by
  induction hdup with
  | @cons_mem tail hx =>
      obtain ⟨pre, post, htail⟩ := List.append_of_mem hx
      subst tail
      let l' := x :: post
      refine ⟨l', by simp [l'], ?_, ?_, ?_, ?_⟩
      · apply hchain.suffix
        exact ⟨x :: pre, by simp [l', List.cons_append]⟩
      · simp [l']
      · rw [show x :: (pre ++ x :: post) =
          (x :: pre) ++ (x :: post) by simp]
        rw [List.getLast?_append_of_ne_nil (x :: pre)
          (by simp : x :: post ≠ [])]
      · simp [l']
  | @cons_duplicate y tail hdup ih =>
      obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'len⟩ :=
        ih hchain.tail
      refine ⟨y :: l', by simp, ?_, ?_, ?_, ?_⟩
      · apply hl'chain.cons
        intro z hz
        apply hchain.rel_head?
        rw [← hl'head]
        exact hz
      · simp
      · rw [show y :: l' = [y] ++ l' by rfl,
          List.getLast?_append_of_ne_nil [y] hl'ne]
        rw [show y :: tail = [y] ++ tail by rfl,
          List.getLast?_append_of_ne_nil [y] hdup.ne_nil]
        exact hl'last
      · simp only [List.length_cons]
        omega

/-- A shortest finite chain is simple; equivalently every
reflexive-transitive reachability witness has a `Nodup` list realization. -/
theorem exists_nodup_chain_of_reflTransGen
    {alpha : Type u} {r : alpha → alpha → Prop}
    {a b : alpha} (h : Relation.ReflTransGen r a b) :
    ∃ l : List alpha, ChainEndpoints r a b l ∧ l.Nodup := by
  classical
  obtain ⟨l0, hl0ne, hl0chain, hl0head, hl0last⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  let P : ℕ → Prop := fun n ↦
    ∃ l : List alpha, ChainEndpoints r a b l ∧ l.length = n
  have hP : ∃ n, P n := by
    refine ⟨l0.length, l0, ?_, rfl⟩
    refine ⟨hl0ne, hl0chain, ?_, ?_⟩
    · rw [List.head?_eq_some_head hl0ne, hl0head]
    · rw [List.getLast?_eq_some_getLast hl0ne, hl0last]
  let n := Nat.find hP
  obtain ⟨l, hl, hlen⟩ := Nat.find_spec hP
  refine ⟨l, hl, ?_⟩
  by_contra hnot
  obtain ⟨x, hxdup⟩ :=
    List.exists_duplicate_iff_not_nodup.mpr hnot
  obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'len⟩ :=
    exists_shorter_chain_of_duplicate hxdup hl.2.1
  have hl'endpoint : ChainEndpoints r a b l' := by
    refine ⟨hl'ne, hl'chain, ?_, ?_⟩
    · rw [hl'head]
      exact hl.2.2.1
    · rw [hl'last]
      exact hl.2.2.2
  have hmin : n ≤ l'.length :=
    Nat.find_min' hP ⟨l', hl'endpoint, rfl⟩
  omega

/-- A shortest realization is simultaneously state-simple and chordless. -/
theorem exists_nodup_noForwardChord_chain_of_reflTransGen
    {alpha : Type u} {r : alpha → alpha → Prop}
    {a b : alpha} (h : Relation.ReflTransGen r a b) :
    ∃ l : List alpha, ChainEndpoints r a b l ∧ l.Nodup ∧
      ChainHasNoForwardChord r l := by
  classical
  obtain ⟨l0, hl0ne, hl0chain, hl0head, hl0last⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  let P : ℕ → Prop := fun n ↦
    ∃ l : List alpha, ChainEndpoints r a b l ∧ l.length = n
  have hP : ∃ n, P n := by
    refine ⟨l0.length, l0, ?_, rfl⟩
    refine ⟨hl0ne, hl0chain, ?_, ?_⟩
    · rw [List.head?_eq_some_head hl0ne, hl0head]
    · rw [List.getLast?_eq_some_getLast hl0ne, hl0last]
  let n := Nat.find hP
  obtain ⟨l, hl, hlen⟩ := Nat.find_spec hP
  have hminimal : ∀ {l' : List alpha},
      ChainEndpoints r a b l' → l.length ≤ l'.length := by
    intro l' hl'
    have hmin : n ≤ l'.length :=
      Nat.find_min' hP ⟨l', hl', rfl⟩
    omega
  refine ⟨l, hl, ?_, ?_⟩
  · by_contra hnot
    obtain ⟨x, hxdup⟩ :=
      List.exists_duplicate_iff_not_nodup.mpr hnot
    obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'len⟩ :=
      exists_shorter_chain_of_duplicate hxdup hl.2.1
    have hl'endpoint : ChainEndpoints r a b l' := by
      refine ⟨hl'ne, hl'chain, ?_, ?_⟩
      · rw [hl'head]
        exact hl.2.2.1
      · rw [hl'last]
        exact hl.2.2.2
    exact (Nat.not_lt_of_ge (hminimal hl'endpoint)) hl'len
  · intro pre mid post x y hdecomp hmid hxy
    obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'len⟩ :=
      exists_shorter_chain_of_forwardChord hdecomp hl.2.1 hmid hxy
    have hl'endpoint : ChainEndpoints r a b l' := by
      refine ⟨hl'ne, hl'chain, ?_, ?_⟩
      · rw [hl'head]
        exact hl.2.2.1
      · rw [hl'last]
        exact hl.2.2.2
    exact (Nat.not_lt_of_ge (hminimal hl'endpoint)) hl'len

/-- Specialized simple-list realization of a marked one-hole residual
reachability witness. -/
theorem exists_nodup_markedRoute
    {V : Type u} (G : DWeb V) (J : Set G.DPath)
    {a b : V}
    (h : Relation.ReflTransGen (G.OneHoleMarkedStep J)
      (.ready a) (.ready b)) :
    ∃ l : List (OneHoleResidualState V),
      ChainEndpoints (G.OneHoleMarkedStep J) (.ready a) (.ready b) l ∧
        l.Nodup :=
  exists_nodup_chain_of_reflTransGen h

/-- A shortest marked residual route, with both repeated states and forward
chords erased. -/
def IsReducedMarkedRoute
    {V : Type u} (G : DWeb V) (J : Set G.DPath)
    (a b : V) (l : List (OneHoleResidualState V)) : Prop :=
  ChainEndpoints (G.OneHoleMarkedStep J) (.ready a) (.ready b) l ∧
    l.Nodup ∧ ChainHasNoForwardChord (G.OneHoleMarkedStep J) l

/-! ## Chosen direction of a marked transition -/

/-- The forward interpretation of a marked transition.  When a ready-to-
ready transition admits both residual interpretations, forward has priority;
this makes the set of edges toggled by a finite route deterministic. -/
def OneHoleChosenForwardStep
    {V : Type u} (G : DWeb V) (J : Set G.DPath) :
    OneHoleResidualState V → OneHoleResidualState V → Prop
  | .ready x, .ready y =>
      G.graph.Adj x y ∧ (x, y) ∉ familyEdges J ∧ y ∉ G.vertexSet J
  | .ready x, .pending y =>
      G.graph.Adj x y ∧ (x, y) ∉ familyEdges J ∧ y ∈ G.vertexSet J
  | .pending _, _ => False

/-- The complementary backward interpretation of a marked transition. -/
def OneHoleChosenBackwardStep
    {V : Type u} (G : DWeb V) (J : Set G.DPath) :
    OneHoleResidualState V → OneHoleResidualState V → Prop
  | .ready x, .ready y =>
      ¬ OneHoleChosenForwardStep G J (.ready x) (.ready y) ∧
        (y, x) ∈ familyEdges J
  | .pending y, .ready x => (x, y) ∈ familyEdges J
  | _, .pending _ => False

theorem oneHoleMarkedStep_iff_chosenDirection
    {V : Type u} (G : DWeb V) (J : Set G.DPath)
    (s t : OneHoleResidualState V) :
    G.OneHoleMarkedStep J s t ↔
      OneHoleChosenForwardStep G J s t ∨
        OneHoleChosenBackwardStep G J s t := by
  cases s <;> cases t <;>
    simp only [OneHoleMarkedStep, OneHoleChosenForwardStep,
      OneHoleChosenBackwardStep] <;> tauto

theorem oneHoleChosenDirection_exclusive
    {V : Type u} (G : DWeb V) (J : Set G.DPath)
    {s t : OneHoleResidualState V}
    (hforward : OneHoleChosenForwardStep G J s t)
    (hbackward : OneHoleChosenBackwardStep G J s t) : False := by
  cases s <;> cases t <;>
    simp only [OneHoleChosenForwardStep, OneHoleChosenBackwardStep] at *
  exact hbackward.1 hforward

private theorem Walk.not_self_mem_edgeSet_of_isPath
    {V : Type u} {D : Digraph V} {a b x : V}
    (p : DirectedPath.Walk D a b) (hp : p.IsPath) :
    (x, x) ∉ p.edgeSet := by
  induction p with
  | nil => simp [DirectedPath.Walk.edgeSet]
  | @cons a c b hac p ih =>
      intro hxx
      simp only [DirectedPath.Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hxx
      rcases hxx with hhead | htail
      · have hax : x = a := congrArg Prod.fst hhead
        have hcx : x = c := congrArg Prod.snd hhead
        have hacEq : a = c := hax.symm.trans hcx
        subst c
        subst x
        exact (List.nodup_cons.mp hp).1 p.start_mem_support
      · exact ih hp.tail htail

private theorem not_self_mem_familyEdges
    {V : Type u} {G : DWeb V} {J : Set G.DPath} {x : V} :
    (x, x) ∉ familyEdges J := by
  intro hxx
  simp only [familyEdges, Set.mem_iUnion] at hxx
  rcases hxx with ⟨p, _hpJ, hxp⟩
  cases p with
  | inl p => exact Walk.not_self_mem_edgeSet_of_isPath p.walk p.isPath hxp
  | inr r =>
      rcases hxp with ⟨n, heq⟩
      have hsame : r n = r (n + 1) := by
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        exact hfst.symm.trans hsnd
      exact (Nat.ne_of_lt (Nat.lt_succ_self n)) (r.injective hsame)

theorem IsReducedMarkedRoute.not_ready_before_pending
    {V : Type u} {G : DWeb V} {J : Set G.DPath}
    {a b x : V} {l pre mid post : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l)
    (hdecomp : l = pre ++ .ready x :: mid ++ .pending x :: post) : False := by
  cases post with
  | nil =>
    have hlast := hl.1.2.2.2
    rw [hdecomp] at hlast
    have hlast' :
        (pre ++ OneHoleResidualState.ready x :: mid ++
          [OneHoleResidualState.pending x]).getLast? =
          some (OneHoleResidualState.pending x) := by
      rw [show pre ++ OneHoleResidualState.ready x :: mid ++
          [OneHoleResidualState.pending x] =
        (pre ++ OneHoleResidualState.ready x :: mid) ++
          [OneHoleResidualState.pending x] by simp,
        List.getLast?_append_of_ne_nil
          (pre ++ OneHoleResidualState.ready x :: mid) (by simp)]
      simp
    rw [hlast'] at hlast
    cases hlast
  | cons s post =>
    have hsuffix :
        (OneHoleResidualState.pending x :: s :: post).IsChain
          (G.OneHoleMarkedStep J) := by
      have hchain := hl.1.2.1
      rw [hdecomp] at hchain
      have h := hchain
      rw [show pre ++ .ready x :: mid ++ .pending x :: s :: post =
        (pre ++ .ready x :: mid) ++ (.pending x :: s :: post) by simp] at h
      exact h.right_of_append
    have hstep : G.OneHoleMarkedStep J (.pending x) s :=
      (List.isChain_cons_cons.mp hsuffix).1
    cases s with
    | pending y => exact hstep.elim
    | ready y =>
        have hdirect : G.OneHoleMarkedStep J (.ready x) (.ready y) :=
          Or.inr hstep
        apply hl.2.2 pre (mid ++ [.pending x]) post (.ready x) (.ready y)
        · simpa [List.append_assoc] using hdecomp
        · simp
        · exact hdirect

/-- Two distinct ordered occurrences in a reduced route cannot carry the
same marked state.  This decomposition form is convenient when reasoning
about equality of their projected vertices. -/
theorem IsReducedMarkedRoute.ne_of_ordered_occurrences
    {V : Type u} {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l pre mid post : List (OneHoleResidualState V)}
    {s t : OneHoleResidualState V}
    (hl : IsReducedMarkedRoute G J a b l)
    (hdecomp : l = pre ++ s :: mid ++ t :: post) : s ≠ t := by
  intro hst
  subst t
  let suffix : List (OneHoleResidualState V) := s :: mid ++ s :: post
  have hdup : List.Duplicate s suffix := by
    apply List.Duplicate.cons_mem
    simp [suffix]
  have hsuffix : List.Sublist suffix l := by
    rw [hdecomp]
    simpa [suffix, List.append_assoc] using
      (List.sublist_append_right pre suffix)
  exact (hdup.mono_sublist hsuffix).not_nodup hl.2.1

/-- The only possible repeated projected vertex in traversal order is a
pending occurrence followed later by the ready occurrence of that vertex.
Same-tag repetitions contradict state simplicity, while ready-before-
pending is excluded by chordlessness. -/
theorem IsReducedMarkedRoute.ordered_projected_duplicate
    {V : Type u} {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l pre mid post : List (OneHoleResidualState V)}
    {s t : OneHoleResidualState V}
    (hl : IsReducedMarkedRoute G J a b l)
    (hdecomp : l = pre ++ s :: mid ++ t :: post)
    (hvertex : s.vertex = t.vertex) :
    ∃ x, s = .pending x ∧ t = .ready x := by
  cases s with
  | ready x =>
      cases t with
      | ready y =>
          have hxy : x = y := hvertex
          subst y
          exact False.elim (hl.ne_of_ordered_occurrences hdecomp rfl)
      | pending y =>
          have hxy : x = y := hvertex
          subst y
          exact False.elim (hl.not_ready_before_pending hdecomp)
  | pending x =>
      cases t with
      | ready y =>
          have hxy : x = y := hvertex
          subst y
          exact ⟨x, rfl, rfl⟩
      | pending y =>
          have hxy : x = y := hvertex
          subst y
          exact False.elim (hl.ne_of_ordered_occurrences hdecomp rfl)

/-- If the ready copy of a previously pending vertex has a ready successor,
the chosen interpretation of that departure is forward.  A backward
departure would use the same incoming old-warp edge as the mandatory
cancellation immediately following the pending copy, forcing a repeated
ready state. -/
theorem IsReducedMarkedRoute.chosenForward_ready_ready_of_pending_before
    {V : Type u} {G : DWeb V} {J : Set G.DPath}
    {a b x y : V} {l pre mid post : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    (hdecomp : l = pre ++ .pending x :: mid ++ .ready x :: .ready y :: post) :
    OneHoleChosenForwardStep G J (.ready x) (.ready y) := by
  have hout : G.OneHoleMarkedStep J (.ready x) (.ready y) := by
    apply (List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.1.2.1)
    show l = (pre ++ .pending x :: mid) ++ .ready x :: .ready y :: post
    simpa [List.append_assoc] using hdecomp
  rcases (oneHoleMarkedStep_iff_chosenDirection G J _ _).1 hout with
    hforward | hbackward
  · exact hforward
  · have hyx : (y, x) ∈ familyEdges J := hbackward.2
    cases mid with
    | nil =>
        have hxx : (x, x) ∈ familyEdges J := by
          have hin : G.OneHoleMarkedStep J (.pending x) (.ready x) := by
            apply (List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.1.2.1)
            show l = pre ++ .pending x :: .ready x :: .ready y :: post
            simpa [List.append_assoc] using hdecomp
          exact hin
        exact False.elim (not_self_mem_familyEdges hxx)
    | cons s mid =>
        have hin : G.OneHoleMarkedStep J (.pending x) s := by
          have hchain := hl.1.2.1
          rw [hdecomp] at hchain
          have hsuffix :
              (OneHoleResidualState.pending x :: s :: mid ++
                .ready x :: .ready y :: post).IsChain
                (G.OneHoleMarkedStep J) := by
            have h := hchain
            rw [show pre ++ .pending x :: s :: mid ++
                .ready x :: .ready y :: post =
              pre ++ (.pending x :: s :: mid ++
                .ready x :: .ready y :: post) by simp] at h
            exact h.right_of_append
          exact (List.isChain_cons_cons.mp hsuffix).1
        cases s with
        | pending z => exact False.elim hin
        | ready z =>
            have hzx : (z, x) ∈ familyEdges J := hin
            have hzy : z = y := familyEdges_in_unique hJ.isWarp hzx hyx
            subst z
            let suffix : List (OneHoleResidualState V) :=
              .ready y :: mid ++ .ready x :: .ready y :: post
            have hdup : List.Duplicate (.ready y) suffix := by
              apply List.Duplicate.cons_mem
              simp [suffix]
            have hsuffix : List.Sublist suffix l := by
              rw [hdecomp]
              simpa [suffix, List.append_assoc] using
                (List.sublist_append_right
                  (pre ++ [OneHoleResidualState.pending x]) suffix)
            exact ((hdup.mono_sublist hsuffix).not_nodup hl.2.1).elim

/-- Specialized state-simple, chordless realization of marked residual
reachability. -/
theorem exists_reduced_markedRoute
    {V : Type u} (G : DWeb V) (J : Set G.DPath)
    {a b : V}
    (h : Relation.ReflTransGen (G.OneHoleMarkedStep J)
      (.ready a) (.ready b)) :
    ∃ l : List (OneHoleResidualState V),
      IsReducedMarkedRoute G J a b l :=
  exists_nodup_noForwardChord_chain_of_reflTransGen h

end DWeb
end Erdos599
