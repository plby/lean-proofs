/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingPrefixContacts
import ErdosProblems.Erdos599.FiniteRelationTrace
import Mathlib.Tactic.FinCases

/-!
# A raw matching prefix need not be an alternating trace

The bipartite matching orbit remembers all reference contacts, but its
projection need not satisfy the collision rules of an alternating trace.
This is the five-vertex obstruction recorded in the proof audit: the first
forward edge and a later, non-adjacent backward edge meet at `x`.

Consequently an orientation-aware compiler cannot merely preserve all
maximal raw runs in their original order.  A genuine source Rule-2
normalization has to change the run decomposition (and prove its owner
interval invariant); ordinary chronological erasure is not such a proof.
-/

namespace Erdos599
namespace TwoWarpMatchingRawRunCompatibilityObstruction

open Set DirectedPath Alternating

inductive Vertex
  | s | x | a | b | t
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj u v :=
    (u = s ∧ v = x) ∨ (u = x ∧ v = t) ∨ (u = a ∧ v = b) ∨
      (u = a ∧ v = x) ∨ (u = x ∧ v = b)

def sx : FinitePath graph where
  start := s
  finish := x
  walk := .cons (by simp [graph]) .nil
  isPath := by simp [Walk.IsPath, Walk.support]

def xt : FinitePath graph where
  start := x
  finish := t
  walk := .cons (by simp [graph]) .nil
  isPath := by simp [Walk.IsPath, Walk.support]

def ab : FinitePath graph where
  start := a
  finish := b
  walk := .cons (by simp [graph]) .nil
  isPath := by simp [Walk.IsPath, Walk.support]

def ax : FinitePath graph where
  start := a
  finish := x
  walk := .cons (by simp [graph]) .nil
  isPath := by simp [Walk.IsPath, Walk.support]

def xb : FinitePath graph where
  start := x
  finish := b
  walk := .cons (by simp [graph]) .nil
  isPath := by simp [Walk.IsPath, Walk.support]

def sxt : FinitePath graph where
  start := s
  finish := t
  walk := Walk.cons (u := s) (v := x) (w := t) (by simp [graph])
    (Walk.cons (u := x) (v := t) (w := t) (by simp [graph]) Walk.nil)
  isPath := by
    change [s, x, t].Nodup
    simp

def axb : FinitePath graph where
  start := a
  finish := b
  walk := Walk.cons (u := a) (v := x) (w := b) (by simp [graph])
    (Walk.cons (u := x) (v := b) (w := b) (by simp [graph]) Walk.nil)
  isPath := by
    change [a, x, b].Nodup
    simp

@[simp] theorem sx_support : sx.support = {s, x} := by
  ext v
  change v ∈ [s, x] ↔ _
  simp

@[simp] theorem xt_support : xt.support = {x, t} := by
  ext v
  change v ∈ [x, t] ↔ _
  simp

@[simp] theorem ab_support : ab.support = {a, b} := by
  ext v
  change v ∈ [a, b] ↔ _
  simp

@[simp] theorem ax_support : ax.support = {a, x} := by
  ext v
  change v ∈ [a, x] ↔ _
  simp

@[simp] theorem xb_support : xb.support = {x, b} := by
  ext v
  change v ∈ [x, b] ↔ _
  simp

@[simp] theorem sxt_support : sxt.support = {s, x, t} := by
  ext v
  simp [FinitePath.support, sxt, Walk.support]

@[simp] theorem axb_support : axb.support = {a, x, b} := by
  ext v
  simp [FinitePath.support, axb, Walk.support]

abbrev web : DWeb Vertex where
  graph := graph
  source := {s, a}
  target := {t, b}

def W : Set web.DPath := {Sum.inl sxt, Sum.inl ab}

def Y : Set web.DPath := {Sum.inl axb}

theorem W_isWarp : web.IsWarp W := by
  intro p hp q hq hpq
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint sxt.support ab.support
    rw [sxt_support, ab_support]
    simp [Set.disjoint_left]
  · change Disjoint ab.support sxt.support
    rw [ab_support, sxt_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim

theorem Y_isWarp : web.IsWarp Y := by
  intro p hp q hq hpq
  change p = Sum.inl axb at hp
  change q = Sum.inl axb at hq
  exact (hpq (hp.trans hq.symm)).elim

theorem Y_initialSet_subset_W : web.initialSet Y ⊆ web.initialSet W := by
  rintro v ⟨p, hp, rfl⟩
  change p = Sum.inl axb at hp
  subst p
  refine ⟨Sum.inl ab, ?_, ?_⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))
  rfl

theorem Y_terminalFrontier_subset_W :
    web.terminalFrontier Y ⊆ web.terminalFrontier W := by
  rintro v ⟨p, hp, hpv⟩
  change p = Sum.inl axb at hp
  subst p
  have hv : v = b := by simpa [axb] using Option.some.inj hpv.symm
  subst v
  refine ⟨Sum.inl ab, ?_, rfl⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))

/-- The five raw links really are fragments of the two endpoint-aligned
warps displayed above. -/
theorem raw_links_have_warp_labels :
    IsFragmentOf sx W ∧ IsFragmentOf ax Y ∧ IsFragmentOf ab W ∧
      IsFragmentOf xb Y ∧ IsFragmentOf xt W := by
  refine ⟨⟨.inl sxt, by simp [W], ?_⟩,
    ⟨.inl axb, by simp [Y], ?_⟩, ⟨.inl ab, by simp [W], ?_⟩,
    ⟨.inl axb, by simp [Y], ?_⟩, ⟨.inl sxt, by simp [W], ?_⟩⟩
  · constructor <;> intro z hz
    · change z ∈ sx.support at hz
      change z ∈ sxt.support
      rw [sx_support] at hz
      rw [sxt_support]
      aesop
    · change z ∈ sx.edgeSet at hz
      change z ∈ sxt.edgeSet
      simp [sx, sxt, FinitePath.edgeSet, Walk.edgeSet] at hz ⊢
      aesop
  · constructor <;> intro z hz
    · change z ∈ ax.support at hz
      change z ∈ axb.support
      rw [ax_support] at hz
      rw [axb_support]
      aesop
    · change z ∈ ax.edgeSet at hz
      change z ∈ axb.edgeSet
      simp [ax, axb, FinitePath.edgeSet, Walk.edgeSet] at hz ⊢
      aesop
  · exact FinitePath.isSubpathOf_self ab
  · constructor <;> intro z hz
    · change z ∈ xb.support at hz
      change z ∈ axb.support
      rw [xb_support] at hz
      rw [axb_support]
      aesop
    · change z ∈ xb.edgeSet at hz
      change z ∈ axb.edgeSet
      simp [xb, axb, FinitePath.edgeSet, Walk.edgeSet] at hz ⊢
      aesop
  · constructor <;> intro z hz
    · change z ∈ xt.support at hz
      change z ∈ sxt.support
      rw [xt_support] at hz
      rw [sxt_support]
      aesop
    · change z ∈ xt.edgeSet at hz
      change z ∈ sxt.edgeSet
      simp [xt, sxt, FinitePath.edgeSet, Walk.edgeSet] at hz ⊢
      aesop

private theorem exclusive_WY_sx :
    TwoWarpMatchingTraversal.Exclusive W Y s x := by
  constructor
  · exact TwoWarpMatchingTraversal.matchingEdge_actual (by
      simp [W, familyEdges, sxt, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, axb, FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_YW_ax :
    TwoWarpMatchingTraversal.Exclusive Y W a x := by
  constructor
  · exact TwoWarpMatchingTraversal.matchingEdge_actual (by
      simp [Y, familyEdges, axb, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [W, familyEdges, sxt, ab, FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_WY_ab :
    TwoWarpMatchingTraversal.Exclusive W Y a b := by
  constructor
  · exact TwoWarpMatchingTraversal.matchingEdge_actual (by
      simp [W, familyEdges, ab, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, axb, FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_YW_xb :
    TwoWarpMatchingTraversal.Exclusive Y W x b := by
  constructor
  · exact TwoWarpMatchingTraversal.matchingEdge_actual (by
      simp [Y, familyEdges, axb, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [W, familyEdges, sxt, ab, FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_WY_xt :
    TwoWarpMatchingTraversal.Exclusive W Y x t := by
  constructor
  · exact TwoWarpMatchingTraversal.matchingEdge_actual (by
      simp [W, familyEdges, sxt, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, axb, FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

open TwoWarpMatchingTraversal

/-- The exact simple port prefix of the two matchings. -/
def rawPort (i : Fin 6) : Port Vertex :=
  match i.1 with
  | 0 => .inl s
  | 1 => .inr x
  | 2 => .inl a
  | 3 => .inr b
  | 4 => .inl x
  | _ => .inr t

def rawPrefix : FinitePortPrefix W Y s where
  lastIndex := 5
  positive := by omega
  port := rawPort
  starts := by simp [rawPort]
  steps := by
    intro i
    fin_cases i <;> simp [rawPort, TwoWarpMatchingTraversal.Step,
      exclusive_WY_sx, exclusive_YW_ax, exclusive_WY_ab,
      exclusive_YW_xb, exclusive_WY_xt]
  injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rawPort] at hij ⊢

/-- With `X={s,t}` this is a genuine distinct first-return outcome; the
repeated contact `x` lies strictly outside `X`. -/
def rawFirstReturn : ForwardOrbitOutcome W Y ({s, t} : Set Vertex) s :=
  .firstReturn rawPrefix
    (by
      intro i hipos hlast
      fin_cases i <;> simp [rawPrefix, rawPort,
        FinitePortPrefix.projectedVertex, projectPort] at hipos hlast ⊢)
    (by simp [rawPrefix, rawPort, FinitePortPrefix.projectedVertex, projectPort])
    (by simp [rawPrefix, rawPort, FinitePortPrefix.projectedVertex, projectPort])

def firstForward : Link graph where
  path := sx
  direction := .forward
  nontrivial := by simp [sx]

def firstBackward : Link graph where
  path := ax
  direction := .backward
  nontrivial := by simp [ax]

def middleForward : Link graph where
  path := ab
  direction := .forward
  nontrivial := by simp [ab]

def lastBackward : Link graph where
  path := xb
  direction := .backward
  nontrivial := by simp [xb]

def lastForward : Link graph where
  path := xt
  direction := .forward
  nontrivial := by simp [xt]

/-- The first forward run and the later backward run have the forbidden
non-adjacent contact at `x`. -/
theorem not_compatible_firstForward_lastBackward :
    ¬ CompatibleInOrder False firstForward lastBackward := by
  intro h
  have hdisj : Disjoint sx.support xb.support := by
    exact h.2 (by simp)
  exact Set.disjoint_left.1 hdisj
    (show x ∈ sx.support by simp)
    (show x ∈ xb.support by simp)

/-- No compatibility-certified run walk can retain the five literal runs in
their raw order.  The contradiction is exactly its `0 < 3` compatibility
field, not a loss caused by a later switching theorem. -/
theorem no_certifiedRunWalk_with_raw_links
    (C : FiniteCertifiedRunWalk graph) (hlast : C.lastIndex = 4)
    (h0 : C.link ⟨0, by omega⟩ = firstForward)
    (_h1 : C.link ⟨1, by omega⟩ = firstBackward)
    (_h2 : C.link ⟨2, by omega⟩ = middleForward)
    (h3 : C.link ⟨3, by omega⟩ = lastBackward)
    (_h4 : C.link ⟨4, by omega⟩ = lastForward) : False := by
  let i : Fin (C.lastIndex + 1) := ⟨0, by omega⟩
  let j : Fin (C.lastIndex + 1) := ⟨3, by omega⟩
  have hij : i < j := by
    exact Fin.mk_lt_mk.mpr (by omega)
  have hc := C.compatible i j hij
  have hadjacent : ¬ ((3 : Nat) = 0 + 1) := by omega
  rw [h0, h3] at hc
  change CompatibleInOrder ((3 : Nat) = 0 + 1)
    firstForward lastBackward at hc
  exact not_compatible_firstForward_lastBackward
    (show CompatibleInOrder False firstForward lastBackward by
      simpa [hadjacent] using hc)

#print axioms not_compatible_firstForward_lastBackward
#print axioms no_certifiedRunWalk_with_raw_links

end TwoWarpMatchingRawRunCompatibilityObstruction
end Erdos599
