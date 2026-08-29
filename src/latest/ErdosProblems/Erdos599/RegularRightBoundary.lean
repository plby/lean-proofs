/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceAnnularStep
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# The obstruction at an overlapping right boundary

A path family which links a requested vertex all the way to the web target
cannot at the same time regard that vertex as a nonterminal point of its
right boundary.  In particular, a right-tight family can link a requested
vertex lying on its right boundary only when that vertex is already a web
target.

This is the precise obstruction which has to be accounted for when two
ladder frontiers overlap.  It is useful independently of any particular
slice construction: a constructor claiming both `LinksToTarget` and
`MeetsOnlyAtTerminal` must either prove the displayed request/boundary
intersection is contained in the target or keep the already completed
components outside the boundary-tight pending family.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularRightBoundary

open DirectedPath

universe u
variable {V : Type u}

/-- A web with one source is unhindered as soon as that source can reach
the target.

Indeed, the terminal frontier of any wave has to meet a fixed target path
from the unique source.  It is therefore nonempty.  A path witnessing that
nonemptiness starts in the source, hence at its unique vertex, so the wave
does not miss any source.

This small observation is useful when auditing frontier-overlap examples:
the trivial wave on the unique source is not a hindrance, irrespective of
whether the source itself is a target. -/
theorem isUnhindered_of_source_eq_singleton_of_mem_reachableToTarget
    (Gamma : DWeb V) {a : V} (hsource : Gamma.source = {a})
    (haReach : a ∈ Gamma.reachableToTarget) :
    Gamma.IsUnhindered := by
  apply Gamma.isUnhindered_iff.2
  intro W hW
  apply Set.Subset.antisymm hW.2.1
  intro x hxSource
  have hx : x = a := by
    simpa only [hsource, Set.mem_singleton_iff] using hxSource
  subst x
  have haSource : a ∈ Gamma.source := by
    rw [hsource]
    exact Set.mem_singleton a
  obtain ⟨p, hpTarget⟩ := haReach
  obtain ⟨x, _hxp, hxFrontier⟩ := hW.2.2 haSource p hpTarget
  obtain ⟨q, hqW, _hqTerminal⟩ := hxFrontier
  have hqInitialSource : q.initial ∈ Gamma.source :=
    hW.2.1 ⟨q, hqW, rfl⟩
  have hqInitial : q.initial = a := by
    simpa only [hsource, Set.mem_singleton_iff] using hqInitialSource
  exact ⟨q, hqW, hqInitial⟩

/-! ### A concrete branching-stage audit -/

namespace BranchingStage

/-- The three vertices of the smallest branching example. -/
inductive Vertex
  | u | b | c
  deriving DecidableEq

open Vertex

/-- Two target edges leave the unique source. -/
def graph : Digraph Vertex where
  Adj x y := x = u ∧ (y = b ∨ y = c)

/-- The edge from the source to the first target. -/
def ub : FinitePath graph where
  start := u
  finish := b
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [u, b].Nodup
    simp

@[simp] theorem ub_support : ub.support = ({u, b} : Set Vertex) := by
  ext x
  change x ∈ [u, b] ↔ _
  simp

/-- The branching web has one source and two targets. -/
def web : DWeb Vertex where
  graph := graph
  source := {u}
  target := {b, c}

/-- The branching web already satisfies the standard source/target edge
normalization. -/
theorem isNormalized : web.IsNormalized := by
  intro x y hxy
  simp only [web, graph] at hxy ⊢
  rcases hxy with ⟨rfl, rfl | rfl⟩ <;> simp

/-- The source is not itself a target. -/
theorem source_not_target : u ∉ web.target := by
  simp [web]

/-- Nevertheless the unique source reaches a target. -/
theorem source_mem_reachableToTarget : u ∈ web.reachableToTarget := by
  exact ⟨ub, rfl, by simp [web, ub]⟩

/-- The unique trivial-wave component is essential, despite its vertex not
being a target: the outgoing edge to `b` witnesses reachability after the
vertex itself is removed from the frontier. -/
theorem source_mem_essential_trivialWave :
    u ∈ web.essential (web.terminalFrontier web.trivialWave) := by
  rw [web.terminalFrontier_trivialWave, web.mem_essential_iff]
  constructor
  · exact Set.mem_singleton u
  · change u ∉ web.roof (({u} : Set Vertex) \ {u})
    rw [Set.sdiff_self, web.not_mem_roof_iff]
    exact ⟨ub, ⟨rfl, by simp [web, ub]⟩, Set.disjoint_empty ub.support⟩

/-- Consequently the trivial wave is not a hindrance. -/
theorem trivialWave_not_isHindrance :
    ¬ web.IsHindrance web.trivialWave := by
  intro h
  exact h.2 web.initialSet_trivialWave

/-- Hence the concrete branching stage is unhindered.  In particular, its
trivial source path is a wave but not a hindrance. -/
theorem isUnhindered : web.IsUnhindered :=
  isUnhindered_of_source_eq_singleton_of_mem_reachableToTarget
    web rfl source_mem_reachableToTarget

/-- The completed source-to-target component used in the overlap audit. -/
def targetFamily : Set web.DPath := {Sum.inl ub}

/-- The completed component genuinely links the unique source to the web
target. -/
theorem targetFamily_linksToTarget :
    LinksToTarget web targetFamily {u} := by
  intro a ha
  have haEq : a = u := Set.mem_singleton_iff.mp ha
  subst a
  refine ⟨Sum.inl ub, Set.mem_singleton _, ub, rfl, ?_, ?_⟩
  · have h : ub.support ∩ ({u} : Set Vertex) = {u} := by
      rw [ub_support]
      simp
    simpa only [web] using h
  · exact ⟨[], [b], rfl, b, by simp [web], by simp⟩

end BranchingStage

/-- A requested vertex which also belongs to the right boundary of a
right-tight target-linking family is already a target vertex.

Normalization is used only to turn the target hit in `LinksToTarget` into
the finish of its finite witness.  Right-boundary tightness then identifies
that finish with the requested boundary point. -/
theorem request_inter_rightBoundary_subset_target
    {Gamma : DWeb V} (hNorm : Gamma.IsNormalized)
    {W : Set Gamma.DPath} {U B : Set V}
    (hlinks : LinksToTarget Gamma W U)
    (htight : SliceSpliceSource.MeetsOnlyAtTerminal Gamma W B) :
    U ∩ B ⊆ Gamma.target := by
  intro a ha
  obtain ⟨p, hpW, q, rfl, hpure, hsuffix⟩ := hlinks a ha.1
  have haSupport : a ∈ q.support := by
    have haInter : a ∈ q.support ∩ U := by
      rw [hpure]
      exact Set.mem_singleton a
    exact haInter.1
  have hfinishTarget : q.finish ∈ Gamma.target :=
    SliceAnnularStep.finish_mem_target_of_suffixMeets_of_normalized
      hNorm q hsuffix
  have hterminal := htight (Sum.inl q) hpW a haSupport ha.2
  change some q.finish = some a at hterminal
  exact Option.some.inj hterminal ▸ hfinishTarget

/-- Pointwise version of
`request_inter_rightBoundary_subset_target`. -/
theorem target_of_requested_rightBoundary
    {Gamma : DWeb V} (hNorm : Gamma.IsNormalized)
    {W : Set Gamma.DPath} {U B : Set V}
    (hlinks : LinksToTarget Gamma W U)
    (htight : SliceSpliceSource.MeetsOnlyAtTerminal Gamma W B)
    {a : V} (haU : a ∈ U) (haB : a ∈ B) :
    a ∈ Gamma.target :=
  request_inter_rightBoundary_subset_target hNorm hlinks htight ⟨haU, haB⟩

namespace BranchingStage

open Vertex

/-- The completed component cannot be made right-tight at a boundary which
contains both its non-target start and its target finish.  This is the
concrete obstruction exhibited by a persistent overlap of ladder
frontiers. -/
theorem targetFamily_not_meetsOnlyAtTerminal :
    ¬ SliceSpliceSource.MeetsOnlyAtTerminal web targetFamily {u, b} := by
  intro htight
  exact source_not_target
    (target_of_requested_rightBoundary isNormalized
      targetFamily_linksToTarget htight (by simp) (by simp))

end BranchingStage

end RegularRightBoundary
end CardinalInduction
end Erdos599
