/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeDesignatedLimit
import ErdosProblems.Erdos599.SingularSafeCompletedMachine
import ErdosProblems.Erdos599.RegularRightBoundary

/-!
# Trivial-source resurrection loses deleted target endpoints

Lifting a final residual wave and adding trivial paths only at the deleted
sources is not a sound replacement for retaining a selected target linkage.
Even when the selected linkage is safely deletable, an unselected source may
have an ambient path into one of its deleted target endpoints.  That path is
invisible in the residual web and is stopped neither by the residual wave nor
by the deleted sources.

The four-vertex example below makes this exact.  The selected path is
`a -> t`; the residual has the full maximal wave `b -> s`; nevertheless the
ambient path `b -> t` avoids both the residual terminal frontier `{s}` and
the deleted source set `{a}`.  Thus `ResurrectionSeparates` is strictly
stronger than residual unhinderedness, and retaining (or rerouting) the
selected source--target paths is logically necessary in an ambient wave.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularResurrectionSeparatesCounterexample

open DirectedPath SingularSafeDesignatedLimit

inductive Vertex
  | a | b | t | s
  deriving DecidableEq

open Vertex

/-- The selected edge, the competing entrance into its target, and one
residual target edge. -/
def graph : Digraph Vertex where
  Adj x y := (x = a ∧ y = t) ∨ (x = b ∧ (y = t ∨ y = s))

def web : DWeb Vertex where
  graph := graph
  source := {a, b}
  target := {t, s}

def pathAT : FinitePath web.graph where
  start := a
  finish := t
  walk := .cons (by simp [web, graph]) .nil
  isPath := by
    change [a, t].Nodup
    simp

def bt : FinitePath web.graph where
  start := b
  finish := t
  walk := .cons (by simp [web, graph]) .nil
  isPath := by
    change [b, t].Nodup
    simp

def bs : FinitePath web.graph where
  start := b
  finish := s
  walk := .cons (by simp [web, graph]) .nil
  isPath := by
    change [b, s].Nodup
    simp

@[simp] theorem pathAT_support : pathAT.support = ({a, t} : Set Vertex) := by
  ext x
  change x ∈ [a, t] ↔ _
  simp

@[simp] theorem bt_support : bt.support = ({b, t} : Set Vertex) := by
  ext x
  change x ∈ [b, t] ↔ _
  simp

@[simp] theorem bs_support : bs.support = ({b, s} : Set Vertex) := by
  ext x
  change x ∈ [b, s] ↔ _
  simp

theorem web_normalized : web.IsNormalized := by
  intro x y hxy
  simp only [web, graph] at hxy ⊢
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> simp

def selected : Set web.DPath := {Sum.inl pathAT}

@[simp] theorem selected_vertexSet :
    web.vertexSet selected = ({a, t} : Set Vertex) := by
  ext x
  simp only [DWeb.mem_vertexSet, selected]
  constructor
  · rintro ⟨p, rfl, hxp⟩
    change x ∈ pathAT.support at hxp
    simpa using hxp
  · intro hx
    refine ⟨Sum.inl pathAT, rfl, ?_⟩
    change x ∈ pathAT.support
    simpa using hx

/-- The selected edge is an honest linkage of the designated source. -/
theorem selected_linkage :
    IsLinkageBetween web {a} web.target selected := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    simp only [selected, Set.mem_singleton_iff] at hp hq
    exact (hpq (hp.trans hq.symm)).elim
  · intro p hp
    simp only [selected, Set.mem_singleton_iff] at hp
    exact ⟨pathAT, hp⟩
  · ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      simp only [selected, Set.mem_singleton_iff] at hp
      subst p
      change pathAT.start = a
      rfl
    · intro hx
      have hxa : x = a := by simpa using hx
      subst x
      exact ⟨Sum.inl pathAT, Set.mem_singleton _, rfl⟩
  · rintro x ⟨p, hp, hpx⟩
    simp only [selected, Set.mem_singleton_iff] at hp
    subst p
    change some pathAT.finish = some x at hpx
    have hxt : x = t := (Option.some.inj hpx).symm
    subst x
    simp [web]
  · intro p hp
    simp only [selected, Set.mem_singleton_iff] at hp
    subst p
    refine ⟨pathAT, rfl, ?_, ?_⟩
    · change pathAT.support ∩ ({a} ∪ web.target) =
        {pathAT.start, pathAT.finish}
      rw [pathAT_support]
      ext x
      rcases x with (_ | _ | _ | _) <;> simp [web, pathAT]
    · change pathAT.support ∩ {a} = {pathAT.start}
      rw [pathAT_support]
      simp [pathAT]

abbrev residual : DWeb Vertex := web.delete (web.vertexSet selected)

@[simp] theorem residual_source : residual.source = {b} := by
  rw [residual, selected_vertexSet]
  ext x
  rcases x with (_ | _ | _ | _) <;> simp [web]

@[simp] theorem residual_target : residual.target = {s} := by
  rw [residual, selected_vertexSet]
  ext x
  rcases x with (_ | _ | _ | _) <;> simp [web]

/-- The surviving target edge, retyped in the deletion. -/
def residualPath : FinitePath residual.graph where
  start := b
  finish := s
  walk := .cons (by
    rw [residual, selected_vertexSet]
    change graph.Adj b s ∧ b ∈ ({a, t} : Set Vertex)ᶜ ∧
      s ∈ ({a, t} : Set Vertex)ᶜ
    simp [graph]) .nil
  isPath := by
    change [b, s].Nodup
    simp

@[simp] theorem residualPath_support :
    residualPath.support = ({b, s} : Set Vertex) := by
  ext x
  change x ∈ [b, s] ↔ _
  simp

def residualFamily : Set residual.DPath := {Sum.inl residualPath}

@[simp] theorem residualFamily_initialSet :
    residual.initialSet residualFamily = {b} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [residualFamily, Set.mem_singleton_iff] at hp
    subst p
    change residualPath.start = b
    rfl
  · intro hx
    have hxb : x = b := by simpa using hx
    subst x
    exact ⟨Sum.inl residualPath, Set.mem_singleton _, rfl⟩

@[simp] theorem residualFamily_terminalFrontier :
    residual.terminalFrontier residualFamily = {s} := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [residualFamily, Set.mem_singleton_iff] at hp
    subst p
    change some residualPath.finish = some x at hpx
    have hxs : x = s := (Option.some.inj hpx).symm
    simpa [hxs]
  · intro hx
    have hxs : x = s := by simpa using hx
    subst x
    exact ⟨Sum.inl residualPath, Set.mem_singleton _, rfl⟩

theorem residualFamily_isWave : residual.IsWave residualFamily := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp q hq hpq
    simp only [residualFamily, Set.mem_singleton_iff] at hp hq
    exact (hpq (hp.trans hq.symm)).elim
  · rw [residualFamily_initialSet, residual_source]
  · rw [residualFamily_terminalFrontier, residual_source,
      ← residual_target, roof_target]
    exact Set.subset_univ _

/-- A finite prefix which has already reached the upper path's finish is the
whole upper path. -/
private theorem FinitePath.eq_of_prefix_of_finish_eq {D : Digraph Vertex}
    {p q : FinitePath D} (hpq : p.IsPrefixOf q)
    (hfinish : p.finish = q.finish) : p = q := by
  have hstart : p.start = q.start := hpq.start_eq
  cases p with
  | mk ps pf pw ppath =>
      cases q with
      | mk qs qf qw qpath =>
          dsimp at hstart hfinish hpq ⊢
          subst qs
          subst qf
          have hs : pw.support = qw.support :=
            FinitePath.IsPrefixOf.eq_support_of_finish_eq hpq rfl
          have hw : pw = qw := Walk.eq_of_support_eq pw qw hs
          subst qw
          rfl

/-- A path extending a normalized finite target path is that path itself. -/
private theorem eq_of_target_extension
    {p : residual.DPath}
    (h : Path.Extends (Sum.inl residualPath) p) :
    p = Sum.inl residualPath := by
  have hsSupport : s ∈ p.support :=
    Path.support_mono_of_extends h
      (by change s ∈ residualPath.support; rw [residualPath_support]; simp)
  have hsTarget : s ∈ residual.target := by rw [residual_target]; simp
  have hResidualNorm : residual.IsNormalized :=
    SingularSafeCompletedMachine.isNormalized_delete web_normalized
      (web.vertexSet selected)
  have hpTerminal : p.terminal? = some s :=
    hResidualNorm.terminal?_eq_of_mem_path p hsSupport hsTarget
  rcases p with q | r
  · change some q.finish = some s at hpTerminal
    have hqfinish : q.finish = s := Option.some.inj hpTerminal
    congr 1
    exact (FinitePath.eq_of_prefix_of_finish_eq h hqfinish.symm).symm
  · simp at hpTerminal

/-- The surviving full target path is forward-extension maximal as a wave. -/
theorem residualWave_isMax :
    IsMax (⟨residualFamily, residualFamily_isWave⟩ : residual.Wave) := by
  intro N hMN
  constructor
  · intro p hp
    obtain ⟨q, hqM, hqp⟩ := hMN.2 p hp
    simp only [residualFamily, Set.mem_singleton_iff] at hqM
    subst q
    have hpEq : p = Sum.inl residualPath := eq_of_target_extension hqp
    subst p
    exact ⟨Sum.inl residualPath, Set.mem_singleton _, Path.extends_refl _⟩
  · intro p hp
    simp only [residualFamily, Set.mem_singleton_iff] at hp
    subst p
    obtain ⟨q, hqN, hpq⟩ := hMN.1 (Sum.inl residualPath)
      (Set.mem_singleton _)
    have hq : q = Sum.inl residualPath := eq_of_target_extension hpq
    subst q
    exact ⟨Sum.inl residualPath, hqN, Path.extends_refl _⟩

/-- The residual is unhindered (indeed, its displayed maximal wave starts at
its whole source). -/
theorem residual_unhindered : residual.IsUnhindered := by
  have hbReach : b ∈ residual.reachableToTarget := by
    refine ⟨residualPath, rfl, ?_⟩
    change residualPath.finish ∈ residual.target
    rw [residual_target]
    simp [residualPath]
  exact RegularRightBoundary.isUnhindered_of_source_eq_singleton_of_mem_reachableToTarget
    residual residual_source hbReach

/-- The competing ambient path avoids the two-frontier set used by
`ResurrectionSeparates`. -/
theorem bt_avoids_resurrectionFrontier :
    Disjoint bt.support
      (residual.terminalFrontier residualFamily ∪
        (web.source ∩ web.vertexSet selected)) := by
  rw [bt_support, residualFamily_terminalFrontier, selected_vertexSet]
  simp [web]

/-- Even the full maximal residual wave fails the proposed no-linkage
resurrection separator. -/
theorem not_resurrectionSeparates_safeBatch :
    ¬ ResurrectionSeparates web (web.vertexSet selected)
      ⟨residualFamily, residualFamily_isWave⟩ := by
  intro hsep
  have hbSource : b ∈ web.source := by simp [web]
  have hbRoof := hsep hbSource
  have hbNotRoof : b ∉ web.roof
      ((web.delete (web.vertexSet selected)).terminalFrontier residualFamily ∪
        (web.source ∩ web.vertexSet selected)) := by
    rw [web.not_mem_roof_iff]
    exact ⟨bt, ⟨rfl, by simp [web, bt]⟩,
      bt_avoids_resurrectionFrontier⟩
  exact hbNotRoof hbRoof

/-- Complete counterexample package: the linkage carrier is safely
deletable and the exhibited residual wave is maximal, but the no-linkage
resurrection condition is false. -/
theorem safeBatch_with_maximalWave_not_resurrectionSeparates :
    (web.delete (web.vertexSet selected)).IsUnhindered ∧
      IsLinkageBetween web {a} web.target selected ∧
      IsMax (⟨residualFamily, residualFamily_isWave⟩ : residual.Wave) ∧
      ¬ ResurrectionSeparates web (web.vertexSet selected)
        ⟨residualFamily, residualFamily_isWave⟩ := by
  exact ⟨residual_unhindered, selected_linkage, residualWave_isMax,
    not_resurrectionSeparates_safeBatch⟩

#print axioms safeBatch_with_maximalWave_not_resurrectionSeparates

end SingularResurrectionSeparatesCounterexample
end CardinalInduction
end Erdos599
