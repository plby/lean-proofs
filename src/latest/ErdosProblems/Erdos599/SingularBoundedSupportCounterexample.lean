/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularBoundedSupportRows
import ErdosProblems.Erdos599.SingularProgressiveExchangeAmbient

/-!
# Bounded support does not provide historical forward coherence

The bounded-support selector is useful for triangular competitor closure,
but it does not by itself solve the same-column history problem.  In the
finite normalized unhindered crossing web, take the target path
`d -> x -> t1` and put the literal trivial path at the unrequested source
`b`.  Every `b`--target path uses either `x` or `t1`.  Hence no warp which
forward-extends the completed `d` component can later target-link `b`.

This sharp example distinguishes the positive support-control theorem from
the still necessary future-safe or registered-provenance selection.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularBoundedSupportCounterexample

open DirectedPath SingularExtension SingularJointFullRow
  SingularBoundedSupportRows
open SingularSafeBatchCounterexample
open SingularSafeBatchCounterexample.Vertex
open SingularProgressiveExchangeAmbient
open SingularProgressiveExchangeCounterexample

/-- The singleton target linkage chosen for the bounded request `{d}`. -/
def dLinkage : Set web.DPath := {(.inl dxt1 : web.DPath)}

theorem dLinkage_isLinkageBetween :
    IsLinkageBetween web {d} web.target dLinkage := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa [dLinkage] using hp
    have hq' : q = (.inl dxt1 : web.DPath) := by
      simpa [dLinkage] using hq
    exact (hpq (hp'.trans hq'.symm)).elim
  · intro p hp
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa [dLinkage] using hp
    subst p
    exact ⟨dxt1, rfl⟩
  · ext v
    constructor
    · rintro ⟨p, hp, hpv⟩
      have hp' : p = (.inl dxt1 : web.DPath) := by
        simpa [dLinkage] using hp
      subst p
      change d = v at hpv
      exact Set.mem_singleton_iff.2 hpv.symm
    · intro hv
      have hvd : v = d := Set.mem_singleton_iff.1 hv
      subst v
      exact ⟨.inl dxt1, by simp [dLinkage], rfl⟩
  · rintro v ⟨p, hp, hpv⟩
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa [dLinkage] using hp
    subst p
    have hfinish : t1 = v := by simpa [web] using hpv
    subst v
    simp [web]
  · intro p hp
    have hp' : p = (.inl dxt1 : web.DPath) := by
      simpa [dLinkage] using hp
    subst p
    refine ⟨dxt1, rfl, ?_, ?_⟩
    · change dxt1.support ∩
        (({d} : Set Vertex) ∪ ({t1, t2, r} : Set Vertex)) = {d, t1}
      rw [support_dxt1]
      ext v
      cases v <;> simp
    · change dxt1.support ∩ ({d} : Set Vertex) = {d}
      rw [support_dxt1]
      ext v
      cases v <;> simp

/-- Fill the unrequested source with its literal trivial path. -/
def boundedRow : BoundedSupportRow web ({d} : Set Vertex) :=
  BoundedSupportRow.ofLinkage web_normalized (by simp [web])
    dLinkage_isLinkageBetween

/-- The same object is an exact `JointFullRow` with distinguished set equal
to the whole source.  Its fixed complementary domain is therefore empty,
which is a legitimate extension-clause instance. -/
def boundedJointRow : JointFullRow web web.source ({d} : Set Vertex) where
  paths := boundedRow.paths
  isWarp := boundedRow.isWarp
  finiteCharacter := boundedRow.finiteCharacter
  initialSet := boundedRow.initialSet
  linksJoint := by
    simpa using boundedRow.links

/-- The selected completed path is a member of the displayed bounded row. -/
theorem dxt1_mem_boundedRow :
    (.inl dxt1 : web.DPath) ∈ boundedRow.paths := by
  simp [boundedRow, BoundedSupportRow.ofLinkage,
    fillTargetLinkage, dLinkage]

/-- The independently selected bounded row for `{b}` uses the legitimate
`b -> y -> x -> r` target linkage and trivializes the other source. -/
def boundedRowB : BoundedSupportRow web ({b} : Set Vertex) :=
  BoundedSupportRow.ofLinkage web_normalized (by simp [web])
    fixed_isLinkageBetween

theorem byxr_mem_boundedRowB :
    (.inl byxr : web.DPath) ∈ boundedRowB.paths := by
  simp [boundedRowB, BoundedSupportRow.ofLinkage,
    fillTargetLinkage, fixed]

/-- Each bounded row is closed under competitors with itself. -/
theorem boundedRow_self_closed :
    web.competitorClosure boundedRow.paths {d} ⊆ {d} :=
  SingularJointFullRow.competitorClosure_self_subset
    web boundedRow.isWarp {d}

theorem boundedRowB_self_closed :
    web.competitorClosure boundedRowB.paths {b} ⊆ {b} :=
  SingularJointFullRow.competitorClosure_self_subset
    web boundedRowB.isWarp {b}

/-- The two individually self-closed lower-style rows have a cross-column
competitor: their completed target paths meet at `x`. -/
theorem b_mem_cross_competitorClosure :
    b ∈ web.competitorClosure
      (boundedRow.paths ∪ boundedRowB.paths) {d} := by
  refine ⟨d, by simp, (.inl dxt1 : web.DPath), Or.inl dxt1_mem_boundedRow,
    rfl, (.inl byxr : web.DPath), Or.inr byxr_mem_boundedRowB, rfl, ?_⟩
  intro hdisjoint
  change Disjoint dxt1.support byxr.support at hdisjoint
  exact Set.disjoint_left.1 hdisjoint
    (show x ∈ dxt1.support by rw [support_dxt1]; simp)
    (show x ∈ byxr.support by rw [support_byxr]; simp)

/-- Any finite `b`--target path meets the completed carrier at `x` or
`t1`. -/
theorem targetPathFrom_b_meets_dxt1
    (p : FinitePath web.graph) (hp : web.IsTargetPathFrom b p) :
    (p.support ∩ dxt1.support).Nonempty := by
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
        cases rest with
        | nil =>
            have hyt : y ∈ web.target := hp.2
            simpa [web] using hyt
        | @cons _ v _ hadj' rest' =>
            have hvx : v = x := by
              change graph.Adj y v at hadj'
              simpa [graph] using hadj'
            subst v
            refine ⟨x, ?_, ?_⟩
            · change x ∈ (Walk.cons hadj (Walk.cons hadj' rest')).support
              simp
            · rw [support_dxt1]
              simp
      · subst v
        cases rest with
        | nil =>
            have hqt : q ∈ web.target := hp.2
            simpa [web] using hqt
        | @cons _ v _ hadj' rest' =>
            have hvt : v = t1 := by
              change graph.Adj q v at hadj'
              simpa [graph] using hadj'
            subst v
            refine ⟨t1, ?_, ?_⟩
            · change t1 ∈ (Walk.cons hadj (Walk.cons hadj' rest')).support
              simp
            · rw [support_dxt1]
              simp

/-- Even this literal-trivial-outside bounded row has no forward successor
which target-links the newly requested source `b`. -/
theorem no_forward_boundedRow_links_b :
    ¬ ∃ T : Set web.DPath,
      web.IsWarp T ∧ web.ForwardExtension boundedRow.paths T ∧
        LinksToTarget web T {b} := by
  rintro ⟨T, hwarp, hforward, hlinks⟩
  obtain ⟨pd, hpdT, hpdext⟩ :=
    hforward.1 (.inl dxt1) dxt1_mem_boundedRow
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
  have hzSupport : z ∈ f.support := by
    change z ∈ f.walk.support
    rw [hsupport]
    exact List.mem_append_right before hzAfter
  have hfTerminal : web.terminal? (.inl f : web.DPath) = some z :=
    web_normalized.terminal?_eq_of_mem_path (.inl f) hzSupport hzTarget
  have hfFinish : f.finish = z := by
    simpa only [web.terminal?_finite, Option.some.injEq] using hfTerminal
  obtain ⟨v, hvf, hvOld⟩ := targetPathFrom_b_meets_dxt1 f
    ⟨hfStart, hfFinish ▸ hzTarget⟩
  have hvPd : v ∈ pd.support :=
    web.support_mono_of_extends hpdext hvOld
  have hne : pd ≠ (.inl f : web.DPath) := by
    intro heq
    have hdb : d = b := by
      have hinit := web.extends_initial hpdext
      have heqinit := congrArg
        (fun r : web.DPath => DirectedPath.Path.initial r) heq
      change d = DirectedPath.Path.initial pd at hinit
      change DirectedPath.Path.initial pd = f.start at heqinit
      exact hinit.trans (heqinit.trans hfStart)
    exact Vertex.noConfusion hdb
  exact Set.disjoint_left.1 (hwarp hpdT hpbT hne) hvPd hvf

/-- The obstruction occurs inside the exact normalized, unhindered domain
of the singular induction. -/
theorem boundedSupport_history_obstruction :
    web.IsNormalized ∧ web.IsUnhindered ∧
      (∀ p ∈ boundedRow.paths, p.initial ∉ ({d} : Set Vertex) →
        p = web.trivialPath p.initial) ∧
      ¬ ∃ T : Set web.DPath,
        web.IsWarp T ∧ web.ForwardExtension boundedRow.paths T ∧
          LinksToTarget web T {b} :=
  ⟨web_normalized, web_unhindered, boundedRow.trivial_outside,
    no_forward_boundedRow_links_b⟩

/-- The failure is caused exactly by cross-column competition between two
rows which are each internally competitor-closed. -/
theorem cross_column_boundedSupport_obstruction :
    web.competitorClosure boundedRow.paths {d} ⊆ {d} ∧
      web.competitorClosure boundedRowB.paths {b} ⊆ {b} ∧
      b ∈ web.competitorClosure
        (boundedRow.paths ∪ boundedRowB.paths) {d} ∧
      ¬ ∃ T : Set web.DPath,
        web.IsWarp T ∧ web.ForwardExtension boundedRow.paths T ∧
          LinksToTarget web T {b} :=
  ⟨boundedRow_self_closed, boundedRowB_self_closed,
    b_mem_cross_competitorClosure, no_forward_boundedRow_links_b⟩

/-- Packaging the first row with the empty complementary linkage does not
remove the cross-column obstruction. -/
theorem jointFullRow_cross_column_obstruction :
    boundedJointRow.paths = boundedRow.paths ∧
      LinksToTarget web boundedJointRow.paths
        ((web.source \ web.source) ∪ ({d} : Set Vertex)) ∧
      b ∈ web.competitorClosure
        (boundedJointRow.paths ∪ boundedRowB.paths) {d} ∧
      ¬ ∃ T : Set web.DPath,
        web.IsWarp T ∧
          web.ForwardExtension boundedJointRow.paths T ∧
          LinksToTarget web T {b} :=
  ⟨rfl, boundedJointRow.linksJoint, b_mem_cross_competitorClosure,
    no_forward_boundedRow_links_b⟩

#print axioms no_forward_boundedRow_links_b
#print axioms boundedSupport_history_obstruction
#print axioms cross_column_boundedSupport_obstruction
#print axioms jointFullRow_cross_column_obstruction

end SingularBoundedSupportCounterexample
end CardinalInduction
end Erdos599
