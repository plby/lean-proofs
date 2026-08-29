/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProgressiveExchangeCounterexample

/-!
# The progressive crossing obstruction has an unhindered ambient web

The local successor counterexample is not caused by starting outside the
domain of the singular induction.  This file proves directly that its finite
ambient web is unhindered.  Thus the bad split row can occur in the same kind
of normalized unhindered web to which Assertion 9.17 is applied, and its fixed
crossing family is the legitimate complementary linkage.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProgressiveExchangeAmbient

open DirectedPath SingularTargetRowMachine
open SingularSafeBatchCounterexample
open SingularSafeBatchCounterexample.Vertex
open SingularProgressiveExchangeCounterexample

private def dBranch : Set Vertex := {d, w, t2}
private def bReach : Set Vertex := {b, y, x, r, q, t1}

private theorem bReach_step {u v : Vertex}
    (hu : u ∈ bReach) (huv : web.graph.Adj u v) : v ∈ bReach := by
  change graph.Adj u v at huv
  simp only [graph_adj] at huv
  rcases huv with huv | huv | huv | huv | huv | huv | huv | huv | huv
  all_goals rcases huv with ⟨rfl, rfl⟩ <;> simp [bReach] at hu ⊢

private theorem walk_preserves_bReach {u v : Vertex}
    (p : Walk web.graph u v) (hu : u ∈ bReach) : v ∈ bReach := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih => exact ih (bReach_step hu hab)

private theorem finite_start_eq_d_of_finish_mem_dBranch
    (p : FinitePath web.graph) (hstart : p.start ∈ web.source)
    (hfinish : p.finish ∈ dBranch) : p.start = d := by
  change p.start ∈ ({d, b} : Set Vertex) at hstart
  rcases hstart with h | h
  · exact h
  · have hs : p.start = b := by simpa using h
    have hreach : p.finish ∈ bReach :=
      walk_preserves_bReach p.walk (by simp [hs, bReach])
    have hdisjoint : Disjoint bReach dBranch := by
      exact Set.disjoint_left.2 (by
        intro v hvb hvd
        cases v <;> simp [bReach, dBranch] at hvb hvd)
    exact (Set.disjoint_left.1 hdisjoint hreach hfinish).elim

/-- Every ambient wave has a member starting at `d`. -/
private theorem exists_wave_member_starting_d
    (W : Set web.DPath) (hW : web.IsWave W) :
    ∃ f : FinitePath web.graph,
      (.inl f : web.DPath) ∈ W ∧ f.start = d ∧ f.finish ∈ dBranch := by
  have hdSource : d ∈ web.source := by simp [web]
  obtain ⟨z, hzD, hzW⟩ := hW.2.2 hdSource webDwt2 (by
    constructor
    · rfl
    · change t2 ∈ web.target
      simp [web])
  obtain ⟨p, hpW, hpz⟩ := hzW
  rcases p with f | ray
  · have hfinish : f.finish = z := Option.some.inj hpz
    have hzBranch : z ∈ dBranch := by
      have hs := support_webDwt2
      change webDwt2.support = dBranch at hs
      simpa only [hs] using hzD
    have hstartSource : f.start ∈ web.source :=
      hW.2.1 ⟨.inl f, hpW, rfl⟩
    refine ⟨f, hpW,
      finite_start_eq_d_of_finish_mem_dBranch f hstartSource ?_, ?_⟩
    · simpa only [hfinish] using hzBranch
    · simpa only [hfinish] using hzBranch
  · simp at hpz

/-- Every ambient wave also has a member starting at `b`.  If the member
found by the `b-q-t1` test path started at `d`, it would collide at its start
with the already forced `d`-member. -/
private theorem exists_wave_member_starting_b
    (W : Set web.DPath) (hW : web.IsWave W) :
    ∃ f : FinitePath web.graph,
      (.inl f : web.DPath) ∈ W ∧ f.start = b := by
  have hbSource : b ∈ web.source := by simp [web]
  obtain ⟨z, hzB, hzW⟩ := hW.2.2 hbSource bqt1 (by
    constructor
    · rfl
    · simp [web])
  obtain ⟨p, hpW, hpz⟩ := hzW
  rcases p with f | ray
  · have hfinish : f.finish = z := Option.some.inj hpz
    have hzBranch : z ∈ ({b, q, t1} : Set Vertex) := by
      change z ∈ bqt1.support at hzB
      rw [support_bqt1] at hzB
      exact hzB
    have hstartSource : f.start ∈ web.source :=
      hW.2.1 ⟨.inl f, hpW, rfl⟩
    change f.start ∈ ({d, b} : Set Vertex) at hstartSource
    rcases hstartSource with hfd | hfb
    · obtain ⟨g, hgW, hgd, hgfinish⟩ :=
        exists_wave_member_starting_d W hW
      have hfinishB : f.finish ∈ ({b, q, t1} : Set Vertex) := by
        simpa only [hfinish] using hzBranch
      by_cases hfg : (.inl f : web.DPath) = .inl g
      · have hfg' : f = g := Sum.inl.inj hfg
        subst g
        have hdisjoint : Disjoint ({b, q, t1} : Set Vertex) dBranch := by
          exact Set.disjoint_left.2 (by
            intro v hvb hvd
            cases v <;> simp [dBranch] at hvb hvd)
        exact (Set.disjoint_left.1 hdisjoint hfinishB hgfinish).elim
      · have hdisjoint := hW.1 hpW hgW hfg
        have hfdSupport : d ∈ f.support := hfd ▸ f.start_mem_support
        have hgdSupport : d ∈ g.support := hgd ▸ g.start_mem_support
        exact (Set.disjoint_left.1 hdisjoint hfdSupport hgdSupport).elim
    · exact ⟨f, hpW, by simpa using hfb⟩
  · simp at hpz

/-- The ambient crossing web is unhindered. -/
theorem web_unhindered : web.IsUnhindered := by
  rw [web.isUnhindered_iff]
  intro W hW
  apply Set.Subset.antisymm hW.2.1
  intro v hv
  change v ∈ ({d, b} : Set Vertex) at hv
  rcases hv with hvd | hvb
  · obtain ⟨f, hfW, hfd, -⟩ := exists_wave_member_starting_d W hW
    exact ⟨.inl f, hfW, hfd.trans hvd.symm⟩
  · have hvb' : v = b := by simpa using hvb
    obtain ⟨f, hfW, hfb⟩ := exists_wave_member_starting_b W hW
    exact ⟨.inl f, hfW, hfb.trans hvb'.symm⟩

/-- Full source of the counterexample decomposes as the designated singleton
and the fixed linkage's singleton source. -/
theorem source_sdiff_d : web.source \ ({d} : Set Vertex) = {b} := by
  ext v
  cases v <;> simp [web]

/-- Exact induction-domain obstruction: normalized and unhindered ambient
web, a genuine complementary linkage, and a genuine split row whose literal
competitor successor does not exist. -/
theorem unhindered_progressive_obstruction :
    web.IsNormalized ∧ web.IsUnhindered ∧
      IsLinkageBetween web (web.source \ ({d} : Set Vertex)) web.target fixed ∧
      ¬ SplitTargetRowSuccessorRule (I := PUnit) web fixed := by
  refine ⟨web_normalized, web_unhindered, ?_,
    not_splitTargetRowSuccessorRule⟩
  rw [source_sdiff_d]
  exact fixed_isLinkageBetween

#print axioms unhindered_progressive_obstruction

end SingularProgressiveExchangeAmbient
end CardinalInduction
end Erdos599
