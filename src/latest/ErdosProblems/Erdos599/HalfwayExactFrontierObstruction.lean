/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction

/-!
# The exact-frontier strengthening cannot be the induction hypothesis

Countably many disjoint two-leaf stars are normalized and unhindered.
Nevertheless a source-starting warp which links every source to the target
cannot have a separating terminal frontier.  Thus the extra frontier
equality in the historical `SeparatingHalfwayClauseAt` is false even at the
first infinite cardinal.  This audit is not a replacement for the positive
linkability theorem.
-/

namespace Erdos599.CardinalInduction.HalfwayExactFrontierObstruction

open Cardinal Set DirectedPath

abbrev Vertex := ℕ × Option Bool

def graph : Digraph Vertex where
  Adj x y := x.1 = y.1 ∧ x.2 = none ∧ y.2 ≠ none

def web : DWeb Vertex where
  graph := graph
  source := {x | x.2 = none}
  target := {x | x.2 ≠ none}

theorem normalized : web.IsNormalized := by
  intro x y hxy
  exact ⟨hxy.2.2, fun hx ↦ hx hxy.2.1⟩

def branch (i : ℕ) (b : Bool) : FinitePath graph where
  start := (i, none)
  finish := (i, some b)
  walk := .cons (v := (i, some b)) ⟨rfl, rfl, Option.some_ne_none b⟩ .nil
  isPath := by simp [Walk.IsPath, Walk.support]

theorem branch_support (i : ℕ) (b : Bool) :
    (branch i b).support = {(i, none), (i, some b)} := by
  ext x
  simp [FinitePath.support, branch, Walk.support]

theorem walk_preserves_index {x y : Vertex} (p : Walk graph x y) :
    x.1 = y.1 := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact h.1.trans ih

theorem initial_eq_of_terminal_index
    (q : FinitePath graph) (hq : q.start ∈ web.source)
    {i : ℕ} (hi : q.finish.1 = i) : q.start = (i, none) := by
  exact Prod.ext ((walk_preserves_index q.walk).trans hi) hq

/-- Every wave must use the unique source of every star component. -/
theorem unhindered : web.IsUnhindered := by
  rw [web.isUnhindered_iff]
  intro W hW
  apply Set.Subset.antisymm hW.2.1
  rintro ⟨i, t⟩ ht
  change t = none at ht
  subst t
  obtain ⟨z, hz, p, hp, hterminal⟩ :=
    hW.2.2 (show (i, none) ∈ web.source from rfl) (branch i false)
      ⟨rfl, Option.some_ne_none false⟩
  cases p with
  | inr r => simp at hterminal
  | inl q =>
      have hqz : q.finish = z := Option.some.inj hterminal
      have hzi : z.1 = i := by
        change z ∈ (branch i false).support at hz
        rw [branch_support] at hz
        rcases hz with rfl | hz
        · rfl
        · have hz' : z = (i, some false) := hz
          exact congrArg Prod.fst hz'
      exact ⟨.inl q, hp, initial_eq_of_terminal_index q
        (hW.2.1 ⟨.inl q, hp, rfl⟩) (hqz ▸ hzi)⟩

/-- Any source-starting warp that links all sources to the target fails to
separate at its own terminal frontier. -/
theorem terminalFrontier_not_separator
    {W : Set web.DPath} (hW : web.IsWarp W)
    (hstarts : web.initialSet W ⊆ web.source)
    (hlinks : LinksToTarget web W web.source) :
    ¬ IsSeparatorFrom web web.source (web.terminalFrontier W) := by
  intro hsep
  obtain ⟨p, hp, q, rfl, hsource, before, after, hsupp, t, ht, hts⟩ :=
    hlinks (0, none) rfl
  have ha : (0, none) ∈ q.support := by
    have h : (0, none) ∈ q.support ∩ web.source := by
      rw [hsource]
      exact Set.mem_singleton _
    exact h.1
  have htq : t ∈ q.support := by
    change t ∈ q.walk.support
    rw [hsupp]
    exact List.mem_append_right before hts
  have hfinish : q.finish ∈ web.target :=
    (normalized.eq_finish_of_mem_walk q.walk htq ht) ▸ ht
  have haNot : (0, none) ∉ web.terminalFrontier W := by
    intro haTerminal
    have heq := DWeb.IsWarp.finite_support_inter_terminalFrontier
      web hW hp ⟨ha, haTerminal⟩
    have heq' : (0, none) = q.finish := heq
    exact hfinish (congrArg Prod.snd heq'.symm)
  have hleaf (b : Bool) : (0, some b) ∈ web.terminalFrontier W := by
    obtain ⟨z, hz, hzTerminal⟩ := hsep (show (0, none) ∈ web.source from rfl)
      (branch 0 b)
      ⟨rfl, Option.some_ne_none b⟩
    change z ∈ (branch 0 b).support at hz
    rw [branch_support] at hz
    rcases hz with rfl | hz
    · exact (haNot hzTerminal).elim
    · exact hz ▸ hzTerminal
  have hmember (b : Bool) : ∃ f : FinitePath graph,
      (.inl f : web.DPath) ∈ W ∧ f.start = (0, none) ∧
        f.finish = (0, some b) := by
    obtain ⟨p, hp, hterminal⟩ := hleaf b
    cases p with
    | inr r => simp at hterminal
    | inl f =>
        have hfinish : f.finish = (0, some b) := Option.some.inj hterminal
        exact ⟨f, hp, initial_eq_of_terminal_index f
          (hstarts ⟨.inl f, hp, rfl⟩) (congrArg Prod.fst hfinish), hfinish⟩
  obtain ⟨f, hf, hfs, hft⟩ := hmember false
  obtain ⟨g, hg, hgs, hgt⟩ := hmember true
  have heq : (.inl f : web.DPath) = .inl g := by
    by_contra hne
    exact Set.disjoint_left.1 (hW hf hg hne)
      (hfs ▸ f.start_mem_support) (hgs ▸ g.start_mem_support)
  have hfg : f = g := Sum.inl.inj heq
  have hleaves := hft.symm.trans (hfg ▸ hgt)
  have : false = true := Option.some.inj (congrArg Prod.snd hleaves)
  exact Bool.noConfusion this

def sourceEquiv : web.source ≃ ℕ where
  toFun x := x.1.1
  invFun i := ⟨(i, none), rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.2.symm
  right_inv _ := rfl

theorem source_card : #web.source = ℵ₀ := by
  rw [Cardinal.mk_congr sourceEquiv, Cardinal.mk_nat]

/-- The old separating exact-frontier clause is false at `aleph0`. -/
theorem not_separatingHalfwayClauseAt :
    ¬ SeparatingHalfwayClauseAt web ℵ₀ := by
  intro h
  obtain ⟨W, C, hstop, hlinks, _hheight, hfrontier⟩ :=
    h web.source Set.Subset.rfl source_card
  apply terminalFrontier_not_separator hstop.stopover.linkage.isWarp
    (by rw [hstop.stopover.linkage.initialSet_eq]) hlinks
  rw [hfrontier]
  exact hstop.separator

/-- This is an infinite-cardinal counterexample in the intended domain:
the web is unhindered, so the historical universal induction is false. -/
theorem not_universalCardinalInductionAt :
    ¬ UniversalCardinalInductionAt Vertex ℵ₀ := by
  intro h
  exact not_separatingHalfwayClauseAt ((h web unhindered).2 le_rfl)

#print axioms unhindered
#print axioms not_universalCardinalInductionAt

end Erdos599.CardinalInduction.HalfwayExactFrontierObstruction
