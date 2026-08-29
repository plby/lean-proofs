/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# Auxiliary separation alone does not supply finite descent

This file records a three-vertex counterexample showing that the separator
hypothesis in `GroundingCut.assertion8_18` does not imply its
`FiniteDescentDecoder` hypothesis for an arbitrary `PopularAuxiliary.Input`.
The missing input is precisely the ladder-specific source/contact geometry.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFiniteDescentCounterexample

open DirectedPath

inductive Vertex
  | a | b | c
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj x y := (x = a ∧ y = b) ∨ (x = c ∧ y = b)

@[simp] theorem graph_adj (x y : Vertex) :
    graph.Adj x y ↔ (x = a ∧ y = b) ∨ (x = c ∧ y = b) :=
  Iff.rfl

def ab : FinitePath graph where
  start := a
  finish := b
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [a, b].Nodup
    simp

def cb : FinitePath graph where
  start := c
  finish := b
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [c, b].Nodup
    simp

@[simp] theorem ab_start : ab.start = a := rfl
@[simp] theorem ab_finish : ab.finish = b := rfl
@[simp] theorem cb_start : cb.start = c := rfl
@[simp] theorem cb_finish : cb.finish = b := rfl

@[simp] theorem ab_support : ab.support = ({a, b} : Set Vertex) := by
  ext x
  change x ∈ [a, b] ↔ _
  simp

@[simp] theorem cb_support : cb.support = ({c, b} : Set Vertex) := by
  ext x
  change x ∈ [c, b] ↔ _
  simp

@[simp] theorem ab_edgeSet : ab.walk.edgeSet = ({(a, b)} : Set (Vertex × Vertex)) := by
  simp [ab, DirectedPath.Walk.edgeSet]

def web : DWeb Vertex where
  graph := graph
  source := {c}
  target := {b}

def ladderPaths : Set web.DPath := {Sum.inl ab}

theorem ladderPaths_isWarp : web.IsWarp ladderPaths := by
  intro p hp q hq hpq
  simp only [ladderPaths, Set.mem_singleton_iff] at hp hq
  exact False.elim (hpq (hp.trans hq.symm))

def ladder : web.Warp := ⟨ladderPaths, ladderPaths_isWarp⟩

def input : PopularAuxiliary.Input web Empty where
  ladder := ladder
  groundedRecords := ∅
  finiteSource := ∅
  markerSet := {a}
  proxyPath i := nomatch i
  proxy_isRay i := nomatch i

abbrev LV := PopularAuxiliary.Input.LambdaVertex Vertex Empty

@[simp] theorem input_ladder_paths : input.ladder.paths = ladderPaths := rfl
@[simp] theorem input_finiteSource : input.finiteSource = ∅ := rfl
@[simp] theorem input_markerSet : input.markerSet = {a} := rfl

@[simp] theorem input_CE_empty : GroundingCut.CE input (∅ : Set LV) = ∅ := by
  ext e
  simp [GroundingCut.CE, PopularAuxiliary.Input.edgePart]

@[simp] theorem input_CV_empty : GroundingCut.CV input (∅ : Set LV) = ∅ := by
  ext x
  simp [GroundingCut.CV, PopularAuxiliary.Input.oldPart]

@[simp] theorem terminalFrontier_ladderPaths :
    web.terminalFrontier ladderPaths = ({b} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    have hpab : p = (Sum.inl ab : web.DPath) :=
      Set.mem_singleton_iff.mp hp
    subst p
    exact Option.some.inj hpx.symm
  · intro hx
    have hxb : x = b := by simpa using hx
    subst x
    refine ⟨Sum.inl ab, ?_, rfl⟩
    exact Set.mem_singleton (Sum.inl ab : web.DPath)

@[simp] theorem essential_singleton_b :
    web.essential ({b} : Set Vertex) = {b} := by
  apply Set.Subset.antisymm (web.essential_subset {b})
  intro x hx
  have hxb : x = b := by simpa using hx
  subst x
  refine ⟨by simp, ?_⟩
  rw [web.not_mem_roof_iff]
  refine ⟨FinitePath.trivial graph b, ⟨rfl, by simp [web]⟩, ?_⟩
  simp [DWeb.Avoids]

@[simp] theorem input_essentialLadder :
    input.essentialLadder = ladderPaths := by
  ext p
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    have hpab : p = (Sum.inl ab : web.DPath) :=
      Set.mem_singleton_iff.mp hp
    subst p
    refine ⟨Set.mem_singleton (Sum.inl ab : web.DPath), b, rfl, ?_⟩
    simpa using (show b ∈ web.essential ({b} : Set Vertex) by simp)

@[simp] theorem input_terminalCut :
    input.terminalCut = ({b} : Set Vertex) := by
  simp [PopularAuxiliary.Input.terminalCut]

@[simp] theorem input_targetMarkers :
    input.targetMarkers = ({a} : Set Vertex) := by
  ext x
  constructor
  · intro hx
    simpa [PopularAuxiliary.Input.targetMarkers, input] using hx.1
  · intro hx
    have hxa : x = a := by simpa using hx
    subst x
    refine ⟨by simp [PopularAuxiliary.Input.targetMarkers, input], ?_⟩
    rw [input_essentialLadder]
    refine ⟨Sum.inl ab, Set.mem_singleton (Sum.inl ab : web.DPath), ?_⟩
    change a ∈ ab.support
    simp

theorem input_lambda_separator_empty :
    Popular.IsSeparator input.lambda (∅ : Set LV) := by
  intro p hp _
  exfalso
  cases h : p.start with
  | old x =>
    have hx : x ∈ input.finiteSource :=
      (input.mem_lambda_source_old x).1 (h ▸ hp)
    simpa using hx
  | edge x y =>
    exact input.not_mem_lambda_source_edge x y (h ▸ hp)
  | proxy i =>
    exact Empty.elim i

theorem input_terminalCut_separator :
    Popular.IsSeparator web input.terminalCut := by
  intro p _ htarget
  have hfinish : p.finish = b := by
    simpa [web] using htarget
  refine ⟨b, ?_, by simp⟩
  simpa [hfinish] using p.finish_mem_support

theorem not_graph_adj_from_b (x : Vertex) : ¬ graph.Adj b x := by
  simp [graph]

theorem mem_walk_support_of_start_b {z x : Vertex}
    (w : Walk graph b z) (hx : x ∈ w.support) : x = b := by
  cases w with
  | nil => simpa using hx
  | cons h w => exact False.elim (not_graph_adj_from_b _ h)

theorem dpath_support_of_initial_b (p : web.DPath)
    (hp : p.initial = b) : p.support ⊆ ({b} : Set Vertex) := by
  cases p with
  | inl p =>
      rcases p with ⟨s, t, w, hw⟩
      change s = b at hp
      subst s
      intro x hx
      change x ∈ w.support at hx
      simpa using mem_walk_support_of_start_b w hx
  | inr r =>
      have h0 : r 0 = b := hp
      have hout := r.adj_succ 0
      change graph.Adj (r 0) (r 1) at hout
      rw [h0] at hout
      exact False.elim (not_graph_adj_from_b _ hout)

theorem initial_beforeEq {p : web.DPath} {x : Vertex}
    (hx : x ∈ p.support) : GroundingCut.BeforeEq p p.initial x := by
  cases p with
  | inl p =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inl p) x).1 hx
      refine ⟨0, n, ?_, hn, Nat.zero_le _⟩
      exact ⟨p.support_length_pos, p.support_getElem_zero⟩
  | inr r =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inr r) x).1 hx
      exact ⟨0, n, rfl, hn, Nat.zero_le _⟩

theorem firstVertex_eq_initial (p : web.DPath) (S : Set Vertex)
    (hi : p.initial ∈ S) :
    GroundingCut.firstVertex p S ⟨p.initial, p.initial_mem_support, hi⟩ =
      p.initial := by
  let hS : (p.support ∩ S).Nonempty :=
    ⟨p.initial, p.initial_mem_support, hi⟩
  apply GroundingCutDecoder.beforeEq_antisymm
  · exact GroundingCut.firstVertex_beforeEq p S hS
      ⟨p.initial_mem_support, hi⟩
  · exact initial_beforeEq (GroundingCut.firstVertex_mem p S hS).1

theorem fragment_parent_eq_ab (P : input.Fragment) :
    P.parent = (Sum.inl ab : web.DPath) := by
  exact Set.mem_singleton_iff.mp P.parent_mem

theorem fragment_initial_eq_a (P : input.Fragment)
    (hP : P ∈ GroundingCut.fragments input (∅ : Set LV)) :
    P.path.initial = a := by
  have hparent : P.parent = (Sum.inl ab : web.DPath) :=
    fragment_parent_eq_ab P
  have hiParent : P.path.initial ∈
      DirectedPath.Path.support (Sum.inl ab : web.DPath) := by
    rw [← hparent]
    exact P.support_subset P.path.initial_mem_support
  have hi : P.path.initial = a ∨ P.path.initial = b := by
    change P.path.initial ∈ ab.support at hiParent
    rw [ab_support] at hiParent
    simpa using hiParent
  rcases hi with hi | hi
  · exact hi
  · exfalso
    have haParent : a ∈
        DirectedPath.Path.support (Sum.inl ab : web.DPath) := by
      change a ∈ ab.support
      simp
    have hconn : GroundingCut.SurvivingConnected input (∅ : Set LV)
        (Sum.inl ab : web.DPath) P.path.initial a := by
      rw [hi]
      refine ⟨ab, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
      · intro x hx
        exact hx
      · intro e he
        exact he
      · rw [input_CE_empty]
        exact Set.disjoint_empty _
    have haPath : a ∈ P.path.support := by
      rw [hP.2]
      constructor
      · rw [hparent]
        exact haParent
      · rw [hparent]
        exact hconn
    have haOnly : a ∈ ({b} : Set Vertex) :=
      dpath_support_of_initial_b P.path hi haPath
    simpa using haOnly

theorem a_mem_escapeRegion :
    a ∈ input.escapeRegion (∅ : Set LV) := by
  let q := FinitePath.trivial input.lambda.graph
    (PopularAuxiliary.Input.LambdaVertex.old a : LV)
  exact ⟨{
    route := q
    start_eq := Or.inl rfl
    target := (input.mem_lambda_target_old a).2 (by simp)
    avoids := Set.disjoint_empty _
    old_not_mem := by simp }⟩

theorem blockingPoint_eq_a (P : input.Fragment)
    (hP : P ∈ GroundingCut.G0 input (∅ : Set LV)) :
    GroundingCut.blockingPoint input (∅ : Set LV) P = a := by
  have hi : P.path.initial = a := fragment_initial_eq_a P hP.1
  have hiEscape : P.path.initial ∈ input.escapeRegion (∅ : Set LV) := by
    simpa only [hi] using a_mem_escapeRegion
  have hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      input (∅ : Set LV) P :=
    ⟨P.path.initial, P.path.initial_mem_support, hiEscape⟩
  rw [GroundingCut.blockingPoint_eq_first_of_meetsEscape input ∅ P hescape]
  calc
    GroundingCut.firstVertex P.path (input.escapeRegion (∅ : Set LV)) hescape =
        P.path.initial := by
      simpa only using firstVertex_eq_initial P.path
        (input.escapeRegion (∅ : Set LV)) hiEscape
    _ = a := hi

theorem BB_subset_singleton_a :
    GroundingCut.BB input (∅ : Set LV) ⊆ ({a} : Set Vertex) := by
  intro x hx
  rcases hx with hxCV | hxBL
  · simpa using hxCV
  · obtain ⟨P, hP, hPx⟩ := hxBL
    have hxa : x = a := hPx.symm.trans (blockingPoint_eq_a P hP.1)
    simpa only [Set.mem_singleton_iff] using hxa

theorem cb_avoids_BB :
    web.Avoids cb (GroundingCut.BB input (∅ : Set LV)) := by
  change Disjoint cb.support (GroundingCut.BB input (∅ : Set LV))
  rw [Set.disjoint_left]
  intro x hx hBB
  have hxa : x = a := by
    simpa only [Set.mem_singleton_iff] using BB_subset_singleton_a hBB
  subst x
  change a ∈ cb.support at hx
  simpa using hx

/-- A separator of the auxiliary web does not, for an arbitrary auxiliary
input, imply the finite last-contact decoder used by Assertion 8.18. -/
theorem separator_does_not_imply_finiteDescentDecoder :
    Popular.IsSeparator input.lambda (∅ : Set LV) ∧
      Popular.IsSeparator web input.terminalCut ∧
        ¬ GroundingCut.FiniteDescentDecoder input (∅ : Set LV) := by
  refine ⟨input_lambda_separator_empty, input_terminalCut_separator, ?_⟩
  intro hdecode
  have hsource : cb.start ∈ web.source := by simp [web]
  have hterminal : cb.finish ∈ input.terminalCut := by simp
  obtain ⟨q, hqsource, hqtarget, hqavoid⟩ :=
    hdecode cb hsource hterminal cb_avoids_BB
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    input.lambda (∅ : Set LV) input_lambda_separator_empty
      q hqsource hqtarget hqavoid

end GroundingFiniteDescentCounterexample
end Erdos599
