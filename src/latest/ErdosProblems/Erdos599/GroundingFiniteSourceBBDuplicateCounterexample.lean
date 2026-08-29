/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingBBAntichainCounterexample
import ErdosProblems.Erdos599.GroundingFiniteDescentCounterexample

/-!
# A finite cut source can share a residual component with an earlier BL point

The old vertices selected for switching are `CV \ finiteSource`.  Hence a
finite auxiliary source lying in `CV` has no request.  If its grounded finite
parent has an earlier escaping blocking point, the unswitched residual parent
contains two distinct points of the literal boundary `BB = CV ∪ BL`.

This is the smallest form of the finite-parent duplicate which a corrected
Assertion 8.22 relation must split *and* root.  Assertion 8.21 cannot alter
the example because the request type is empty.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFiniteSourceBBDuplicateCounterexample

open DirectedPath PopularGroundingBridge
open GroundingCVFragmentAudit.Concrete.Vertex
open GroundingRootedReachabilityWarp

abbrev Vertex := GroundingCVFragmentAudit.Concrete.Vertex
abbrev graph := GroundingCVFragmentAudit.Concrete.graph
abbrev ab := GroundingCVFragmentAudit.Concrete.ab

@[simp] theorem ab_edgeSet_eq :
    ab.walk.edgeSet = ({(a, b)} : Set (Vertex × Vertex)) := by
  change ({(a, b)} : Set (Vertex × Vertex)) ∪ ∅ = {(a, b)}
  simp

def web : DWeb Vertex where
  graph := graph
  source := {a}
  target := {b}

def ladderPaths : Set web.DPath := {Sum.inl ab}

theorem ladderPaths_isWarp : web.IsWarp ladderPaths := by
  intro p hp q hq hpq
  simp only [ladderPaths, Set.mem_singleton_iff] at hp hq
  exact False.elim (hpq (hp.trans hq.symm))

def ladder : web.Warp := ⟨ladderPaths, ladderPaths_isWarp⟩

theorem web_isNormalized : web.IsNormalized := by
  rintro x y hxy
  constructor
  · intro hy
    have hya : y = a := by simpa [web] using hy
    subst y
    simpa [web, graph, GroundingCVFragmentAudit.Concrete.graph] using hxy
  · intro hx
    have hxb : x = b := by simpa [web] using hx
    subst x
    simpa [web, graph, GroundingCVFragmentAudit.Concrete.graph] using hxy

def input : PopularAuxiliary.Input web Empty where
  ladder := ladder
  groundedRecords := {Sum.inl ab}
  finiteSource := {b}
  markerSet := {a}
  proxyPath i := nomatch i
  proxy_isRay i := nomatch i

abbrev LV := PopularAuxiliary.Input.LambdaVertex Vertex Empty

def cut : Set LV := {PopularAuxiliary.Input.LambdaVertex.old b}

@[simp] theorem input_finiteSource : input.finiteSource = {b} := rfl

theorem groundedRecord_mem :
    (Sum.inl ab : web.DPath) ∈ input.groundedRecords := by
  exact Set.mem_singleton _

theorem groundedRecord_initial_mem_source :
    DirectedPath.Path.initial (Sum.inl ab : web.DPath) ∈ web.source := by
  change a ∈ ({a} : Set Vertex)
  simp

theorem groundedRecord_terminal_mem_finiteSource :
    DirectedPath.Path.terminal? (Sum.inl ab : web.DPath) = some b ∧
      b ∈ input.finiteSource := by
  constructor
  · rfl
  · simp [input]

theorem finiteSource_not_subset_source :
    ¬ input.finiteSource ⊆ web.source := by
  intro h
  have hb : b ∈ web.source := h (by simp [input])
  simpa [web] using hb

@[simp] theorem cut_CV : GroundingCut.CV input cut = {b} := by
  ext x
  simp [cut, GroundingCut.CV, PopularAuxiliary.Input.oldPart]

@[simp] theorem cut_CE : GroundingCut.CE input cut = ∅ := by
  ext e
  simp [cut, GroundingCut.CE, PopularAuxiliary.Input.edgePart]

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
    exact ⟨Sum.inl ab, Set.mem_singleton _, rfl⟩

theorem essentialLadder_eq : input.essentialLadder = ladderPaths := by
  ext p
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    have hpab : p = (Sum.inl ab : web.DPath) :=
      Set.mem_singleton_iff.mp hp
    subst p
    refine ⟨Set.mem_singleton (Sum.inl ab : web.DPath), b, rfl, ?_⟩
    rw [web.mem_essential_iff]
    refine ⟨?_, ?_⟩
    · refine ⟨Sum.inl ab, Set.mem_singleton _, rfl⟩
    · rw [web.not_mem_roof_iff]
      refine ⟨FinitePath.trivial web.graph b, ⟨rfl, by simp [web]⟩, ?_⟩
      change web.Avoids (FinitePath.trivial web.graph b)
        (web.terminalFrontier ladderPaths \ {b})
      rw [terminalFrontier_ladderPaths]
      have hempty : ({b} : Set Vertex) \ {b} = ∅ := by simp
      rw [hempty]
      exact Set.disjoint_empty _

theorem a_mem_targetMarkers : a ∈ input.targetMarkers := by
  refine ⟨by simp [input], ?_⟩
  rw [essentialLadder_eq]
  refine ⟨Sum.inl ab, Set.mem_singleton _, ?_⟩
  change a ∈ ab.support
  simp

theorem a_mem_escapeRegion : a ∈ input.escapeRegion cut := by
  let q := FinitePath.trivial input.lambda.graph
    (PopularAuxiliary.Input.LambdaVertex.old a : LV)
  exact ⟨{
    route := q
    start_eq := Or.inl rfl
    target := (input.mem_lambda_target_old a).2 a_mem_targetMarkers
    avoids := by
      change Disjoint q.support cut
      simp [q, cut]
    old_not_mem := by simp [cut] }⟩

def wholeFragment : input.Fragment where
  path := Sum.inl ab
  parent := Sum.inl ab
  parent_mem := Set.mem_singleton _
  support_subset := Subset.rfl
  edges_subset := Subset.rfl

theorem wholeFragment_mem_fragments :
    wholeFragment ∈ GroundingCut.fragments input cut := by
  constructor
  · rw [cut_CE]
    exact Set.disjoint_empty _
  · ext x
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      have hx' : x = a ∨ x = b := by
        change x ∈ ab.support at hx
        simpa [GroundingCVFragmentAudit.Concrete.ab_support] using hx
      rcases hx' with rfl | rfl
      · refine ⟨FinitePath.trivial web.graph a, Or.inl ⟨rfl, rfl⟩,
          ?_, ?_, ?_⟩
        · intro y hy
          have hya : y = a := by simpa using hy
          subst y
          change a ∈ ab.support
          simp
        · intro e he
          simp [FinitePath.edgeSet, FinitePath.trivial] at he
        · rw [cut_CE]
          exact Set.disjoint_empty _
      · refine ⟨ab, Or.inl ⟨rfl, rfl⟩, Subset.rfl, Subset.rfl, ?_⟩
        rw [cut_CE]
        exact Set.disjoint_empty _
    · exact fun hx ↦ hx.1

theorem wholeFragment_mem_G0 :
    wholeFragment ∈ GroundingCut.G0 input cut := by
  refine ⟨wholeFragment_mem_fragments, ?_⟩
  rintro ⟨_hfragment, _hwhole, _hrecord, hdiscard⟩
  rcases hdiscard with hterminal | hinfinite
  · obtain ⟨t, ht, htCut⟩ := hterminal
    have htb : t = b := Option.some.inj ht.symm
    subst t
    exact htCut (by simp [cut])
  · exact hinfinite.1 ⟨b, rfl⟩

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

theorem wholeFragment_blockingPoint_eq_a :
    GroundingCut.blockingPoint input cut wholeFragment = a := by
  have hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      input cut wholeFragment := by
    exact ⟨a, by change a ∈ ab.support; simp, a_mem_escapeRegion⟩
  rw [GroundingCut.blockingPoint_eq_first_of_meetsEscape
    input cut wholeFragment hescape]
  apply GroundingCutDecoder.beforeEq_antisymm
  · exact GroundingCut.firstVertex_beforeEq wholeFragment.path
      (input.escapeRegion cut) hescape ⟨wholeFragment.path.initial_mem_support,
        a_mem_escapeRegion⟩
  · have hfirst : GroundingCut.firstVertex wholeFragment.path
        (input.escapeRegion cut) hescape ∈ wholeFragment.path.support :=
      (GroundingCut.firstVertex_mem wholeFragment.path
        (input.escapeRegion cut) hescape).1
    change GroundingCut.BeforeEq wholeFragment.path wholeFragment.path.initial
      (GroundingCut.firstVertex wholeFragment.path
        (input.escapeRegion cut) hescape)
    exact initial_beforeEq hfirst

theorem a_mem_BB : a ∈ GroundingCut.BB input cut := by
  apply GroundingCut.BL_subset_BB
  exact ⟨wholeFragment,
    ⟨wholeFragment_mem_G0, Or.inl
      ⟨a, by change a ∈ ab.support; simp, a_mem_escapeRegion⟩⟩,
    wholeFragment_blockingPoint_eq_a⟩

theorem b_mem_BB : b ∈ GroundingCut.BB input cut := by
  apply GroundingCut.CV_subset_BB
  simp

theorem request_isEmpty : IsEmpty (Request input cut) := by
  constructor
  intro r
  cases r with
  | inl r =>
      have hrb : r.1 = b := by simpa [oldRequests, oldPart, cut] using r.2.1
      exact r.2.2 (by simpa [hrb])
  | inr r => simpa [edgeRequests, edgePart, cut] using r.2

theorem ab_mem_residualEdges :
    (a, b) ∈ input.familyEdges \ GroundingCut.CE input cut := by
  constructor
  · refine ⟨(Sum.inl ab : web.DPath), Set.mem_singleton _, ?_⟩
    change (a, b) ∈ ab.walk.edgeSet
    rw [ab_edgeSet_eq]
    simp
  · rw [cut_CE]
    simp

/-- The literal boundary is not a reachability antichain even though no
switching request exists. -/
theorem residualEdges_not_reachabilityAntichain :
    ¬ IsReachabilityAntichain
      (input.familyEdges \ GroundingCut.CE input cut)
      (GroundingCut.BB input cut) := by
  intro hanti
  have hab : a = b := hanti a_mem_BB b_mem_BB
    (Relation.ReflTransGen.single ab_mem_residualEdges)
  cases hab

end GroundingFiniteSourceBBDuplicateCounterexample
end Erdos599
