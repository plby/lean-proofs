/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CycleDecompositionShortCycles
import Mathlib.Data.Fintype.BigOperators

/-!
# Grouping the short cycles of a cycle decomposition

This file supplies the cardinal arithmetic needed to feed the concrete
short-cycle family into the full KSSS cycle-cover bank.  The edge count of a
pairwise edge-disjoint finite graph family is the sum of its edge counts.
Consequently triangle-divisibility gives the required congruence, while the
large reserve of unused path pairs supplies at least as many four-cycles as
five-cycles.
-/

namespace Erdos207

open Finset
open scoped BigOperators
open CycleDecomposition

noncomputable section

/-- Edge cardinality is additive over a finite pairwise edge-disjoint graph
family. -/
lemma edgeFinset_card_graphSup_eq_sum
    {I Y : Type*} [DecidableEq I] [Finite Y]
    (s : Finset I) (F : I → SimpleGraph Y)
    (hF : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (F i) (F j)) :
    (graphSup s F).edgeSet.ncard =
      ∑ i ∈ s, (F i).edgeSet.ncard := by
  induction s using Finset.induction_on with
  | empty => simp [graphSup]
  | @insert a s ha ih =>
      have had : Disjoint (F a) (graphSup s F) := by
        unfold graphSup
        rw [Finset.disjoint_sup_right]
        intro j hj
        exact hF a (mem_insert_self a s) j (mem_insert_of_mem hj) (by
          intro haj
          subst j
          exact ha hj)
      rw [graphSup_insert, SimpleGraph.edgeSet_sup,
        Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr had), ih]
      · simp only [sum_insert, ha, not_false_eq_true, add_left_inj]
      · intro i hi j hj hij
        exact hF i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij

lemma card_edgeFinset_cycleGraph_three :
    (SimpleGraph.cycleGraph 3).edgeFinset.card = 3 := by decide

lemma card_edgeFinset_cycleGraph_four :
    (SimpleGraph.cycleGraph 4).edgeFinset.card = 4 := by decide

lemma card_edgeFinset_cycleGraph_five :
    (SimpleGraph.cycleGraph 5).edgeFinset.card = 5 := by decide

lemma edgeSet_ncard_eq_edgeFinset_card
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (G : SimpleGraph Y) [DecidableRel G.Adj] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← Set.fintypeCard_eq_ncard, SimpleGraph.edgeFinset_card]

lemma edgeSet_ncard_map_embedding
    {X Y : Type*} (G : SimpleGraph X) (f : X ↪ Y) :
    (G.map f).edgeSet.ncard = G.edgeSet.ncard := by
  rw [SimpleGraph.edgeSet_map,
    Set.ncard_image_of_injective _ f.sym2Map.injective]

lemma card_edgeFinset_shortCycleFamily_graph
    {Y I₃ I₄ I₅ : Type*} [Fintype Y] [DecidableEq Y]
    (F : ShortCycleFamily Y I₃ I₄ I₅)
    (i : ShortCycleIndex I₃ I₄ I₅) :
    (F.graph i).edgeSet.ncard =
      match i with
      | .inl _ => 3
      | .inr (.inl _) => 4
      | .inr (.inr _) => 5 := by
  rcases i with i | (i | i)
  · rw [edgeSet_ncard_map_embedding,
      edgeSet_ncard_eq_edgeFinset_card, card_edgeFinset_cycleGraph_three]
  · rw [edgeSet_ncard_map_embedding,
      edgeSet_ncard_eq_edgeFinset_card, card_edgeFinset_cycleGraph_four]
  · rw [edgeSet_ncard_map_embedding,
      edgeSet_ncard_eq_edgeFinset_card, card_edgeFinset_cycleGraph_five]

/-- The weighted number of short cycles is exactly the number of edges in
their graph supremum. -/
lemma ShortCycleFamily.weighted_count_eq_edgeFinset_card
    {Y I₃ I₄ I₅ : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype I₃] [Fintype I₄] [Fintype I₅]
    [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    (F : ShortCycleFamily Y I₃ I₄ I₅)
    (hF : F.PairwiseDisjoint) :
    3 * Fintype.card I₃ + 4 * Fintype.card I₄ +
        5 * Fintype.card I₅ =
      (graphSup univ F.graph).edgeSet.ncard := by
  rw [edgeFinset_card_graphSup_eq_sum univ F.graph (by
    intro i _ j _ hij
    exact hF i j hij)]
  simp [card_edgeFinset_shortCycleFamily_graph,
    Fintype.sum_sum_type, mul_comm, Nat.add_assoc]

/-- Root-root edges and the universal path-cover graph are edge-disjoint. -/
lemma rootMap_disjoint_pathCoverGraph
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) :
    Disjoint (G.map (pathCoverRootEmbedding (X := V) (k := k)))
      (pathCoverGraph V k) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv huv'
  rw [SimpleGraph.map_adj] at huv
  obtain ⟨a, b, hab, rfl, rfl⟩ := huv
  exact pathCoverGraph_not_adj_root_root a b huv'

lemma cycleRecord_length_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : CycleRecord V) : R.walk.length ≤ Fintype.card V := by
  rw [← Fintype.card_fin R.walk.length]
  exact Fintype.card_le_of_injective
    (walkCycleEmbedding R.walk R.isCycle) (walkCycleEmbedding R.walk R.isCycle).injective

lemma card_decompositionFiveCycleIndex_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : CycleDecomposition G) :
    Fintype.card (DecompositionFiveCycleIndex D) ≤
      D.cycleCount * Fintype.card V := by
  rw [Fintype.card_sigma]
  calc
    (∑ c : Fin D.cycleCount,
        Fintype.card (Fin ((D.cycleRecordAt c).walk.length - 2))) =
        ∑ c : Fin D.cycleCount,
          ((D.cycleRecordAt c).walk.length - 2) := by simp
    _ ≤ ∑ _c : Fin D.cycleCount, Fintype.card V := by
      apply sum_le_sum
      intro c _
      exact (Nat.sub_le _ _).trans
        (cycleRecord_length_le_card (D.cycleRecordAt c))
    _ = D.cycleCount * Fintype.card V := by simp

lemma pred_le_choose_two (m : ℕ) (hm : 2 ≤ m) :
    m - 1 ≤ m.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  calc
    (m - 1) * 2 ≤ (m - 1) * m := Nat.mul_le_mul_left _ hm
    _ = m * (m - 1) := Nat.mul_comm _ _

lemma card_decompositionUnusedFourIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (m : ℕ) (D : CycleDecomposition G) :
    Fintype.card (DecompositionUnusedFourIndex m D) =
      (Fintype.card V).choose 2 * (3 * m ^ 2 - D.cycleCount) := by
  change Fintype.card
      ((SimpleGraph.completeGraph V).edgeSet ×
        Fin (unusedPathPairCount m D.cycleCount)) = _
  rw [Fintype.card_prod, Fintype.card_fin]
  have hedge : Fintype.card (SimpleGraph.completeGraph V).edgeSet =
      (Fintype.card V).choose 2 := by
    rw [← SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  rw [hedge]
  rfl

/-- When the path-cover parameter is the number of root vertices, its unused
four-cycles already dominate all chain five-cycles. -/
lemma card_fiveCycle_le_unusedFour
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hV : 2 ≤ Fintype.card V)
    (D : CycleDecomposition G)
    (hD : D.cycleCount < (Fintype.card V) ^ 2) :
    Fintype.card (DecompositionFiveCycleIndex D) ≤
      Fintype.card
        (DecompositionUnusedFourIndex (Fintype.card V) D) := by
  let m := Fintype.card V
  have hchoose : m - 1 ≤ m.choose 2 := pred_le_choose_two m hV
  have hpairs : 2 * m ^ 2 ≤ 3 * m ^ 2 - D.cycleCount := by
    dsimp only [m]
    omega
  have hscale : m ≤ 2 * (m - 1) := by
    dsimp only [m]
    omega
  rw [card_decompositionUnusedFourIndex]
  refine (card_decompositionFiveCycleIndex_le D).trans ?_
  change D.cycleCount * m ≤ m.choose 2 * (3 * m ^ 2 - D.cycleCount)
  calc
    D.cycleCount * m ≤ m ^ 2 * m := Nat.mul_le_mul_right m hD.le
    _ ≤ m ^ 2 * (2 * (m - 1)) := Nat.mul_le_mul_left _ hscale
    _ = (m - 1) * (2 * m ^ 2) := by ring
    _ ≤ m.choose 2 * (3 * m ^ 2 - D.cycleCount) :=
      Nat.mul_le_mul hchoose hpairs

lemma card_fiveCycle_le_fourCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hV : 2 ≤ Fintype.card V)
    (D : CycleDecomposition G)
    (hD : D.cycleCount < (Fintype.card V) ^ 2) :
    Fintype.card (DecompositionFiveCycleIndex D) ≤
      Fintype.card
        (DecompositionFourCycleIndex (Fintype.card V) D) := by
  rw [Fintype.card_sum]
  exact (card_fiveCycle_le_unusedFour hV D hD).trans
    (Nat.le_add_left _ _)

lemma completedAugmentedGraph_edge_count_divisible
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : TriangleDivisible G) (D : CycleDecomposition G)
    (hD : D.cycleCount < (Fintype.card V) ^ 2) :
    3 ∣ (D.completedAugmentedGraph (Fintype.card V) hD).edgeSet.ncard := by
  classical
  rw [completedAugmentedGraph_eq,
    SimpleGraph.edgeSet_sup,
    Set.ncard_union_eq
      (SimpleGraph.disjoint_edgeSet.mpr
        (rootMap_disjoint_pathCoverGraph G)),
    edgeSet_ncard_map_embedding,
    edgeSet_ncard_eq_edgeFinset_card G,
    edgeSet_ncard_eq_edgeFinset_card
      (pathCoverGraph V (6 * (Fintype.card V) ^ 2))]
  exact Nat.dvd_add hG.2
    (pathCoverGraph_triangleDivisible (X := V) (Fintype.card V)).2

/-- The completed cycle/path-cover expansion admits exactly the full bounded
cycle-cover grouping required by the KSSS absorber bank. -/
theorem CycleDecomposition.hasFullCycleCoverGrouping_completed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : 2 ≤ Fintype.card V) (hG : TriangleDivisible G)
    (D : CycleDecomposition G) :
    let hD := D.cycleCount_lt_card_sq hV
    HasFullCycleCoverGrouping
      ((D.completedAugmentedGraph (Fintype.card V) hD).map
        (fullCycleCoverBaseEmbedding
          (PathCoverVertex V (6 * (Fintype.card V) ^ 2)))) := by
  let m := Fintype.card V
  let hD : D.cycleCount < m ^ 2 := D.cycleCount_lt_card_sq hV
  let F := D.shortCycleFamily m hD
  have hpair : F.PairwiseDisjoint := shortCycleFamily_pairwiseDisjoint m D hD
  have hmore : Fintype.card (DecompositionFiveCycleIndex D) ≤
      Fintype.card (DecompositionFourCycleIndex m D) := by
    exact card_fiveCycle_le_fourCycle hV D hD
  have hdiv : 3 ∣
      3 * Fintype.card (DecompositionTriangleIndex D) +
        4 * Fintype.card (DecompositionFourCycleIndex m D) +
          5 * Fintype.card (DecompositionFiveCycleIndex D) := by
    rw [F.weighted_count_eq_edgeFinset_card hpair,
      show F = D.shortCycleFamily m hD from rfl]
    unfold graphSup
    rw [Finset.sup_univ_eq_iSup,
      iSup_shortCycleFamily_eq_completedAugmentedGraph]
    exact completedAugmentedGraph_edge_count_divisible hG D hD
  obtain ⟨k, hk⟩ := shortCycle_counts_groupable _ _ _ hmore hdiv
  have hgroup := hasFullCycleCoverGrouping_of_shortCycles F hpair k hk
  change HasFullCycleCoverGrouping
    ((graphSup univ (D.shortCycleFamily m hD).graph).map
      (fullCycleCoverBaseEmbedding
        (PathCoverVertex V (6 * m ^ 2)))) at hgroup
  rw [graphSup_shortCycleFamily_eq_completedAugmentedGraph] at hgroup
  simpa only [m] using hgroup

end

end Erdos207
