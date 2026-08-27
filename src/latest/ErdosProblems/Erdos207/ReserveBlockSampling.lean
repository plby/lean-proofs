/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBlockConcentration
import ErdosProblems.Erdos207.ReserveEdgeSampling

/-!
# Concentration for disjoint reserve-edge blocks

This specializes independent block activation to the crossing-edge reserve
used in the KSSS master iteration.  A block of `d` crossing edges is active
with probability exactly `r^d`; pairwise-disjoint blocks therefore obey the
usual binomial union bounds without any unproved independence assertion.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma blockProbability_reserveEdgeProbability
    {V J : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0)
    (blocks : J → Finset (Sym2 V)) (j : J)
    (hj : blocks j ⊆ crossingEdges G U) :
    blockProbability (reserveEdgeProbability G U r) blocks j =
      r ^ (blocks j).card := by
  unfold blockProbability
  calc
    ∏ e ∈ blocks j, reserveEdgeProbability G U r e =
        ∏ _e ∈ blocks j, r := by
      apply prod_congr rfl
      intro e he
      simp [reserveEdgeProbability, hj he]
    _ = r ^ (blocks j).card := by simp

/-- Exact joint law for prescribed active and inactive reserve blocks. -/
theorem reserveEdgeLaw_probability_block_pattern
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (blocks : J → Finset (Sym2 V)) (A B : Finset J)
    (hcross : ∀ j ∈ A ∪ B, blocks j ⊆ crossingEdges G U)
    (hpair : ((A ∪ B : Finset J) : Set J).PairwiseDisjoint blocks)
    (hAB : Disjoint A B) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦
          (∀ j ∈ A, IsBlockActive blocks j ω) ∧
          (∀ j ∈ B, ¬ IsBlockActive blocks j ω)) =
      (∏ j ∈ A, r ^ (blocks j).card) *
        ∏ j ∈ B, (1 - r ^ (blocks j).card) := by
  unfold reserveEdgeLaw
  rw [independentBits_probability_block_pattern
    (reserveEdgeProbability G U r)
    (reserveEdgeProbability_le_one G U hr) blocks A B hpair hAB]
  congr 1
  · apply prod_congr rfl
    intro j hj
    exact blockProbability_reserveEdgeProbability G U r blocks j
      (hcross j (mem_union_left B hj))
  · apply prod_congr rfl
    intro j hj
    rw [blockProbability_reserveEdgeProbability G U r blocks j
      (hcross j (mem_union_right A hj))]

/-- Upper binomial tail for equal-sized disjoint reserve blocks. -/
theorem reserveEdgeLaw_probability_activeBlocks_card_ge_le
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (blocks : J → Finset (Sym2 V)) (S : Finset J)
    (hcross : ∀ j ∈ S, blocks j ⊆ crossingEdges G U)
    (hpair : (S : Set J).PairwiseDisjoint blocks)
    (d k : ℕ) (hcard : ∀ j ∈ S, (blocks j).card = d) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) ≤
      (Nat.choose S.card k : ℝ≥0) * (r ^ d) ^ k := by
  have hbase := independentBits_probability_activeBlocks_card_ge_le
    (reserveEdgeProbability G U r)
    (reserveEdgeProbability_le_one G U hr) blocks S hpair k
  unfold reserveEdgeLaw
  calc
    (FiniteLaw.independentBits (reserveEdgeProbability G U r)
        (reserveEdgeProbability_le_one G U hr)).probability
        (fun ω ↦ k ≤ (activeBlocks blocks S ω).card) ≤
      ∑ T ∈ S.powersetCard k,
        ∏ j ∈ T, blockProbability
          (reserveEdgeProbability G U r) blocks j := hbase
    _ = ∑ _T ∈ S.powersetCard k, (r ^ d) ^ k := by
      apply sum_congr rfl
      intro T hT
      have hTdata := mem_powersetCard.mp hT
      calc
        ∏ j ∈ T, blockProbability
            (reserveEdgeProbability G U r) blocks j =
          ∏ _j ∈ T, r ^ d := by
            apply prod_congr rfl
            intro j hj
            rw [blockProbability_reserveEdgeProbability G U r blocks j
              (hcross j (hTdata.1 hj)), hcard j (hTdata.1 hj)]
        _ = (r ^ d) ^ k := by simp [hTdata.2]
    _ = (Nat.choose S.card k : ℝ≥0) * (r ^ d) ^ k := by
      simp [card_powersetCard]

/-- Lower binomial tail for equal-sized disjoint reserve blocks. -/
theorem reserveEdgeLaw_probability_activeBlocks_card_le_le
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (blocks : J → Finset (Sym2 V)) (S : Finset J)
    (hcross : ∀ j ∈ S, blocks j ⊆ crossingEdges G U)
    (hpair : (S : Set J).PairwiseDisjoint blocks)
    (d k : ℕ) (hcard : ∀ j ∈ S, (blocks j).card = d) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) ≤
      (Nat.choose S.card (S.card - k) : ℝ≥0) *
        (1 - r ^ d) ^ (S.card - k) := by
  have hbase := independentBits_probability_activeBlocks_card_le_le
    (reserveEdgeProbability G U r)
    (reserveEdgeProbability_le_one G U hr) blocks S hpair k
  unfold reserveEdgeLaw
  calc
    (FiniteLaw.independentBits (reserveEdgeProbability G U r)
        (reserveEdgeProbability_le_one G U hr)).probability
        (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) ≤
      ∑ T ∈ S.powersetCard (S.card - k),
        ∏ j ∈ T, (1 - blockProbability
          (reserveEdgeProbability G U r) blocks j) := hbase
    _ = ∑ _T ∈ S.powersetCard (S.card - k),
          (1 - r ^ d) ^ (S.card - k) := by
      apply sum_congr rfl
      intro T hT
      have hTdata := mem_powersetCard.mp hT
      calc
        ∏ j ∈ T, (1 - blockProbability
            (reserveEdgeProbability G U r) blocks j) =
          ∏ _j ∈ T, (1 - r ^ d) := by
            apply prod_congr rfl
            intro j hj
            rw [blockProbability_reserveEdgeProbability G U r blocks j
              (hcross j (hTdata.1 hj)), hcard j (hTdata.1 hj)]
        _ = (1 - r ^ d) ^ (S.card - k) := by simp [hTdata.2]
    _ = (Nat.choose S.card (S.card - k) : ℝ≥0) *
          (1 - r ^ d) ^ (S.card - k) := by
      simp [card_powersetCard]

/-- Exponential lower tail for equal-sized disjoint reserve blocks. -/
theorem reserveEdgeLaw_probability_activeBlocks_card_le_le_exp
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (blocks : J → Finset (Sym2 V)) (S : Finset J)
    (hcross : ∀ j ∈ S, blocks j ⊆ crossingEdges G U)
    (hpair : (S : Set J).PairwiseDisjoint blocks)
    (d k : ℕ) (hcard : ∀ j ∈ S, (blocks j).card = d)
    (hk : (k : ℝ) ≤ ((r ^ d : ℝ≥0) : ℝ) * S.card / 4) :
    ((reserveEdgeLaw G U r hr).probability
        (fun ω ↦ (activeBlocks blocks S ω).card ≤ k) : ℝ) ≤
      Real.exp (-(((r ^ d : ℝ≥0) : ℝ) * S.card) / 4) := by
  have huniform : ∀ j ∈ S,
      blockProbability (reserveEdgeProbability G U r) blocks j = r ^ d := by
    intro j hj
    rw [blockProbability_reserveEdgeProbability G U r blocks j (hcross j hj),
      hcard j hj]
  have hqle : r ^ d ≤ (1 : ℝ≥0) :=
    pow_le_one₀ (by positivity) hr
  exact independentBits_probability_activeBlocks_card_le_le_exp
    (reserveEdgeProbability G U r)
    (reserveEdgeProbability_le_one G U hr) blocks S hpair
    (r ^ d) hqle huniform k hk

end

end Erdos207
