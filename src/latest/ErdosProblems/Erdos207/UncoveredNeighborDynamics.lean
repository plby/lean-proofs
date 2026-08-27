/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredPairKernel
import ErdosProblems.Erdos207.DriftErrorArithmetic

/-! # Exact uncovered-neighbor dynamics for arbitrary fixed vertex subsets -/

namespace Erdos207

open Finset

noncomputable section

def uncoveredNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset (Finset V)) (U : Finset V) (v : V) (S : GreedyStateOn V) : Finset V :=
  U.filter fun u ↦ u ≠ v ∧ {v, u} ∈ Q ∧ PairUncovered {v, u} S

def uncoveredNeighborLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset (Finset V)) (U : Finset V) (v : V) (S : GreedyStateOn V) (T : TripleOn V) : Finset V :=
  (uncoveredNeighbors Q U v S).filter fun u ↦ {v, u} ⊆ T.1

theorem pairUncovered_greedyStep_iff_and
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V) (T : TripleOn V)
    (hP : P.card = 2) : PairUncovered P (greedyStep F S T) ↔ PairUncovered P S ∧ ¬ P ⊆ T.1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hcovered
      obtain ⟨R, hR, hPR, hcard⟩ := mem_chosenPairFinsets_iff.mp hcovered
      exact h (mem_chosenPairFinsets_iff.mpr ⟨R, mem_insert_of_mem hR, hPR, hcard⟩)
    · intro hPT
      exact h (mem_chosenPairFinsets_iff.mpr ⟨T, mem_insert_self _ _, hPT, hP⟩)
  · rintro ⟨h, hPT⟩ hcovered
    obtain ⟨R, hR, hPR, hcard⟩ := mem_chosenPairFinsets_iff.mp hcovered
    rcases mem_insert.mp hR with rfl | hR
    · exact hPT hPR
    · exact h (mem_chosenPairFinsets_iff.mpr ⟨R, hR, hPR, hcard⟩)

theorem uncoveredNeighbors_greedyStep
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : Finset (Finset V)) (U : Finset V) (v : V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    uncoveredNeighbors Q U v (greedyStep F S T) =
      (uncoveredNeighbors Q U v S).filter fun u ↦ ¬ {v, u} ⊆ T.1 := by
  ext u
  by_cases huv : u = v
  · subst u
    simp [uncoveredNeighbors]
  · have hpair : ({v, u} : Finset V).card = 2 := by simp [Ne.symm huv]
    simp only [uncoveredNeighbors, mem_filter, pairUncovered_greedyStep_iff_and F S _ T hpair]
    tauto

theorem uncoveredNeighborLoss_card_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset (Finset V)) (U : Finset V) (v : V) (S : GreedyStateOn V) (T : TripleOn V) :
    (uncoveredNeighborLoss Q U v S T).card ≤ 2 := by
  by_cases hv : v ∈ T.1
  · have hsub : uncoveredNeighborLoss Q U v S T ⊆ T.1.erase v := by
      intro u hu
      have hdata := mem_filter.mp hu
      have hne := (mem_filter.mp hdata.1).2.1
      exact mem_erase.mpr ⟨hne, hdata.2 (by simp)⟩
    have hcard := card_le_card hsub
    rw [card_erase_of_mem hv, T.2] at hcard
    exact hcard
  · have hempty : uncoveredNeighborLoss Q U v S T = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hv ((mem_filter.mp hu).2 (by simp))
    simp [hempty]

theorem uncoveredNeighbors_step_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : Finset (Finset V)) (U : Finset V) (v : V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    ((uncoveredNeighbors Q U v (greedyStep F S T)).card : ℝ) -
      (uncoveredNeighbors Q U v S).card = -((uncoveredNeighborLoss Q U v S T).card : ℝ) := by
  have hnat : (uncoveredNeighborLoss Q U v S T).card +
      (uncoveredNeighbors Q U v (greedyStep F S T)).card = (uncoveredNeighbors Q U v S).card := by
    rw [uncoveredNeighbors_greedyStep]
    exact card_filter_add_card_filter_not _
  have hreal : ((uncoveredNeighborLoss Q U v S T).card : ℝ) +
      (uncoveredNeighbors Q U v (greedyStep F S T)).card = (uncoveredNeighbors Q U v S).card := by
    exact_mod_cast hnat
  linarith only [hreal]

theorem sum_uncoveredNeighborLoss_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset (Finset V)) (U : Finset V) (v : V) (S : GreedyStateOn V) :
    ∑ T ∈ S.available, (uncoveredNeighborLoss Q U v S T).card =
      ∑ u ∈ uncoveredNeighbors Q U v S, (availableTrianglesContainingPair S {v, u}).card := by
  simp only [uncoveredNeighborLoss, availableTrianglesContainingPair, card_eq_sum_ones, sum_filter]
  rw [sum_comm]

theorem greedyKernel_uncoveredNeighbor_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : Finset (Finset V)) (U : Finset V) (v : V)
    (S : GreedyStateOn V) (hA : S.available.Nonempty) :
    (greedyKernel F S).expectationReal (fun S' ↦
      ((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card) =
      -(∑ u ∈ uncoveredNeighbors Q U v S, ((availableTrianglesContainingPair S {v, u}).card : ℝ)) /
        S.available.card := by
  rw [greedyKernel_expectationReal_increment_of_nonempty F S hA]
  simp_rw [uncoveredNeighbors_step_increment]
  have hsum : (∑ T : S.available, ((uncoveredNeighborLoss Q U v S T).card : ℝ)) =
      ∑ u ∈ uncoveredNeighbors Q U v S, ((availableTrianglesContainingPair S {v, u}).card : ℝ) := by
    calc
      _ = ∑ T ∈ S.available, ((uncoveredNeighborLoss Q U v S T).card : ℝ) := by
        rw [Finset.univ_eq_attach]
        exact sum_attach S.available (fun T ↦ ((uncoveredNeighborLoss Q U v S T).card : ℝ))
      _ = _ := by exact_mod_cast sum_uncoveredNeighborLoss_card Q U v S
  rw [sum_neg_distrib, hsum]
  ring

end

end Erdos207
