/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPairAvailabilityUnrestricted
import ErdosProblems.Erdos207.InitialPairAverage
import ErdosProblems.Erdos207.PairSharingCount

/-! # All initial residual pairs, including pairs whose stars might be empty -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

def initialResidualPairs {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) : Finset (Finset V) :=
  ((univ : Finset V).powersetCard 2).filter fun P ↦
    ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ H.Adj u v

theorem mem_initialResidualPairs
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (P : Finset V) :
    P ∈ initialResidualPairs H ↔ P.card = 2 ∧ ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ H.Adj u v := by
  simp only [initialResidualPairs, mem_filter, mem_powersetCard, subset_univ, true_and]

theorem initialResidualPairs_card_le
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) :
    (initialResidualPairs H).card ≤ Fintype.card V ^ 2 := by
  have hsub : initialResidualPairs H ⊆ (univ : Finset V).powersetCard 2 := filter_subset _ _
  calc
    _ ≤ ((univ : Finset V).powersetCard 2).card := card_le_card hsub
    _ = (Fintype.card V).choose 2 := by simp
    _ ≤ _ := Nat.choose_le_pow _ _

theorem initialResidualPairs_cover_available
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V)
    {P : Finset V} (hP : P.card = 2)
    (hstar : (availableTrianglesContainingPair (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)) P).Nonempty) :
    P ∈ initialResidualPairs H := by
  obtain ⟨T, hT⟩ := hstar
  obtain ⟨hTavailable, hPT⟩ := mem_availableTrianglesContainingPair_iff.mp hT
  have houtside := (mem_legalAvailable_iff.mp hTavailable).1
  have havoid := (mem_outsideAvailableTriangles_iff.mp houtside).2
  exact (mem_initialResidualPairs H P).mpr ⟨hP, fun u hu v hv hne ↦ havoid u (hPT hu) v (hPT hv) hne⟩

theorem initialResidualPairs_initial_degree_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {bank : TripleSystemOn V}
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn bank).card ≤ C) {P : Finset V} (hP : P ∈ initialResidualPairs H) :
    (Fintype.card V : ℝ) - (3 * (C : ℝ) + 2) ≤
      ((availableTrianglesContainingPair (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)) P).card : ℝ) ∧
    ((availableTrianglesContainingPair (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)) P).card : ℝ) ≤
      Fintype.card V := by
  have hp := (mem_initialResidualPairs H P).mp hP
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hp.1
  have hnotH : ¬ H.Adj u v := hp.2 u (by simp) v (by simp) huv
  have hlower := card_sub_two_le_initialPairStar_add_three_mul_unrestricted (q := q) hdegree hsupport huv hnotH
  have hnat : Fintype.card V ≤ (availableTrianglesContainingPair (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)) {u, v}).card + 3 * C + 2 :=
    (Nat.sub_le_iff_le_add).mp hlower
  have hreal : (Fintype.card V : ℝ) ≤
      ((availableTrianglesContainingPair (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
        (outsideAvailableTriangles H bank)) {u, v}).card : ℝ) + 3 * (C : ℝ) + 2 := by exact_mod_cast hnat
  refine ⟨by linarith only [hreal], ?_⟩
  have hsub : availableTrianglesContainingPair (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)) {u, v} ⊆
      universeTriplesContainingPair {u, v} := fun _ hT ↦
    mem_universeTriplesContainingPair_iff.mpr (mem_availableTrianglesContainingPair_iff.mp hT).2
  exact_mod_cast (card_le_card hsub).trans (card_universeTriplesContainingPair_le V {u, v} (by simp [huv]))

end

end Erdos207
