/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPairAvailability

/-!
# Initial global availability

The initial lower bound for every nonexceptional pair is converted into a
global cubic availability bound.  The conversion is exact: summing all
available pair-stars counts every available triple three times.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

lemma sum_pairIndicators_eq_three
    {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    (∑ P : PairOn V, if P.1 ⊆ T.1 then 1 else 0) = 3 := by
  let e : PairOn V ↪ Finset V := Function.Embedding.subtype _
  have hmap :
      ((univ.filter fun P : PairOn V ↦ P.1 ⊆ T.1).map e) =
        T.1.powersetCard 2 := by
    ext P
    simp only [mem_map, mem_filter, mem_univ, true_and,
      mem_powersetCard]
    constructor
    · rintro ⟨Q, hQT, hQP⟩
      subst P
      exact ⟨hQT, Q.2⟩
    · rintro ⟨hPT, hPcard⟩
      exact ⟨⟨P, hPcard⟩, hPT, rfl⟩
  calc
    (∑ P : PairOn V, if P.1 ⊆ T.1 then 1 else 0) =
        (univ.filter fun P : PairOn V ↦ P.1 ⊆ T.1).card := by simp
    _ = (T.1.powersetCard 2).card := by
      rw [← hmap, card_map]
    _ = 3 := by rw [card_powersetCard, T.2]; norm_num

/-- Every available triangle contributes once to each of its three pairs. -/
theorem sum_card_availableTrianglesContainingPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) :
    ∑ P : PairOn V, (availableTrianglesContainingPair S P.1).card =
      3 * S.available.card := by
  calc
    ∑ P : PairOn V, (availableTrianglesContainingPair S P.1).card =
        ∑ P : PairOn V, ∑ T ∈ S.available,
          if P.1 ⊆ T.1 then 1 else 0 := by
      apply sum_congr rfl
      intro P _hP
      rw [availableTrianglesContainingPair, card_eq_sum_ones, sum_filter]
    _ = ∑ T ∈ S.available, ∑ P : PairOn V,
          if P.1 ⊆ T.1 then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ _T ∈ S.available, 3 := by
      apply sum_congr rfl
      intro T _hT
      exact sum_pairIndicators_eq_three T
    _ = 3 * S.available.card := by simp [Nat.mul_comm]

lemma sum_orderedPairIndicators_eq_six
    {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    (∑ u : V, ∑ v ∈ (univ.erase u),
      if ({u, v} : Finset V) ⊆ T.1 then 1 else 0) = 6 := by
  have hinner : ∀ u : V,
      (∑ v ∈ (univ.erase u),
        if ({u, v} : Finset V) ⊆ T.1 then 1 else 0) =
        if u ∈ T.1 then 2 else 0 := by
    intro u
    by_cases hu : u ∈ T.1
    · have hfilter :
          (univ.erase u).filter
              (fun v ↦ ({u, v} : Finset V) ⊆ T.1) =
            T.1.erase u := by
        ext v
        simp only [mem_filter, mem_erase, mem_univ, and_true]
        constructor
        · rintro ⟨hvu, hsub⟩
          exact ⟨hvu, hsub (by simp)⟩
        · rintro ⟨hvu, hvT⟩
          refine ⟨hvu, ?_⟩
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hu
          · exact hvT
      calc
        (∑ v ∈ (univ.erase u),
            if ({u, v} : Finset V) ⊆ T.1 then 1 else 0) =
            ((univ.erase u).filter
              (fun v ↦ ({u, v} : Finset V) ⊆ T.1)).card := by
          rw [card_eq_sum_ones, sum_filter]
        _ = (T.1.erase u).card := by rw [hfilter]
        _ = 2 := by rw [card_erase_of_mem hu, T.2]
        _ = if u ∈ T.1 then 2 else 0 := by simp [hu]
    · simp only [if_neg hu]
      apply sum_eq_zero
      intro v hv
      simp only [ite_eq_right_iff]
      intro hsub
      exact (hu (hsub (by simp))).elim
  calc
    (∑ u : V, ∑ v ∈ (univ.erase u),
        if ({u, v} : Finset V) ⊆ T.1 then 1 else 0) =
        ∑ u : V, if u ∈ T.1 then 2 else 0 := by
      apply sum_congr rfl
      intro u _hu
      exact hinner u
    _ = ∑ _u ∈ T.1, 2 := by
      rw [sum_ite_mem, inter_eq_right.mpr (subset_univ T.1)]
    _ = 6 := by simp [T.2]

/-- Equivalently, summing over ordered distinct endpoints counts every
available triangle six times. -/
theorem sum_ordered_card_availableTrianglesContainingPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) :
    ∑ u : V, ∑ v ∈ (univ.erase u),
        (availableTrianglesContainingPair S {u, v}).card =
      6 * S.available.card := by
  calc
    ∑ u : V, ∑ v ∈ (univ.erase u),
        (availableTrianglesContainingPair S {u, v}).card =
        ∑ u : V, ∑ v ∈ (univ.erase u), ∑ T ∈ S.available,
          if ({u, v} : Finset V) ⊆ T.1 then 1 else 0 := by
      apply sum_congr rfl
      intro u _hu
      apply sum_congr rfl
      intro v _hv
      rw [availableTrianglesContainingPair, card_eq_sum_ones, sum_filter]
    _ = ∑ T ∈ S.available, ∑ u : V, ∑ v ∈ (univ.erase u),
          if ({u, v} : Finset V) ⊆ T.1 then 1 else 0 := by
      simp_rw [sum_comm (s := univ.erase _)]
      rw [sum_comm]
    _ = ∑ _T ∈ S.available, 6 := by
      apply sum_congr rfl
      intro T _hT
      exact sum_orderedPairIndicators_eq_six T
    _ = 6 * S.available.card := by simp [Nat.mul_comm]

/-- Vertices distinct from `u` which are not joined to `u` in `H`. -/
def graphGoodPartners
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (u : V) : Finset V :=
  (univ.erase u) \ H.neighborFinset u

@[simp]
lemma mem_graphGoodPartners_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {u v : V} :
    v ∈ graphGoodPartners H u ↔ v ≠ u ∧ ¬H.Adj u v := by
  simp [graphGoodPartners, SimpleGraph.mem_neighborFinset]

lemma graphGoodPartners_subset_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (u : V) :
    graphGoodPartners H u ⊆ univ.erase u :=
  sdiff_subset

lemma card_sub_degree_add_one_le_graphGoodPartners
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (u : V) :
    Fintype.card V - (H.degree u + 1) ≤
      (graphGoodPartners H u).card := by
  have hneighbors : H.neighborFinset u ⊆ (univ.erase u) := by
    intro v hv
    have hadj : H.Adj u v := by
      simpa only [SimpleGraph.mem_neighborFinset] using hv
    exact mem_erase.mpr ⟨(H.ne_of_adj hadj).symm, mem_univ v⟩
  rw [graphGoodPartners, card_sdiff_of_subset hneighbors,
    card_erase_of_mem (mem_univ u), card_univ,
    SimpleGraph.card_neighborFinset_eq_degree]
  omega

lemma card_sub_add_one_le_graphGoodPartners_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {C : ℕ}
    (hdegree : ∀ x, H.degree x ≤ C) (u : V) :
    Fintype.card V - (C + 1) ≤ (graphGoodPartners H u).card := by
  have hmain := card_sub_degree_add_one_le_graphGoodPartners H u
  have hu := hdegree u
  omega

/-- The local initial codegree estimate summed over nonflexible first
endpoints.  This is a division-free cubic lower bound for the initial global
availability. -/
theorem initial_globalAvailability_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C L : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    (hXcard : X.card ≤ C)
    (hlarge : L + 3 * C + 2 ≤ Fintype.card V) :
    (Fintype.card V - C) * (Fintype.card V - (C + 1)) * L ≤
      6 * (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available.card := by
  let S₀ := absorberGreedyInitialState
    (absorberErdosForbiddenConfigurationsOn q B)
    (outsideAvailableTriangles H B)
  have houtside : Fintype.card V - C ≤ (univ \ X).card := by
    rw [card_sdiff_of_subset (subset_univ X), card_univ]
    omega
  have hper : ∀ u ∈ (univ \ X),
      (Fintype.card V - (C + 1)) * L ≤
        ∑ v ∈ (univ.erase u),
          (availableTrianglesContainingPair S₀ {u, v}).card := by
    intro u hu
    have huX : u ∉ X := (mem_sdiff.mp hu).2
    have hpartners :=
      card_sub_add_one_le_graphGoodPartners_of_degree hdegree u
    calc
      (Fintype.card V - (C + 1)) * L ≤
          (graphGoodPartners H u).card * L :=
        Nat.mul_le_mul_right L hpartners
      _ = ∑ _v ∈ graphGoodPartners H u, L := by simp
      _ ≤ ∑ v ∈ graphGoodPartners H u,
          (availableTrianglesContainingPair S₀ {u, v}).card := by
        apply sum_le_sum
        intro v hv
        have hvdata := mem_graphGoodPartners_iff.mp hv
        have hlocal := card_sub_two_le_initialPairStar_add_three_mul
          (q := q) hbank hdegree hsupport hvdata.1.symm hvdata.2
        dsimp only [S₀]
        omega
      _ ≤ ∑ v ∈ (univ.erase u),
          (availableTrianglesContainingPair S₀ {u, v}).card := by
        exact sum_le_sum_of_subset (graphGoodPartners_subset_erase H u)
  calc
    (Fintype.card V - C) * (Fintype.card V - (C + 1)) * L ≤
        (univ \ X).card *
          ((Fintype.card V - (C + 1)) * L) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_right _ houtside
    _ = ∑ _u ∈ (univ \ X),
        ((Fintype.card V - (C + 1)) * L) := by simp
    _ ≤ ∑ u ∈ (univ \ X), ∑ v ∈ (univ.erase u),
        (availableTrianglesContainingPair S₀ {u, v}).card := by
      apply sum_le_sum
      intro u hu
      exact hper u hu
    _ ≤ ∑ u : V, ∑ v ∈ (univ.erase u),
        (availableTrianglesContainingPair S₀ {u, v}).card := by
      exact sum_le_sum_of_subset (sdiff_subset : (univ \ X) ⊆ univ)
    _ = 6 * S₀.available.card :=
      sum_ordered_card_availableTrianglesContainingPair S₀
    _ = 6 * (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)).available.card := rfl

end

end Erdos207
