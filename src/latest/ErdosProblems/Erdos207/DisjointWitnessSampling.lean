/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightSystem
import ErdosProblems.Erdos207.JointInclusionFactorialTail

/-! # Disjoint witness sets retain a product of their total weights -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.probability_forced_disjointWitnesses_le
    {Ω I J : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw Ω) (selected : Ω → Finset I) (pi : I → ℝ≥0)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ A ⊆ selected omega) ≤ setWeight pi A)
    (alternatives : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint alternatives)
    (U : Finset I) (hU : ∀ j ∈ S, Disjoint U (alternatives j)) :
    L.probability (fun omega ↦ U ⊆ selected omega ∧
      ∀ j ∈ S, ∃ x ∈ alternatives j, x ∈ selected omega) ≤
        setWeight pi U * ∏ j ∈ S, ∑ x ∈ alternatives j, pi x := by
  induction S using Finset.induction_on generalizing U with
  | empty => simpa using hjoint U
  | @insert j S hjS ih =>
      have hpairS : (S : Set J).PairwiseDisjoint alternatives :=
        fun a ha b hb hab ↦ hpair (mem_insert_of_mem ha) (mem_insert_of_mem hb) hab
      have hxU (x : I) (hx : x ∈ alternatives j) : x ∉ U := by
        intro hxU
        exact disjoint_left.mp (hU j (mem_insert_self j S)) hxU hx
      have hnew (x : I) (hx : x ∈ alternatives j) :
          ∀ k ∈ S, Disjoint (insert x U) (alternatives k) := by
        intro k hk
        have hjk : j ≠ k := fun heq ↦ hjS (heq ▸ hk)
        have hblocks := hpair (mem_insert_self j S) (mem_insert_of_mem hk) hjk
        apply disjoint_left.mpr
        intro i hi hik
        rcases mem_insert.mp hi with rfl | hi
        · exact disjoint_left.mp hblocks hx hik
        · exact disjoint_left.mp (hU k (mem_insert_of_mem hk)) hi hik
      calc
        _ ≤ L.probability (fun omega ↦ ∃ x ∈ alternatives j,
            insert x U ⊆ selected omega ∧ ∀ k ∈ S, ∃ y ∈ alternatives k, y ∈ selected omega) := by
          apply L.probability_mono
          intro omega homega
          obtain ⟨x, hx, hxt⟩ := homega.2 j (mem_insert_self j S)
          exact ⟨x, hx, insert_subset_iff.mpr ⟨hxt, homega.1⟩,
            fun k hk ↦ homega.2 k (mem_insert_of_mem hk)⟩
        _ ≤ ∑ x ∈ alternatives j, L.probability (fun omega ↦
            insert x U ⊆ selected omega ∧ ∀ k ∈ S, ∃ y ∈ alternatives k, y ∈ selected omega) :=
          L.probability_exists_le _ _
        _ ≤ ∑ x ∈ alternatives j, setWeight pi (insert x U) *
            ∏ k ∈ S, ∑ y ∈ alternatives k, pi y := by
          apply sum_le_sum
          intro x hx
          exact ih hpairS _ (hnew x hx)
        _ = setWeight pi U * ∏ k ∈ insert j S, ∑ y ∈ alternatives k, pi y := by
          rw [prod_insert hjS]
          calc
            _ = ∑ x ∈ alternatives j, (pi x * setWeight pi U) *
                ∏ k ∈ S, ∑ y ∈ alternatives k, pi y := by
              apply sum_congr rfl
              intro x hx
              rw [setWeight, prod_insert (hxU x hx)]
              rfl
            _ = _ := by rw [← sum_mul, ← sum_mul]; ring

theorem FiniteLaw.probability_disjointWitnesses_le
    {Ω I J : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw Ω) (selected : Ω → Finset I) (pi : I → ℝ≥0)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ A ⊆ selected omega) ≤ setWeight pi A)
    (alternatives : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint alternatives) :
    L.probability (fun omega ↦ ∀ j ∈ S, ∃ x ∈ alternatives j, x ∈ selected omega) ≤
      ∏ j ∈ S, ∑ x ∈ alternatives j, pi x := by
  simpa only [empty_subset, true_and, setWeight, prod_empty, one_mul] using
    L.probability_forced_disjointWitnesses_le selected pi hjoint alternatives S hpair ∅
      (fun _ _ ↦ disjoint_empty_left _)

theorem FiniteLaw.probability_image_subset_le_of_bounded_fibers
    {Ω I J : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw Ω) (selected : Ω → Finset I) (S : Finset I) (f : I → J)
    (sigma : ℝ≥0) (M : ℕ)
    (hselected : L.SupportedOn fun omega ↦ selected omega ⊆ S)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ A ⊆ selected omega) ≤ sigma ^ A.card)
    (hfibers : ∀ j, (S.filter (fun x ↦ f x = j)).card ≤ M) (Q : Finset J) :
    L.probability (fun omega ↦ Q ⊆ (selected omega).image f) ≤ ((M : ℝ≥0) * sigma) ^ Q.card := by
  let alternatives := fun j ↦ S.filter (fun x ↦ f x = j)
  have hpair : (Q : Set J).PairwiseDisjoint alternatives := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro x hxa hxb
    exact hab ((mem_filter.mp hxa).2.symm.trans (mem_filter.mp hxb).2)
  calc
    _ ≤ L.probability (fun omega ↦ ∀ j ∈ Q, ∃ x ∈ alternatives j, x ∈ selected omega) := by
      apply L.probability_mono_of_supported hselected
      intro omega hsub hQ j hj
      obtain ⟨x, hx, hfx⟩ := mem_image.mp (hQ hj)
      exact ⟨x, mem_filter.mpr ⟨hsub hx, hfx⟩, hx⟩
    _ ≤ ∏ j ∈ Q, ∑ _x ∈ alternatives j, sigma :=
      L.probability_disjointWitnesses_le selected (fun _ ↦ sigma)
        (fun A ↦ by simpa only [setWeight, prod_const] using hjoint A) alternatives Q hpair
    _ ≤ ∏ _j ∈ Q, (M : ℝ≥0) * sigma := by
      apply prod_le_prod'
      intro j _
      simp only [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfibers j) zero_le
    _ = _ := by rw [prod_const]

theorem FiniteLaw.probability_disjointWitnesses_le_uniform
    {Ω I J : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw Ω) (selected : Ω → Finset I) (sigma : ℝ≥0)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ A ⊆ selected omega) ≤ sigma ^ A.card)
    (alternatives : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint alternatives)
    (M : ℕ) (hM : ∀ j ∈ S, (alternatives j).card ≤ M) :
    L.probability (fun omega ↦ ∀ j ∈ S, ∃ x ∈ alternatives j, x ∈ selected omega) ≤
      ((M : ℝ≥0) * sigma) ^ S.card := by
  apply (L.probability_disjointWitnesses_le selected (fun _ ↦ sigma)
    (fun A ↦ by simpa only [setWeight, prod_const] using hjoint A) alternatives S hpair).trans
  rw [← prod_const]
  apply prod_le_prod'
  intro j hj
  simp only [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM j hj) zero_le

def activeWitnessIndices
    {I J : Type*} [DecidableEq I] [DecidableEq J] (alternatives : J → Finset I)
    (S : Finset J) (selected : Finset I) : Finset J :=
  S.filter fun j ↦ ∃ x ∈ alternatives j, x ∈ selected

theorem FiniteLaw.probability_activeWitnessIndices_card_ge_le
    {Ω I J : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw Ω) (selected : Ω → Finset I) (sigma : ℝ≥0)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ A ⊆ selected omega) ≤ sigma ^ A.card)
    (alternatives : J → Finset I) (S : Finset J)
    (hpair : (S : Set J).PairwiseDisjoint alternatives)
    (M : ℕ) (hM : ∀ j ∈ S, (alternatives j).card ≤ M)
    (s R : ℕ) (hR : 0 < R) (hs : 2*s ≤ R) :
    L.probability (fun omega ↦ R ≤ (activeWitnessIndices alternatives S (selected omega)).card) ≤
      (2 * (S.card : ℝ≥0) * M * sigma / R) ^ s := by
  let active := fun omega ↦ activeWitnessIndices alternatives S (selected omega)
  have hsub (omega : Ω) : active omega ⊆ S := filter_subset _ _
  have hactive : ∀ H ∈ S.powersetCard s,
      L.probability (fun omega ↦ H ⊆ active omega) ≤ ((M : ℝ≥0) * sigma) ^ s := by
    intro H hH
    have hm := mem_powersetCard.mp hH
    calc
      _ ≤ L.probability (fun omega ↦ ∀ j ∈ H, ∃ x ∈ alternatives j, x ∈ selected omega) := by
        apply L.probability_mono
        intro omega hA j hj
        exact (mem_filter.mp (hA hj)).2
      _ ≤ ((M : ℝ≥0) * sigma) ^ s := by
        simpa only [hm.2] using L.probability_disjointWitnesses_le_uniform selected sigma hjoint alternatives H
          (fun a ha b hb hab ↦ hpair (hm.1 ha) (hm.1 hb) hab) M (fun j hj ↦ hM j (hm.1 hj))
  have ht := L.probability_card_inter_ge_le_powerMoment active S s R (((M : ℝ≥0) * sigma) ^ s) hR hs hactive
  simp_rw [inter_eq_right.mpr (hsub _)] at ht
  convert ht using 1
  rw [← mul_pow]
  congr 1
  ring

end

end Erdos207
