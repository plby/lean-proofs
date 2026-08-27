/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointBlockUpperTail

/-! # Two-coordinate witnesses in disjoint blocks

A collision requires its own coordinate and one alternative coordinate.
The witness union bound retains both factors, unlike a raw reservoir-star
bound.  Only joint inclusion of coordinates is used.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def pairWitnesses
    {I J : Type*} [DecidableEq J]
    (key : J → I) (alternatives : J → Finset I)
    (S : Finset J) (omega : I → Bool) : Finset J :=
  S.filter fun j ↦ omega (key j) = true ∧
    ∃ x ∈ alternatives j, omega x = true

namespace FiniteLaw

theorem probability_forced_pairWitnesses_le
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (pi : I → ℝ≥0)
    (hjoint : ∀ A, L.probability (fun omega ↦ ∀ i ∈ A, omega i = true) ≤ setWeight pi A)
    (key : J → I) (alternatives : J → Finset I) (S : Finset J)
    (hkey : ∀ j ∈ S, key j ∉ alternatives j)
    (hpair : (S : Set J).PairwiseDisjoint (fun j ↦ insert (key j) (alternatives j)))
    (U : Finset I)
    (hU : ∀ j ∈ S, Disjoint U (insert (key j) (alternatives j))) :
    L.probability (fun omega ↦ (∀ i ∈ U, omega i = true) ∧
      ∀ j ∈ S, omega (key j) = true ∧ ∃ x ∈ alternatives j, omega x = true) ≤
      setWeight pi U * ∏ j ∈ S, pi (key j) * ∑ x ∈ alternatives j, pi x := by
  induction S using Finset.induction_on generalizing U with
  | empty => simpa using hjoint U
  | @insert j S hjS ih =>
      have hkeyS : ∀ k ∈ S, key k ∉ alternatives k :=
        fun k hk ↦ hkey k (mem_insert_of_mem hk)
      have hpairS : (S : Set J).PairwiseDisjoint
          (fun k ↦ insert (key k) (alternatives k)) := by
        intro a ha b hb hab
        exact hpair (mem_insert_of_mem ha) (mem_insert_of_mem hb) hab
      have hkeyU : key j ∉ U := by
        intro hjU
        exact disjoint_left.mp (hU j (mem_insert_self j S)) hjU (mem_insert_self _ _)
      have hxU (x : I) (hx : x ∈ alternatives j) : x ∉ U := by
        intro hxU
        exact disjoint_left.mp (hU j (mem_insert_self j S)) hxU (mem_insert_of_mem hx)
      have hxkey (x : I) (hx : x ∈ alternatives j) : x ≠ key j := by
        intro heq
        exact hkey j (mem_insert_self j S) (heq ▸ hx)
      have hnew (x : I) (hx : x ∈ alternatives j) :
          ∀ k ∈ S, Disjoint (insert x (insert (key j) U))
            (insert (key k) (alternatives k)) := by
        intro k hk
        have hjk : j ≠ k := fun heq ↦ hjS (heq ▸ hk)
        have hblocks := hpair (mem_insert_self j S) (mem_insert_of_mem hk) hjk
        apply disjoint_left.mpr
        intro i hi hik
        rcases mem_insert.mp hi with rfl | hi
        · exact disjoint_left.mp hblocks (mem_insert_of_mem hx) hik
        rcases mem_insert.mp hi with rfl | hi
        · exact disjoint_left.mp hblocks (mem_insert_self _ _) hik
        · exact disjoint_left.mp (hU k (mem_insert_of_mem hk)) hi hik
      calc
        _ ≤ L.probability (fun omega ↦ ∃ x ∈ alternatives j,
            (∀ i ∈ insert x (insert (key j) U), omega i = true) ∧
              ∀ k ∈ S, omega (key k) = true ∧ ∃ y ∈ alternatives k, omega y = true) := by
          apply L.probability_mono
          intro omega h
          obtain ⟨x, hx, hxt⟩ := (h.2 j (mem_insert_self j S)).2
          refine ⟨x, hx, ?_, fun k hk ↦ h.2 k (mem_insert_of_mem hk)⟩
          intro i hi
          rcases mem_insert.mp hi with rfl | hi
          · exact hxt
          rcases mem_insert.mp hi with rfl | hi
          · exact (h.2 j (mem_insert_self j S)).1
          · exact h.1 i hi
        _ ≤ ∑ x ∈ alternatives j, L.probability (fun omega ↦
            (∀ i ∈ insert x (insert (key j) U), omega i = true) ∧
              ∀ k ∈ S, omega (key k) = true ∧ ∃ y ∈ alternatives k, omega y = true) :=
          L.probability_exists_le _ _
        _ ≤ ∑ x ∈ alternatives j, setWeight pi (insert x (insert (key j) U)) *
            ∏ k ∈ S, pi (key k) * ∑ y ∈ alternatives k, pi y := by
          apply sum_le_sum
          intro x hx
          exact ih hkeyS hpairS _ (hnew x hx)
        _ = setWeight pi U * ∏ k ∈ insert j S,
            pi (key k) * ∑ y ∈ alternatives k, pi y := by
          rw [prod_insert hjS]
          have hweights (x : I) (hx : x ∈ alternatives j) :
              setWeight pi (insert x (insert (key j) U)) = pi x * (pi (key j) * setWeight pi U) := by
            unfold setWeight
            rw [prod_insert (by simpa only [mem_insert, not_or] using And.intro (hxkey x hx) (hxU x hx)),
              prod_insert hkeyU]
          calc
            _ = ∑ x ∈ alternatives j, (pi x * (pi (key j) * setWeight pi U)) *
                ∏ k ∈ S, pi (key k) * ∑ y ∈ alternatives k, pi y := by
              apply sum_congr rfl
              intro x hx
              rw [hweights x hx]
            _ = _ := by
              rw [← sum_mul, ← sum_mul]
              ring

theorem probability_pairWitnesses_subset_le
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (pi : I → ℝ≥0)
    (hjoint : ∀ A, L.probability (fun omega ↦ ∀ i ∈ A, omega i = true) ≤ setWeight pi A)
    (key : J → I) (alternatives : J → Finset I) (S H : Finset J) (hHS : H ⊆ S)
    (hkey : ∀ j ∈ S, key j ∉ alternatives j)
    (hpair : (S : Set J).PairwiseDisjoint (fun j ↦ insert (key j) (alternatives j))) :
    L.probability (fun omega ↦ H ⊆ pairWitnesses key alternatives S omega) ≤
      ∏ j ∈ H, pi (key j) * ∑ x ∈ alternatives j, pi x := by
  have h := L.probability_forced_pairWitnesses_le pi hjoint key alternatives H
    (fun j hj ↦ hkey j (hHS hj))
    (fun a ha b hb hab ↦ hpair (hHS ha) (hHS hb) hab) ∅ (fun _ _ ↦ disjoint_empty_left _)
  have hevent : (fun omega ↦ H ⊆ pairWitnesses key alternatives S omega) =
      (fun omega ↦ (∀ i ∈ (∅ : Finset I), omega i = true) ∧
        ∀ j ∈ H, omega (key j) = true ∧ ∃ x ∈ alternatives j, omega x = true) := by
    funext omega
    apply propext
    simp only [Finset.notMem_empty, false_implies, implies_true, true_and]
    constructor
    · intro h j hj
      exact (mem_filter.mp (h hj)).2
    · intro h j hj
      exact mem_filter.mpr ⟨hHS hj, h j hj⟩
  simpa only [hevent, setWeight, prod_empty, one_mul] using h

theorem probability_pairWitnesses_subset_le_uniform
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (sigma : ℝ≥0)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ ∀ i ∈ A, omega i = true) ≤ sigma ^ A.card)
    (key : J → I) (alternatives : J → Finset I) (S H : Finset J) (hHS : H ⊆ S)
    (hkey : ∀ j ∈ S, key j ∉ alternatives j)
    (hpair : (S : Set J).PairwiseDisjoint (fun j ↦ insert (key j) (alternatives j)))
    (M : ℕ) (hM : ∀ j ∈ S, (alternatives j).card ≤ M) :
    L.probability (fun omega ↦ H ⊆ pairWitnesses key alternatives S omega) ≤
      ((M : ℝ≥0) * sigma ^ 2) ^ H.card := by
  apply (L.probability_pairWitnesses_subset_le (fun _ ↦ sigma)
    (fun A ↦ by simpa [setWeight] using hjoint A) key alternatives S H hHS hkey hpair).trans
  rw [← prod_const]
  apply prod_le_prod'
  intro j hj
  simp only [sum_const, nsmul_eq_mul]
  calc
    sigma * ((alternatives j).card * sigma) ≤ sigma * ((M : ℝ≥0) * sigma) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hM j (hHS hj)) zero_le) zero_le
    _ = (M : ℝ≥0) * sigma ^ 2 := by ring

theorem probability_pairWitnesses_card_ge_le
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (sigma : ℝ≥0)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ ∀ i ∈ A, omega i = true) ≤ sigma ^ A.card)
    (key : J → I) (alternatives : J → Finset I) (S : Finset J)
    (hkey : ∀ j ∈ S, key j ∉ alternatives j)
    (hpair : (S : Set J).PairwiseDisjoint (fun j ↦ insert (key j) (alternatives j)))
    (M : ℕ) (hM : ∀ j ∈ S, (alternatives j).card ≤ M)
    (s R : ℕ) (hR : 0 < R) (hs : 2 * s ≤ R) :
    L.probability (fun omega ↦ R ≤ (pairWitnesses key alternatives S omega).card) ≤
      (2 * (S.card : ℝ≥0) * M * sigma ^ 2 / R) ^ s := by
  have ht := L.probability_card_inter_ge_le_powerMoment (pairWitnesses key alternatives S)
    S s R (((M : ℝ≥0) * sigma ^ 2) ^ s) hR hs (fun H hH ↦ by
      have hm := mem_powersetCard.mp hH
      simpa only [hm.2] using L.probability_pairWitnesses_subset_le_uniform sigma hjoint
        key alternatives S H hm.1 hkey hpair M hM)
  have hsub (omega : I → Bool) : pairWitnesses key alternatives S omega ⊆ S := filter_subset _ _
  simp_rw [inter_eq_right.mpr (hsub _)] at ht
  convert ht using 1
  rw [← mul_pow]
  congr 1
  ring

theorem probability_pairWitnesses_card_ge_le_dyadic
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw (I → Bool)) (sigma : ℝ≥0)
    (hjoint : ∀ A : Finset I, L.probability (fun omega ↦ ∀ i ∈ A, omega i = true) ≤ sigma ^ A.card)
    (key : J → I) (alternatives : J → Finset I) (S : Finset J)
    (hkey : ∀ j ∈ S, key j ∉ alternatives j)
    (hpair : (S : Set J).PairwiseDisjoint (fun j ↦ insert (key j) (alternatives j)))
    (M : ℕ) (hM : ∀ j ∈ S, (alternatives j).card ≤ M)
    (s R : ℕ) (hR : 0 < R) (hs : 2 * s ≤ R)
    (hmean : 4 * (S.card : ℝ≥0) * M * sigma ^ 2 ≤ R) :
    L.probability (fun omega ↦ R ≤ (pairWitnesses key alternatives S omega).card) ≤
      ((2 : ℝ≥0) ^ s)⁻¹ := by
  apply (L.probability_pairWitnesses_card_ge_le sigma hjoint key alternatives S hkey hpair M hM s R hR hs).trans
  have hRreal : (0 : ℝ≥0) < R := by exact_mod_cast hR
  have hbase : 2 * (S.card : ℝ≥0) * M * sigma ^ 2 / R ≤ (1 / 2 : ℝ≥0) := by
    apply (div_le_iff₀ hRreal).mpr
    calc
      _ = (4 * (S.card : ℝ≥0) * M * sigma ^ 2) / 2 := by ring
      _ ≤ (R : ℝ≥0) / 2 := div_le_div_of_nonneg_right hmean zero_le
      _ = _ := by ring
  simpa only [one_div, inv_pow] using pow_le_pow_left' hbase s

end FiniteLaw

end

end Erdos207
