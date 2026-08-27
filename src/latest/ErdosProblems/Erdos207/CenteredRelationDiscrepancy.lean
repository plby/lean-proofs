/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BipartiteCodegreeMoment
import Mathlib.Data.Real.Basic

/-! # Centered rectangle discrepancy from actual degree and codegree bounds -/

namespace Erdos207

open Finset

theorem sum_centered_sq_eq
    {B : Type*} (U : Finset B) (f : B → ℝ) (mu : ℝ) :
    ∑ b ∈ U, (f b-mu)^2 = ∑ b ∈ U, f b^2 - 2*mu*(∑ b ∈ U, f b) + U.card*mu^2 := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul]
  rw [← sum_mul, ← mul_sum]
  ring

theorem sum_sq_relationPreneighbors_le_real
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (D C : ℝ) (hC : 0 ≤ C)
    (hdegree : ∀ a, ((relationNeighborsIn r univ a).card : ℝ) ≤ D)
    (hcodegree : ∀ a a', a ≠ a' → ((relationCommonNeighbors r a a').card : ℝ) ≤ C)
    (S : Finset A) :
    (∑ b : B, ((relationPreneighborsIn r S b).card : ℝ)^2) ≤ D*S.card+C*(S.card : ℝ)^2 := by
  have heq : (∑ b : B, ((relationPreneighborsIn r S b).card : ℝ)^2) =
      ∑ a ∈ S, ∑ a' ∈ S, ((relationCommonNeighbors r a a').card : ℝ) := by
    exact_mod_cast sum_sq_relationPreneighbors_eq_sum_commonNeighbors r S
  rw [heq]
  calc
    _ ≤ ∑ _a ∈ S, (D+C*S.card) := by
      apply sum_le_sum
      intro a ha
      rw [← add_sum_erase S (fun a' ↦ ((relationCommonNeighbors r a a').card : ℝ)) ha]
      apply add_le_add
      · rw [relationCommonNeighbors_self]
        exact hdegree a
      · calc
          _ ≤ ∑ _a' ∈ S.erase a, C := sum_le_sum (fun a' ha' ↦ hcodegree a a' (ne_of_mem_erase ha').symm)
          _ = (S.erase a).card*C := by simp
          _ ≤ (S.card : ℝ)*C := by
            apply mul_le_mul_of_nonneg_right _ hC
            exact_mod_cast card_le_card (erase_subset a S)
          _ = _ := mul_comm _ _
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

theorem sum_relationPreneighbors_ge_real
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (d : ℝ)
    (hdegree : ∀ a, d ≤ ((relationNeighborsIn r univ a).card : ℝ)) (S : Finset A) :
    d*S.card ≤ ∑ b : B, ((relationPreneighborsIn r S b).card : ℝ) := by
  have heq : (∑ b : B, ((relationPreneighborsIn r S b).card : ℝ)) =
      ∑ a ∈ S, ((relationNeighborsIn r univ a).card : ℝ) := by
    exact_mod_cast (card_relationPairsBetween_eq_sum_right r S univ).symm.trans
      (card_relationPairsBetween_eq_sum_left r S univ)
  rw [heq]
  calc
    _ = ∑ _a ∈ S, d := by simp [mul_comm]
    _ ≤ _ := sum_le_sum (fun a _ ↦ hdegree a)

theorem centered_relation_secondMoment_le
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (d D C rho : ℝ) (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hdegree : ∀ a, d ≤ ((relationNeighborsIn r univ a).card : ℝ) ∧
      ((relationNeighborsIn r univ a).card : ℝ) ≤ D)
    (hcodegree : ∀ a a', a ≠ a' → ((relationCommonNeighbors r a a').card : ℝ) ≤ C)
    (S : Finset A) :
    (∑ b : B, (((relationPreneighborsIn r S b).card : ℝ)-rho*S.card)^2) ≤
      D*S.card+(C-2*rho*d+rho^2*Fintype.card B)*(S.card : ℝ)^2 := by
  rw [sum_centered_sq_eq]
  have hsecond := sum_sq_relationPreneighbors_le_real r D C hC (fun a ↦ (hdegree a).2) hcodegree S
  have hfirst := sum_relationPreneighbors_ge_real r d (fun a ↦ (hdegree a).1) S
  have hlinear := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 2*(rho*S.card))
  simp only [card_univ]
  nlinarith only [hsecond, hlinear]

theorem centered_relation_rectangle_sq_le
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (rho bound : ℝ) (S : Finset A) (U : Finset B)
    (hsecond : (∑ b : B, (((relationPreneighborsIn r S b).card : ℝ)-rho*S.card)^2) ≤ bound) :
    (((relationPairsBetween r S U).card : ℝ)-rho*S.card*U.card)^2 ≤ U.card*bound := by
  have heq : ((relationPairsBetween r S U).card : ℝ)-rho*S.card*U.card =
      ∑ b ∈ U, (((relationPreneighborsIn r S b).card : ℝ)-rho*S.card) := by
    rw [card_relationPairsBetween_eq_sum_right]
    simp only [Nat.cast_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ (U.card : ℝ)*∑ b ∈ U, (((relationPreneighborsIn r S b).card : ℝ)-rho*S.card)^2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (U.card : ℝ)*∑ b : B, (((relationPreneighborsIn r S b).card : ℝ)-rho*S.card)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg (subset_univ U) (fun _ _ _ ↦ sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsecond (by positivity)

theorem typical_relation_rectangle_sq_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (r : V → V → Prop) [DecidableRel r] (rho xi : ℝ) (hrho : 0 ≤ rho) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hdegree : ∀ v, (1-xi)*rho*Fintype.card V ≤ ((relationNeighborsIn r univ v).card : ℝ) ∧
      ((relationNeighborsIn r univ v).card : ℝ) ≤ (1+xi)*rho*Fintype.card V)
    (hcodegree : ∀ v w, v ≠ w → ((relationCommonNeighbors r v w).card : ℝ) ≤ (1+xi)*rho^2*Fintype.card V)
    (S U : Finset V) :
    (((relationPairsBetween r S U).card : ℝ)-rho*S.card*U.card)^2 ≤
      (2*rho*Fintype.card V+3*xi*rho^2*(Fintype.card V : ℝ)^2)*S.card*U.card := by
  have hsecond := centered_relation_secondMoment_le r ((1-xi)*rho*Fintype.card V)
    ((1+xi)*rho*Fintype.card V) ((1+xi)*rho^2*Fintype.card V) rho (by positivity) hrho hdegree hcodegree S
  have hb := centered_relation_rectangle_sq_le r rho _ S U hsecond
  apply hb.trans
  have hS : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ S
  have hcoef : (1+xi)*rho*Fintype.card V ≤ 2*rho*Fintype.card V := by
    gcongr
    linarith only [hxi1]
  calc
    _ = (U.card : ℝ)*((1+xi)*rho*Fintype.card V*S.card+
        3*xi*rho^2*Fintype.card V*(S.card : ℝ)^2) := by ring
    _ ≤ (U.card : ℝ)*(2*rho*Fintype.card V*S.card+
        3*xi*rho^2*Fintype.card V*((S.card : ℝ)*Fintype.card V)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add (mul_le_mul_of_nonneg_right hcoef (by positivity))
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ (S.card : ℝ))
    _ = _ := by ring

theorem typical_relation_rectangle_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    (r : V → V → Prop) [DecidableRel r] (rho xi error : ℝ)
    (hrho : 0 ≤ rho) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (herror : 0 ≤ error)
    (hdegree : ∀ v, (1-xi)*rho*Fintype.card V ≤ ((relationNeighborsIn r univ v).card : ℝ) ∧
      ((relationNeighborsIn r univ v).card : ℝ) ≤ (1+xi)*rho*Fintype.card V)
    (hcodegree : ∀ v w, v ≠ w → ((relationCommonNeighbors r v w).card : ℝ) ≤ (1+xi)*rho^2*Fintype.card V)
    (hbudget : 2*rho*Fintype.card V+3*xi*rho^2*(Fintype.card V : ℝ)^2 ≤ error^2)
    (S U : Finset V) (hUS : U.card ≤ S.card) :
    ((relationPairsBetween r S U).card : ℝ) ≤ (rho*U.card+error)*S.card := by
  have hb := typical_relation_rectangle_sq_le r rho xi hrho hxi hxi1 hdegree hcodegree S U
  have hsq : (((relationPairsBetween r S U).card : ℝ)-rho*S.card*U.card)^2 ≤
      (error*S.card)^2 := by
    apply hb.trans
    calc
      _ ≤ error^2*S.card*U.card := by gcongr
      _ ≤ error^2*S.card*S.card := by gcongr
      _ = _ := by ring
  have hupper := le_of_sq_le_sq hsq (by positivity : 0 ≤ error*S.card)
  nlinarith only [hupper]

end Erdos207
