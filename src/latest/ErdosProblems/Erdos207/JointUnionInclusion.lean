/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteJointBind
import ErdosProblems.Erdos207.BatchKernelJointInclusion

/-! # Union inclusion under conditional sampling, with the prior additive error retained -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem joint_union_inclusion_with_error
    {D S I : Type*} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S] [DecidableEq I]
    (P : FiniteLaw D) (K : D → FiniteLaw S) (old : D → Finset I) (new : D → S → Finset I)
    (w v : I → ℝ≥0) (A b : ℝ≥0) (U : Finset I)
    (hold : ∀ Q ⊆ U, P.probability (fun d ↦ Q ⊆ old d) ≤ A * setWeight w Q + b)
    (hnew : ∀ d Q, (K d).probability (fun s ↦ Q ⊆ new d s) ≤ setWeight v Q) :
    (P.jointBind K).probability (fun z ↦ U ⊆ old z.1 ∪ new z.1 z.2) ≤
      A * setWeight (fun i ↦ w i + v i) U + b * setWeight (fun i ↦ 1 + v i) U := by
  classical
  have hcover : (P.jointBind K).probability (fun z ↦ U ⊆ old z.1 ∪ new z.1 z.2) ≤
      (P.jointBind K).probability (fun z ↦ ∃ Q ∈ U.powerset, Q ⊆ old z.1 ∧ U \ Q ⊆ new z.1 z.2) := by
    apply FiniteLaw.probability_mono
    intro z hz
    refine ⟨U ∩ old z.1, mem_powerset.mpr inter_subset_left, inter_subset_right, ?_⟩
    intro i hi
    have hm := mem_sdiff.mp hi
    rcases mem_union.mp (hz hm.1) with ho | hn
    · exact (hm.2 (mem_inter.mpr ⟨hm.1, ho⟩)).elim
    · exact hn
  have hterm (Q : Finset I) (hQ : Q ∈ U.powerset) :
      (P.jointBind K).probability (fun z ↦ Q ⊆ old z.1 ∧ U \ Q ⊆ new z.1 z.2) ≤
        setWeight v (U \ Q) * (A * setWeight w Q + b) := by
    exact (P.jointBind_probability_and_le K (fun d ↦ Q ⊆ old d)
      (fun d s ↦ U \ Q ⊆ new d s) (setWeight v (U \ Q))
      (fun d _ ↦ hnew d (U \ Q))).trans
      (mul_le_mul_of_nonneg_left (hold Q (mem_powerset.mp hQ)) zero_le)
  apply hcover.trans
  apply ((P.jointBind K).probability_exists_le U.powerset _).trans
  apply (sum_le_sum hterm).trans_eq
  have hproduct : ∑ Q ∈ U.powerset, setWeight w Q * setWeight v (U \ Q) =
      setWeight (fun i ↦ w i + v i) U := by
    exact (prod_add w v U).symm
  have herror : ∑ Q ∈ U.powerset, setWeight v (U \ Q) =
      setWeight (fun i ↦ 1 + v i) U := by
    simpa only [setWeight, prod_const_one, one_mul] using (prod_add (fun _ ↦ (1 : ℝ≥0)) v U).symm
  calc
    _ = A * (∑ Q ∈ U.powerset, setWeight w Q * setWeight v (U \ Q)) +
        b * (∑ Q ∈ U.powerset, setWeight v (U \ Q)) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro Q _
      ring
    _ = _ := by rw [hproduct, herror]

theorem joint_union_inclusion_with_uniform_error
    {D S I : Type*} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S] [DecidableEq I]
    (P : FiniteLaw D) (K : D → FiniteLaw S) (old : D → Finset I) (new : D → S → Finset I)
    (w v : I → ℝ≥0) (A b : ℝ≥0) (U : Finset I)
    (hold : ∀ Q ⊆ U, P.probability (fun d ↦ Q ⊆ old d) ≤ A * setWeight w Q + b)
    (hnew : ∀ d Q, (K d).probability (fun s ↦ Q ⊆ new d s) ≤ setWeight v Q)
    (hv : ∀ i ∈ U, v i ≤ 1) :
    (P.jointBind K).probability (fun z ↦ U ⊆ old z.1 ∪ new z.1 z.2) ≤
      A * setWeight (fun i ↦ w i + v i) U + b * 2 ^ U.card := by
  apply (joint_union_inclusion_with_error P K old new w v A b U hold hnew).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  change (∏ i ∈ U, (1 + v i)) ≤ 2 ^ U.card
  rw [← prod_const]
  exact prod_le_prod' (fun i hi ↦ by
    calc
      1 + v i ≤ 1 + 1 := add_le_add le_rfl (hv i hi)
      _ = 2 := by norm_num)

end

end Erdos207
