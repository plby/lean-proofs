/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InhomogeneousWeightedJointInclusion

/-! # Factorial-free joint inclusion for adaptive batch-insertion kernels -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem batch_kernel_probability_subset_le
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (delta : W → ℝ≥0)
    (hnew : ∀ s U, Disjoint U (R s) →
      (K s).probability (fun s' ↦ U ⊆ R s') ≤ setWeight delta U)
    (s : Ω) (U : Finset W) :
    (K s).probability (fun s' ↦ U ⊆ R s') ≤
      ∑ Q ∈ U.powerset, if Q ⊆ R s then setWeight delta (U \ Q) else 0 := by
  classical
  have hdis : Disjoint (U \ (U ∩ R s)) (R s) := by
    apply disjoint_left.mpr
    intro e he hR
    have hm := mem_sdiff.mp he
    exact hm.2 (mem_inter.mpr ⟨hm.1, hR⟩)
  calc
    _ ≤ (K s).probability (fun s' ↦ U \ (U ∩ R s) ⊆ R s') :=
      (K s).probability_mono (fun s' h ↦ sdiff_subset.trans h)
    _ ≤ setWeight delta (U \ (U ∩ R s)) := hnew s _ hdis
    _ = (if U ∩ R s ⊆ R s then setWeight delta (U \ (U ∩ R s)) else 0) := by
      rw [if_pos inter_subset_right]
    _ ≤ _ := Finset.single_le_sum (s := U.powerset)
      (f := fun Q : Finset W ↦ if Q ⊆ R s then setWeight delta (U \ Q) else 0)
      (a := U ∩ R s) (fun _ _ ↦ zero_le) (mem_powerset.mpr inter_subset_left)

theorem bind_batch_joint_inclusion
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (pi delta : W → ℝ≥0)
    (hnew : ∀ s U, Disjoint U (R s) →
      (K s).probability (fun s' ↦ U ⊆ R s') ≤ setWeight delta U)
    (hold : ∀ U, L.probability (fun s ↦ U ⊆ R s) ≤ setWeight pi U) (U : Finset W) :
    (FiniteLaw.bind L K).probability (fun s ↦ U ⊆ R s) ≤
      setWeight (fun e ↦ pi e + delta e) U := by
  classical
  rw [FiniteLaw.probability_bind]
  calc
    _ ≤ ∑ s, L.mass s *
        ∑ Q ∈ U.powerset, if Q ⊆ R s then setWeight delta (U \ Q) else 0 := by
      apply sum_le_sum
      intro s _hs
      exact mul_le_mul_of_nonneg_left (batch_kernel_probability_subset_le K R delta hnew s U) zero_le
    _ = ∑ Q ∈ U.powerset, setWeight delta (U \ Q) * L.probability (fun s ↦ Q ⊆ R s) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro Q _hQ
      unfold FiniteLaw.probability
      rw [mul_sum]
      apply sum_congr rfl
      intro s _hs
      by_cases hQ : Q ⊆ R s <;> simp [hQ, mul_comm]
    _ ≤ ∑ Q ∈ U.powerset, setWeight delta (U \ Q) * setWeight pi Q :=
      sum_le_sum (fun Q _hQ ↦ mul_le_mul_of_nonneg_left (hold Q) zero_le)
    _ = _ := by
      unfold setWeight
      rw [prod_add]
      apply sum_congr rfl
      intro Q _hQ
      ring

theorem evolveKernels_batch_joint_inclusion
    {Ω W : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq W]
    (K : ℕ → Ω → FiniteLaw Ω) (R : Ω → Finset W) (delta : ℕ → W → ℝ≥0)
    (hnew : ∀ t s U, Disjoint U (R s) →
      (K t s).probability (fun s' ↦ U ⊆ R s') ≤ setWeight (delta t) U)
    (s0 : Ω) (hempty : R s0 = ∅) (t : ℕ) (U : Finset W) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure s0)).probability (fun s ↦ U ⊆ R s) ≤
      setWeight (cumulativePointHazard delta t) U := by
  classical
  induction t generalizing U with
  | zero =>
      by_cases hU : U = ∅
      · subst U
        simp [setWeight]
      · have hcard : U.card ≠ 0 := card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hU)
        simp [FiniteLaw.evolveKernels_zero, FiniteLaw.probability_pure, hempty,
          cumulativePointHazard, setWeight, hU, hcard]
  | succ t ih =>
      rw [FiniteLaw.evolveKernels_succ]
      have h := bind_batch_joint_inclusion (FiniteLaw.evolveKernels K t (FiniteLaw.pure s0))
        (K t) R (cumulativePointHazard delta t) (delta t) (hnew t) ih U
      have hfun : cumulativePointHazard delta (t + 1) =
          fun e ↦ cumulativePointHazard delta t e + delta t e := by
        funext e
        simp only [cumulativePointHazard, sum_range_succ]
      rw [hfun]
      exact h

end

end Erdos207
