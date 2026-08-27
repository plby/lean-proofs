/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveReferenceConcentration

/-! # One simultaneous reference-count event, allowing upper-only codegree tests -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def ReferenceCountGood (lower : Bool) (epsilon actual target : ℝ) : Prop :=
  (lower = true → (1-epsilon)*target ≤ actual) ∧ actual ≤ (1+epsilon)*target

theorem referenceCountGood_of_small_deviation
    (lower : Bool) (epsilon actual target mu : ℝ)
    (hmean : (lower = true → (1-epsilon/2)*target ≤ mu) ∧ mu ≤ (1+epsilon/2)*target)
    (hdeviation : |actual-mu| ≤ (epsilon/2)*target) :
    ReferenceCountGood lower epsilon actual target := by
  refine ⟨?_, real_sampled_reference_upper target mu actual epsilon hmean.2 hdeviation⟩
  intro hlower
  exact (real_sampled_reference_window target mu actual epsilon ⟨hmean.1 hlower, hmean.2⟩ hdeviation).1

theorem reserveEdgeLaw_probability_not_referenceCountGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (S : Finset (Sym2 V)) (hS : S ⊆ crossingEdges G U) (lower : Bool) (target epsilon : ℝ)
    (htarget : 0 ≤ target) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hmean : (lower = true → (1-epsilon/2)*target ≤ (r : ℝ)*S.card) ∧
      (r : ℝ)*S.card ≤ (1+epsilon/2)*target) :
    ((reserveEdgeLaw G U r hr).probability (fun bits ↦
      ¬ ReferenceCountGood lower epsilon ((S ∩ reserveEdges G U bits).card : ℝ) target) : ℝ) ≤
        2*Real.exp (-epsilon^2*target/32) := by
  have hmu : (r : ℝ)*S.card ≤ 2*target := hmean.2.trans (by
    apply mul_le_mul_of_nonneg_right _ htarget
    linarith only [hepsilon1])
  have hb := reserveEdgeLaw_probability_abs_inter_count_gt_reference G U r hr S hS target (epsilon/2)
    hmu (by positivity) (by linarith only [hepsilon1])
  have hmono : (reserveEdgeLaw G U r hr).probability (fun bits ↦
      ¬ ReferenceCountGood lower epsilon ((S ∩ reserveEdges G U bits).card : ℝ) target) ≤
      (reserveEdgeLaw G U r hr).probability (fun bits ↦ (epsilon/2)*target <
        |((S ∩ reserveEdges G U bits).card : ℝ)-(r : ℝ)*S.card|) := by
    apply FiniteLaw.probability_mono
    intro bits hbad
    by_contra hn
    exact hbad (referenceCountGood_of_small_deviation lower epsilon _ target _ hmean (le_of_not_gt hn))
  have hmonoR : ((reserveEdgeLaw G U r hr).probability (fun bits ↦
      ¬ ReferenceCountGood lower epsilon ((S ∩ reserveEdges G U bits).card : ℝ) target) : ℝ) ≤
      (reserveEdgeLaw G U r hr).probability (fun bits ↦ (epsilon/2)*target <
        |((S ∩ reserveEdges G U bits).card : ℝ)-(r : ℝ)*S.card|) := by exact_mod_cast hmono
  apply hmonoR.trans
  have hexp : -(epsilon/2)^2*target/8 = -epsilon^2*target/32 := by ring
  simpa only [hexp] using hb

theorem reserveEdgeLaw_probability_not_all_referenceCounts_le
    {J V : Type*} [Fintype J] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (S : J → Finset (Sym2 V)) (Relevant : J → Prop) (lower : J → Bool) (target : J → ℝ)
    (epsilon minimum : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hminimum : 0 ≤ minimum)
    (hS : ∀ j, Relevant j → S j ⊆ crossingEdges G U)
    (htarget : ∀ j, Relevant j → minimum ≤ target j)
    (hmean : ∀ j, Relevant j →
      (lower j = true → (1-epsilon/2)*target j ≤ (r : ℝ)*(S j).card) ∧
        (r : ℝ)*(S j).card ≤ (1+epsilon/2)*target j) :
    ((reserveEdgeLaw G U r hr).probability (fun bits ↦ ¬ ∀ j, Relevant j →
      ReferenceCountGood (lower j) epsilon ((S j ∩ reserveEdges G U bits).card : ℝ) (target j)) : ℝ) ≤
        2*Fintype.card J*Real.exp (-epsilon^2*minimum/32) := by
  let L := reserveEdgeLaw G U r hr
  let Bad := fun j : J ↦ fun bits ↦ Relevant j ∧
    ¬ ReferenceCountGood (lower j) epsilon ((S j ∩ reserveEdges G U bits).card : ℝ) (target j)
  have hpoint : ∀ j, (L.probability (Bad j) : ℝ) ≤ 2*Real.exp (-epsilon^2*minimum/32) := by
    intro j
    by_cases hj : Relevant j
    · have hb := reserveEdgeLaw_probability_not_referenceCountGood G U r hr (S j) (hS j hj) (lower j)
        (target j) epsilon (hminimum.trans (htarget j hj)) hepsilon hepsilon1 (hmean j hj)
      have heq : Bad j = (fun bits ↦ ¬ ReferenceCountGood (lower j) epsilon
          ((S j ∩ reserveEdges G U bits).card : ℝ) (target j)) := by
        funext bits
        simp only [Bad, hj, true_and]
      rw [heq]
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left (htarget j hj) (sq_nonneg epsilon)
      linarith only [hm]
    · have heq : Bad j = (fun _ ↦ False) := by funext bits; simp only [Bad, hj, false_and]
      rw [heq, L.probability_false]
      positivity
  have hcover : L.probability (fun bits ↦ ¬ ∀ j, Relevant j →
      ReferenceCountGood (lower j) epsilon ((S j ∩ reserveEdges G U bits).card : ℝ) (target j)) ≤
      ∑ j : J, L.probability (Bad j) := by
    apply le_trans _ (L.probability_exists_le (univ : Finset J) Bad)
    apply L.probability_mono
    intro bits hb
    simp only [not_forall] at hb
    obtain ⟨j, hj, hbad⟩ := hb
    exact ⟨j, mem_univ _, hj, hbad⟩
  have hcoverR : (L.probability (fun bits ↦ ¬ ∀ j, Relevant j →
      ReferenceCountGood (lower j) epsilon ((S j ∩ reserveEdges G U bits).card : ℝ) (target j)) : ℝ) ≤
      ∑ j : J, (L.probability (Bad j) : ℝ) := by exact_mod_cast hcover
  apply hcoverR.trans
  calc
    _ ≤ ∑ _j : J, 2*Real.exp (-epsilon^2*minimum/32) := sum_le_sum (fun j _ ↦ hpoint j)
    _ = _ := by simp; ring

end

end Erdos207
