/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedIntersectionTail

/-! # Configuration moments with an explicit additive joint-inclusion error -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem expectation_selectedCount_pow_additive_le
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (pi : W → ℝ≥0) (C epsilon : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d)
    (hjoint : ∀ A : Finset W, A.card ≤ s * d →
      L.probability (fun ω ↦ A ⊆ R ω) ≤ C * setWeight pi A + epsilon) :
    L.expectation (fun ω ↦ selectedCount F (R ω) ^ s) ≤
      C * (∑ f : Fin s → I, setWeight pi (tupleUnion F f)) + epsilon * (Fintype.card I : ℝ≥0) ^ s := by
  rw [expectation_selectedCount_pow]
  calc
    _ ≤ ∑ f : Fin s → I, (C * setWeight pi (tupleUnion F f) + epsilon) := by
      apply sum_le_sum
      intro f _hf
      have hevent : (fun ω ↦ ∀ t, F (f t) ⊆ R ω) = (fun ω ↦ tupleUnion F f ⊆ R ω) := by
        funext ω
        exact propext (tuple_joint_iff_union_subset F f (R ω))
      rw [hevent]
      exact hjoint (tupleUnion F f) (card_tupleUnion_le F hcard f)
    _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp [mul_comm]

theorem configurationMomentBound_additive
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (pi : W → ℝ≥0) (C epsilon kappa : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hkappa : HasExtensionBound F pi kappa)
    (hjoint : ∀ A : Finset W, A.card ≤ s * d →
      L.probability (fun ω ↦ A ⊆ R ω) ≤ C * setWeight pi A + epsilon) :
    L.expectation (fun ω ↦ selectedCount F (R ω) ^ s) ≤
      C * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * kappa) ^ s +
        epsilon * (Fintype.card I : ℝ≥0) ^ s := by
  apply (expectation_selectedCount_pow_additive_le L F R pi C epsilon hcard hjoint).trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    (sum_tupleWeight_le_bounded_intersections F pi hcard hkappa s le_rfl) zero_le) le_rfl

theorem configurationTailBound_additive
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (pi : W → ℝ≥0) (C epsilon kappa K : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hkappa : HasExtensionBound F pi kappa) (hK : 0 < K)
    (hjoint : ∀ A : Finset W, A.card ≤ s * d →
      L.probability (fun ω ↦ A ⊆ R ω) ≤ C * setWeight pi A + epsilon) :
    L.probability (fun ω ↦ K ≤ selectedCount F (R ω)) ≤
      C * (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * kappa) / K) ^ s +
        epsilon * ((Fintype.card I : ℝ≥0) / K) ^ s := by
  have hmono := L.probability_mono (fun ω (hω : K ≤ selectedCount F (R ω)) ↦ pow_le_pow_left' hω s)
  apply hmono.trans
  apply (L.probability_le_expectation_div (fun ω ↦ selectedCount F (R ω) ^ s) (pow_pos hK s)).trans
  apply (div_le_div_of_nonneg_right (configurationMomentBound_additive L F R pi C epsilon kappa hcard hkappa hjoint) zero_le).trans_eq
  rw [add_div, mul_div_assoc, mul_div_assoc, ← div_pow, ← div_pow]

theorem dominatedConfigurationTailBound_additive
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W) (X : Ω → ℝ≥0)
    (pi : W → ℝ≥0) (C epsilon kappa K : ℝ≥0) {d s : ℕ}
    (hdom : L.SupportedOn (fun ω ↦ X ω ≤ selectedCount F (R ω)))
    (hcard : ∀ i, (F i).card ≤ d) (hkappa : HasExtensionBound F pi kappa) (hK : 0 < K)
    (hjoint : ∀ A : Finset W, A.card ≤ s * d →
      L.probability (fun ω ↦ A ⊆ R ω) ≤ C * setWeight pi A + epsilon) :
    L.probability (fun ω ↦ K ≤ X ω) ≤
      C * (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * kappa) / K) ^ s +
        epsilon * ((Fintype.card I : ℝ≥0) / K) ^ s := by
  apply (L.probability_mono_of_supported hdom (fun ω hω hX ↦ hX.trans hω)).trans
  exact configurationTailBound_additive L F R pi C epsilon kappa K hcard hkappa hK hjoint

end

end Erdos207
