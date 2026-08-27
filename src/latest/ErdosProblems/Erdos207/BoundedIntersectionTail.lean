/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedIntersectionMoment

/-! # Growing-moment geometric tails from bounded intersections -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem boundedIntersectionMomentCoefficient_le
    (d s : ℕ) (hs : 1 ≤ s) :
    boundedIntersectionMomentCoefficient d s ≤ (d + 1) ^ (d + 1) * s ^ d := by
  unfold boundedIntersectionMomentCoefficient
  calc
    _ ≤ (d + 1) * (s * (d + 1)) ^ d :=
      Nat.mul_le_mul_left (d + 1) (pow_le_pow_left₀ zero_le (by nlinarith) d)
    _ = _ := by rw [mul_pow, pow_succ]; ring

theorem configurationMomentBound_bounded_intersections_scaled
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (π : W → ℝ≥0) (w κ : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ)
    (hjoint : ∀ T : Finset W, T.card ≤ s * d →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ w ^ (s * d) * setWeight π T) :
    L.expectation (fun ω ↦ (selectedCount F (R ω)) ^ s) ≤
      (w ^ d * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ)) ^ s := by
  refine (configurationMomentBound_bounded_intersections L F R π (w ^ (s * d)) κ hcard hκ hjoint).trans_eq ?_
  rw [mul_pow (w ^ d) ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) s,
    ← pow_mul w d s, Nat.mul_comm d s]

theorem probability_ge_le_geometric_of_moment
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ≥0)
    (s : ℕ) (A K : ℝ≥0) (hK : 0 < K)
    (hmoment : L.expectation (fun ω ↦ X ω ^ s) ≤ A ^ s) (hcut : 2 * A ≤ K) :
    L.probability (fun ω ↦ K ≤ X ω) ≤ (1 / 2 : ℝ≥0) ^ s := by
  have hpos : 0 < K ^ s := pow_pos hK s
  have hmono : L.probability (fun ω ↦ K ≤ X ω) ≤ L.probability (fun ω ↦ K ^ s ≤ X ω ^ s) :=
    L.probability_mono (fun _ h ↦ pow_le_pow_left' h s)
  refine hmono.trans ((L.probability_le_expectation_div (fun ω ↦ X ω ^ s) hpos).trans ?_)
  calc
    _ ≤ A ^ s / K ^ s := (div_le_div_iff_of_pos_right hpos).mpr hmoment
    _ = (A / K) ^ s := (div_pow A K s).symm
    _ ≤ _ := by
      apply pow_le_pow_left'
      apply (div_le_iff₀ hK).mpr
      have hhalf : A ≤ K / 2 := (le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).mpr
        (by simpa only [mul_comm] using hcut)
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hhalf

theorem configurationTailBound_bounded_intersections
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (π : W → ℝ≥0) (w κ K : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ) (hK : 0 < K)
    (hjoint : ∀ T : Finset W, T.card ≤ s * d →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ w ^ (s * d) * setWeight π T)
    (hcut : 2 * (w ^ d * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ)) ≤ K) :
    L.probability (fun ω ↦ K ≤ selectedCount F (R ω)) ≤ (1 / 2 : ℝ≥0) ^ s :=
  probability_ge_le_geometric_of_moment L (fun ω ↦ selectedCount F (R ω)) s _ K hK
    (configurationMomentBound_bounded_intersections_scaled L F R π w κ hcard hκ hjoint) hcut

theorem dominatedConfigurationTailBound_bounded_intersections
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W) (X : Ω → ℝ≥0)
    (π : W → ℝ≥0) (w κ K : ℝ≥0) {d s : ℕ}
    (hdom : L.SupportedOn (fun ω ↦ X ω ≤ selectedCount F (R ω)))
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ) (hK : 0 < K)
    (hjoint : ∀ T : Finset W, T.card ≤ s * d →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ w ^ (s * d) * setWeight π T)
    (hcut : 2 * (w ^ d * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ)) ≤ K) :
    L.probability (fun ω ↦ K ≤ X ω) ≤ (1 / 2 : ℝ≥0) ^ s := by
  refine (L.probability_mono_of_supported hdom (fun ω hω hX ↦ hX.trans hω)).trans ?_
  exact configurationTailBound_bounded_intersections L F R π w κ K hcard hκ hK hjoint hcut

end

end Erdos207
