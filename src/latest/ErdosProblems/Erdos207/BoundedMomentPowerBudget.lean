/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedIntersectionTail

/-! # Explicit power-scale cutoffs for growing configuration moments -/

namespace Erdos207

open scoped NNReal

theorem boundedMoment_power_cutoff
    (d s a b : ℕ) (t w κ A Z : ℝ≥0) (hs : 1 ≤ s) (hst : (s : ℝ≥0) ≤ t)
    (hw : w ≤ t ^ b) (hκ : κ ≤ A * Z * t ^ a)
    (hconst : 2 * (((d + 1) ^ (d + 1) : ℕ) : ℝ≥0) * A ≤ t) :
    2 * (w ^ d * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ)) ≤
      Z * t ^ (a + d * (b + 1) + 1) := by
  let D : ℝ≥0 := ((d + 1) ^ (d + 1) : ℕ)
  have hM : (boundedIntersectionMomentCoefficient d s : ℝ≥0) ≤ D * t ^ d := by
    have hM' : (boundedIntersectionMomentCoefficient d s : ℝ≥0) ≤ D * (s : ℝ≥0) ^ d := by
      dsimp only [D]
      exact_mod_cast boundedIntersectionMomentCoefficient_le d s hs
    exact hM'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left' hst d) zero_le)
  have hwd : w ^ d ≤ t ^ (b * d) := (pow_le_pow_left' hw d).trans_eq (pow_mul t b d).symm
  have he : a + d * (b + 1) = b * d + d + a := by ring
  calc
    _ ≤ 2 * (t ^ (b * d) * ((D * t ^ d) * (A * Z * t ^ a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hwd (mul_le_mul hM hκ zero_le zero_le) zero_le zero_le) zero_le
    _ = (2 * D * A) * Z * t ^ (a + d * (b + 1)) := by rw [he, pow_add, pow_add]; ring
    _ ≤ t * Z * t ^ (a + d * (b + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst zero_le) zero_le
    _ = _ := by rw [pow_succ]; ring

theorem dominatedConfigurationTailBound_powerThreshold
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W) (X : Ω → ℝ≥0)
    (π : W → ℝ≥0) (t w κ A Z : ℝ≥0) (d s a b : ℕ)
    (hdom : L.SupportedOn (fun ω ↦ X ω ≤ selectedCount F (R ω)))
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ)
    (hjoint : ∀ T : Finset W, T.card ≤ s * d →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ w ^ (s * d) * setWeight π T)
    (hs : 1 ≤ s) (hst : (s : ℝ≥0) ≤ t) (hw : w ≤ t ^ b)
    (hκscale : κ ≤ A * Z * t ^ a) (hZ : 0 < Z)
    (hconst : 2 * (((d + 1) ^ (d + 1) : ℕ) : ℝ≥0) * A ≤ t) :
    L.probability (fun ω ↦ Z * t ^ (a + d * (b + 1) + 1) ≤ X ω) ≤ (1 / 2 : ℝ≥0) ^ s := by
  have ht : 0 < t := lt_of_lt_of_le (by exact_mod_cast (show 0 < s by omega)) hst
  exact dominatedConfigurationTailBound_bounded_intersections L F R X π w κ _ hdom hcard hκ
    (mul_pos hZ (pow_pos ht _)) hjoint
    (boundedMoment_power_cutoff d s a b t w κ A Z hs hst hw hκscale hconst)

end Erdos207
