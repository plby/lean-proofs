/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.HybridTaylor

/-!
# Variable-length hybrid Taylor estimate

This is the adaptive counterpart of the final theorem in `HybridTaylor`.
The length of each additive block remains inside its own energy term.  That
minor-looking refinement is what permits one simultaneous multiplicative
block decomposition of a long Dirichlet polynomial.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

theorem sum_weight_mul_norm_offset_pow_sq_le
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s : ι → Finset ℕ) (c : ℕ → ℂ) (d : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) (k : ℕ) :
    (∑ i, w i * ∑ n ∈ s i,
        ‖c n * (d n : ℂ) ^ k‖ ^ 2) ≤
      B ^ (2 * k) * ∑ i, w i * ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  calc
    (∑ i, w i * ∑ n ∈ s i,
        ‖c n * (d n : ℂ) ^ k‖ ^ 2) ≤
        ∑ i, w i * ∑ n ∈ s i,
          B ^ (2 * k) * ‖c n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have hpow : |d n| ^ (2 * k) ≤ B ^ (2 * k) :=
        pow_le_pow_left₀ (abs_nonneg _) (hd i n hn) (2 * k)
      calc
        (‖c n‖ * |d n| ^ k) ^ 2 =
            ‖c n‖ ^ 2 * |d n| ^ (2 * k) := by
          rw [mul_pow, ← pow_mul]
          congr 2
          omega
        _ ≤ ‖c n‖ ^ 2 * B ^ (2 * k) :=
          mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
        _ = B ^ (2 * k) * ‖c n‖ ^ 2 := by ring
    _ = B ^ (2 * k) * ∑ i, w i * ∑ n ∈ s i, ‖c n‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- Finite Taylor estimate with a separate character-sieve length on every
block. -/
theorem intervalIntegral_primitiveHybridTaylorMass_variable_le
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    (∫ t in (0 : ℝ)..T,
        primitiveHybridTaylorMass R Q x s c d t) ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        (T + 2 * Real.pi * δ⁻¹) *
          (∑ i, (((H i : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
            ∑ n ∈ s i, ‖c n‖ ^ 2) *
              ∑ k ∈ Finset.range R,
                (T * B) ^ (2 * k) / (k.factorial : ℝ) := by
  classical
  let A : ℝ := ∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  let D : ι → ℝ := fun i ↦ ((H i : ℕ) : ℝ) + (Q : ℝ) ^ 2
  let E : ℝ := ∑ i, D i * ∑ n ∈ s i, ‖c n‖ ^ 2
  let wk : ℕ → ℝ := fun k ↦ T ^ (2 * k) / (k.factorial : ℝ)
  let bk : ℕ → ℝ := fun k ↦ (T * B) ^ (2 * k) / (k.factorial : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD (i : ι) : 0 ≤ D i := by dsimp [D]; positivity
  have hwk (k : ℕ) : 0 ≤ wk k := by dsimp [wk]; positivity
  have hblock (k : ℕ) :
      (∫ t in (0 : ℝ)..T,
          primitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k) t) ≤
        C * ∑ i, D i * ∑ n ∈ s i,
          ‖c n * (d n : ℂ) ^ k‖ ^ 2 := by
    simpa only [primitiveBlockFrequencyMass, C, D] using
      intervalIntegral_weighted_primitive_blockPolynomial_variable_le
        Q H s m0 hs (fun n ↦ c n * (d n : ℂ) ^ k)
          x hδ hT hsep
  have hmono :
      (∫ t in (0 : ℝ)..T,
          primitiveHybridTaylorMass R Q x s c d t) ≤
        ∫ t in (0 : ℝ)..T,
          A * ∑ k ∈ Finset.range R, wk k *
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
    apply intervalIntegral.integral_mono_on hT
    · exact (continuous_primitiveHybridTaylorMass
        R Q x s c d).intervalIntegrable 0 T
    · apply Continuous.intervalIntegrable
      apply continuous_const.mul
      apply continuous_finsetSum (Finset.range R)
      intro k hk
      exact continuous_const.mul
        (continuous_primitiveBlockFrequencyMass Q x s
          (fun n ↦ c n * (d n : ℂ) ^ k))
    · intro t ht
      exact primitiveHybridTaylorMass_le_blockFrequencyMass_endpoint
        R Q x s c d ht.1 ht.2
  calc
    (∫ t in (0 : ℝ)..T,
        primitiveHybridTaylorMass R Q x s c d t) ≤
        ∫ t in (0 : ℝ)..T,
          A * ∑ k ∈ Finset.range R, wk k *
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := hmono
    _ = A * ∑ k ∈ Finset.range R, wk k *
          (∫ t in (0 : ℝ)..T,
            primitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum]
      · apply congrArg (fun z : ℝ ↦ A * z)
        apply Finset.sum_congr rfl
        intro k hk
        rw [intervalIntegral.integral_const_mul]
      · intro k hk
        exact (continuous_const.mul
          (continuous_primitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k))).intervalIntegrable 0 T
    _ ≤ A * ∑ k ∈ Finset.range R, wk k *
          (C * ∑ i, D i * ∑ n ∈ s i,
            ‖c n * (d n : ℂ) ^ k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hblock k) (hwk k)
    _ ≤ A * ∑ k ∈ Finset.range R, wk k *
          (C * (B ^ (2 * k) * E)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (hwk k)
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [E] using
        sum_weight_mul_norm_offset_pow_sq_le D hD s c d hB hd k
    _ = A * C * E * ∑ k ∈ Finset.range R, bk k := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [wk, bk]
      rw [mul_pow]
      ring
    _ = _ := by rfl

/-- Exact hybrid estimate for an ordinary block polynomial with adaptive
block lengths. -/
theorem intervalIntegral_primitiveHybridMass_variable_le
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    (∫ t in (0 : ℝ)..T,
        primitiveHybridMass Q x s c d t) ≤
      Real.exp 1 * Real.exp ((T * B) ^ 2) *
        (T + 2 * Real.pi * δ⁻¹) *
          ∑ i, (((H i : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
            ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  let E : ℝ := ∑ i, (((H i : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
    ∑ n ∈ s i, ‖c n‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlim := tendsto_intervalIntegral_primitiveHybridTaylorMass
    Q x s c d hT hB hd
  apply le_of_tendsto' hlim
  intro R
  refine (intervalIntegral_primitiveHybridTaylorMass_variable_le
    R Q H s m0 hs x hδ hT hsep c d hB hd).trans ?_
  calc
    (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
          C * E *
            ∑ k ∈ Finset.range R,
              (T * B) ^ (2 * k) / (k.factorial : ℝ) ≤
        Real.exp 1 * C * E *
          ∑ k ∈ Finset.range R,
            (T * B) ^ (2 * k) / (k.factorial : ℝ) := by
      gcongr
      exact sum_range_inv_factorial_le_exp_one R
    _ ≤ Real.exp 1 * C * E * Real.exp ((T * B) ^ 2) := by
      gcongr
      exact sum_range_mul_pow_two_mul_div_factorial_le_exp R hT hB
    _ = Real.exp 1 * Real.exp ((T * B) ^ 2) * C * E := by ring
    _ = _ := rfl

end Erdos48
