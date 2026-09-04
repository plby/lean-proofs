/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherAmplifier
import ErdosProblems.Erdos48.HybridLargeSieve

/-!
# Hybrid Gallagher large sieve for rough prime support

The finite squarefree-multiplier amplifier is combined with the existing
Montgomery--Vaughan block estimate.  This gives a variable-block hybrid
large sieve with the amplified arithmetic weight and the natural
`H i + (Q*A)^2` energy coefficient.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

/-- Variable-block hybrid large sieve with Gallagher's squarefree-multiplier
amplifier. -/
theorem intervalIntegral_roughAmplified_primitive_blockPolynomial_variable_le
    {ι : Type*} [Fintype ι]
    (Q A : ℕ) (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (c : ℕ → ℂ) (x : ι → ℝ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (hprime : ∀ i n, n ∈ s i → n.Prime)
    (hrough : ∀ i n, n ∈ s i → Q * A < n) :
    (∫ v in (0 : ℝ)..T,
        ∑ q ∈ Finset.Ioc 0 Q,
          roughAmplifierCoefficient q A *
            ∑ psi : primitiveCharacters q,
              ‖realFrequencyPolynomial x
                (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) ≤
      (T + 2 * Real.pi * δ⁻¹) *
        ∑ i : ι, (((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
          ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  classical
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  have hweight (q : ℕ) : 0 ≤ roughAmplifierCoefficient q A :=
    roughAmplifierCoefficient_nonneg q A
  have hmean (q : ℕ) (psi : primitiveCharacters q) :
      (∫ v in (0 : ℝ)..T,
          ‖realFrequencyPolynomial x
            (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) ≤
        C * ∑ i : ι, ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2 := by
    simpa only [C] using
      intervalIntegral_realFrequencyPolynomial_norm_sq_le
        x hδ hT hsep (fun i ↦ ∑ n ∈ s i, c n * psi.1 n)
  have hinterchange :
      (∫ v in (0 : ℝ)..T,
          ∑ q ∈ Finset.Ioc 0 Q,
            roughAmplifierCoefficient q A *
              ∑ psi : primitiveCharacters q,
                ‖realFrequencyPolynomial x
                  (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) =
        ∑ q ∈ Finset.Ioc 0 Q,
          roughAmplifierCoefficient q A *
            ∑ psi : primitiveCharacters q,
              (∫ v in (0 : ℝ)..T,
                ‖realFrequencyPolynomial x
                  (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum]
      intro psi _
      exact ((continuous_realFrequencyPolynomial x
        (fun i ↦ ∑ n ∈ s i, c n * psi.1 n)).norm.pow 2).intervalIntegrable 0 T
    · intro q hq
      apply Continuous.intervalIntegrable
      apply continuous_const.mul
      apply continuous_finsetSum Finset.univ
      intro psi _
      exact (continuous_realFrequencyPolynomial x
        (fun i ↦ ∑ n ∈ s i, c n * psi.1 n)).norm.pow 2
  rw [hinterchange]
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        roughAmplifierCoefficient q A *
          ∑ psi : primitiveCharacters q,
            (∫ v in (0 : ℝ)..T,
              ‖realFrequencyPolynomial x
                (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2)) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          roughAmplifierCoefficient q A *
            ∑ psi : primitiveCharacters q,
              (C * ∑ i : ι,
                ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (hweight q)
      exact Finset.sum_le_sum fun psi _ ↦ hmean q psi
    _ = C * ∑ i : ι,
        ∑ q ∈ Finset.Ioc 0 Q,
          roughAmplifierCoefficient q A *
            ∑ psi : primitiveCharacters q,
              ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      ring_nf
    _ ≤ C * ∑ i : ι,
        ((((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
          ∑ n ∈ s i, ‖c n‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i _hi
        simpa [primitiveTwistSquareMass] using
          sum_roughAmplifier_primitiveMass_primeSupport_le
            Q A (m0 i) (H i) (s i) (hs i) c
              (hprime i) (hrough i)
      · dsimp [C]
        positivity
    _ = _ := by rfl

/-- Removing the amplifier weight after a uniform lower bound for its
coefficient.  This is the form in which the logarithmic gain is fed into the
Taylor-block argument. -/
theorem mul_intervalIntegral_primitive_blockPolynomial_variable_le_of_amplifier
    {ι : Type*} [Fintype ι]
    (Q A : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (c : ℕ → ℂ) (x : ι → ℝ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (hprime : ∀ i n, n ∈ s i → n.Prime)
    (hrough : ∀ i n, n ∈ s i → Q * A < n) :
    L * (∫ v in (0 : ℝ)..T,
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q,
            ‖realFrequencyPolynomial x
              (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) ≤
      (T + 2 * Real.pi * δ⁻¹) *
        ∑ i : ι, (((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
          ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  classical
  let U : ℝ → ℝ := fun v ↦
    ∑ q ∈ Finset.Ioc 0 Q,
      ∑ psi : primitiveCharacters q,
        ‖realFrequencyPolynomial x
          (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2
  let W : ℝ → ℝ := fun v ↦
    ∑ q ∈ Finset.Ioc 0 Q,
      roughAmplifierCoefficient q A *
        ∑ psi : primitiveCharacters q,
          ‖realFrequencyPolynomial x
            (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2
  have hcontinuousU : Continuous U := by
    dsimp [U]
    apply continuous_finsetSum (Finset.Ioc 0 Q)
    intro q _hq
    apply continuous_finsetSum Finset.univ
    intro psi _hpsi
    exact (continuous_realFrequencyPolynomial x
      (fun i ↦ ∑ n ∈ s i, c n * psi.1 n)).norm.pow 2
  have hcontinuousW : Continuous W := by
    dsimp [W]
    apply continuous_finsetSum (Finset.Ioc 0 Q)
    intro q _hq
    apply continuous_const.mul
    apply continuous_finsetSum Finset.univ
    intro psi _hpsi
    exact (continuous_realFrequencyPolynomial x
      (fun i ↦ ∑ n ∈ s i, c n * psi.1 n)).norm.pow 2
  have hpoint (v : ℝ) : L * U v ≤ W v := by
    dsimp [U, W]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    apply mul_le_mul_of_nonneg_right (hcoeff q hq)
    exact Finset.sum_nonneg fun psi _hpsi ↦ sq_nonneg _
  have hmono :
      (∫ v in (0 : ℝ)..T, L * U v) ≤
        ∫ v in (0 : ℝ)..T, W v := by
    apply intervalIntegral.integral_mono_on hT
    · exact (continuous_const.mul hcontinuousU).intervalIntegrable 0 T
    · exact hcontinuousW.intervalIntegrable 0 T
    · intro v _hv
      exact hpoint v
  rw [intervalIntegral.integral_const_mul] at hmono
  calc
    L * (∫ v in (0 : ℝ)..T, U v) ≤
        ∫ v in (0 : ℝ)..T, W v := hmono
    _ ≤ (T + 2 * Real.pi * δ⁻¹) *
        ∑ i : ι, (((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
          ∑ n ∈ s i, ‖c n‖ ^ 2 := by
      simpa only [W] using
        intervalIntegral_roughAmplified_primitive_blockPolynomial_variable_le
          Q A H s m0 hs c x hδ hT hsep hprime hrough

end Erdos48
