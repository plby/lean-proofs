/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherHybrid
import ErdosProblems.Erdos48.AdaptiveHybridTaylor

/-!
# Taylor reconstruction for the amplified Gallagher hybrid sieve

This file develops the unweighted primitive-character hybrid masses needed
after the rough-support amplifier has supplied its logarithmic coefficient.
The finite Taylor estimate preserves that coefficient on the left, and
uniform Taylor convergence then yields the exact hybrid Dirichlet-polynomial
bound.
-/

open scoped BigOperators Topology Interval
open Filter Set

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

noncomputable def unweightedPrimitiveHybridTaylorMass
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    ∑ psi : primitiveCharacters q,
      ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2

noncomputable def unweightedPrimitiveHybridMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    ∑ psi : primitiveCharacters q,
      ‖primitiveHybridPolynomial x s c d q psi t‖ ^ 2

noncomputable def unweightedPrimitiveBlockFrequencyMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    ∑ psi : primitiveCharacters q,
      ‖realFrequencyPolynomial x
        (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) t‖ ^ 2

theorem continuous_unweightedPrimitiveHybridTaylorMass
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) :
    Continuous (unweightedPrimitiveHybridTaylorMass R Q x s c d) := by
  unfold unweightedPrimitiveHybridTaylorMass
  fun_prop

theorem continuous_unweightedPrimitiveHybridMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) :
    Continuous (unweightedPrimitiveHybridMass Q x s c d) := by
  unfold unweightedPrimitiveHybridMass
  fun_prop

theorem continuous_unweightedPrimitiveBlockFrequencyMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) :
    Continuous (unweightedPrimitiveBlockFrequencyMass Q x s c) := by
  classical
  unfold unweightedPrimitiveBlockFrequencyMass
  apply continuous_finsetSum (Finset.Ioc 0 Q)
  intro q hq
  apply continuous_finsetSum Finset.univ
  intro psi hpsi
  exact (continuous_realFrequencyPolynomial x
    (fun i ↦ ∑ n ∈ s i, c n * psi.1 n)).norm.pow 2

theorem intervalIntegral_unweightedPrimitiveHybridTaylorMass_eq
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridTaylorMass R Q x s c d t) =
      ∑ q ∈ Finset.Ioc 0 Q,
        ∑ psi : primitiveCharacters q,
          (∫ t in (0 : ℝ)..T,
            ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2) := by
  classical
  unfold unweightedPrimitiveHybridTaylorMass
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum]
    intro psi hpsi
    exact ((continuous_primitiveHybridTaylorPolynomial
      R x s c d q psi).norm.pow 2).intervalIntegrable 0 T
  · intro q hq
    exact (continuous_finsetSum Finset.univ fun psi _hpsi ↦
      (continuous_primitiveHybridTaylorPolynomial
        R x s c d q psi).norm.pow 2).intervalIntegrable 0 T

theorem intervalIntegral_unweightedPrimitiveHybridMass_eq
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridMass Q x s c d t) =
      ∑ q ∈ Finset.Ioc 0 Q,
        ∑ psi : primitiveCharacters q,
          (∫ t in (0 : ℝ)..T,
            ‖primitiveHybridPolynomial x s c d q psi t‖ ^ 2) := by
  classical
  unfold unweightedPrimitiveHybridMass
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum]
    intro psi hpsi
    exact ((continuous_primitiveHybridPolynomial
      x s c d q psi).norm.pow 2).intervalIntegrable 0 T
  · intro q hq
    exact (continuous_finsetSum Finset.univ fun psi _hpsi ↦
      (continuous_primitiveHybridPolynomial
        x s c d q psi).norm.pow 2).intervalIntegrable 0 T

theorem tendsto_intervalIntegral_unweightedPrimitiveHybridTaylorMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B) :
    Tendsto (fun R ↦ ∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridTaylorMass R Q x s c d t) atTop
      (𝓝 (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridMass Q x s c d t)) := by
  classical
  simp_rw [intervalIntegral_unweightedPrimitiveHybridTaylorMass_eq,
    intervalIntegral_unweightedPrimitiveHybridMass_eq]
  apply tendsto_finset_sum
  intro q hq
  apply tendsto_finsetSum
  intro psi hpsi
  exact tendsto_intervalIntegral_primitiveHybridTaylorPolynomial_norm_sq
    x s c d q psi hT hB hd

theorem unweightedPrimitiveHybridTaylorMass_le_blockFrequencyMass
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    unweightedPrimitiveHybridTaylorMass R Q x s c d t ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        ∑ k ∈ Finset.range R,
          t ^ (2 * k) / (k.factorial : ℝ) *
            unweightedPrimitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
  classical
  let A : ℝ := ∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹
  let G : ℕ → (q : ℕ) → primitiveCharacters q → ℝ := fun k q psi ↦
    ‖realFrequencyPolynomial x
      (fun i ↦ ∑ n ∈ s i,
        (c n * (d n : ℂ) ^ k) * psi.1 n) t‖ ^ 2
  let wk : ℕ → ℝ := fun k ↦ t ^ (2 * k) / (k.factorial : ℝ)
  have hpoint (q : ℕ) (psi : primitiveCharacters q) :
      ‖primitiveHybridTaylorPolynomial R x s c d q psi t‖ ^ 2 ≤
        A * ∑ k ∈ Finset.range R, wk k * G k q psi := by
    simpa only [A, wk, G, mul_assoc] using
      norm_primitiveHybridTaylorPolynomial_sq_le
        R x s c d q psi t ht
  calc
    unweightedPrimitiveHybridTaylorMass R Q x s c d t ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q,
            (A * ∑ k ∈ Finset.range R, wk k * G k q psi) := by
      unfold unweightedPrimitiveHybridTaylorMass
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum fun psi hpsi ↦ hpoint q psi
    _ = A * ∑ k ∈ Finset.range R, wk k *
          unweightedPrimitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k) t := by
      let H : (q : ℕ) → primitiveCharacters q → ℕ → ℝ :=
        fun q psi k ↦ wk k * G k q psi
      have hswap :
          (∑ q ∈ Finset.Ioc 0 Q,
              ∑ psi : primitiveCharacters q,
                ∑ k ∈ Finset.range R, H q psi k) =
            ∑ k ∈ Finset.range R,
              ∑ q ∈ Finset.Ioc 0 Q,
                ∑ psi : primitiveCharacters q, H q psi k := by
        calc
          _ = ∑ q ∈ Finset.Ioc 0 Q,
                ∑ k ∈ Finset.range R,
                  ∑ psi : primitiveCharacters q, H q psi k := by
            apply Finset.sum_congr rfl
            intro q hq
            exact Finset.sum_comm
          _ = _ := Finset.sum_comm
      calc
        (∑ q ∈ Finset.Ioc 0 Q,
            ∑ psi : primitiveCharacters q,
              (A * ∑ k ∈ Finset.range R, wk k * G k q psi)) =
            A * ∑ q ∈ Finset.Ioc 0 Q,
              ∑ psi : primitiveCharacters q,
                ∑ k ∈ Finset.range R, H q psi k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
        _ = A * ∑ k ∈ Finset.range R,
              ∑ q ∈ Finset.Ioc 0 Q,
                ∑ psi : primitiveCharacters q, H q psi k := by rw [hswap]
        _ = A * ∑ k ∈ Finset.range R, wk k *
            unweightedPrimitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          unfold unweightedPrimitiveBlockFrequencyMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]

theorem unweightedPrimitiveHybridTaylorMass_le_blockFrequencyMass_endpoint
    {ι : Type*} [Fintype ι]
    (R Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ) (d : ℕ → ℝ) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    unweightedPrimitiveHybridTaylorMass R Q x s c d t ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        ∑ k ∈ Finset.range R,
          T ^ (2 * k) / (k.factorial : ℝ) *
            unweightedPrimitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
  refine (unweightedPrimitiveHybridTaylorMass_le_blockFrequencyMass
    R Q x s c d t ht).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_right
    · apply div_le_div_of_nonneg_right
      · exact pow_le_pow_left₀ ht htT (2 * k)
      · positivity
    · unfold unweightedPrimitiveBlockFrequencyMass
      positivity
  · positivity

/-- Finite Taylor estimate with the logarithmic amplifier retained as a
factor on the left. -/
theorem mul_intervalIntegral_unweightedPrimitiveHybridTaylorMass_variable_le
    {ι : Type*} [Fintype ι]
    (R Q A : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B)
    (hprime : ∀ i n, n ∈ s i → n.Prime)
    (hrough : ∀ i n, n ∈ s i → Q * A < n) :
    L * (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridTaylorMass R Q x s c d t) ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        (T + 2 * Real.pi * δ⁻¹) *
          (∑ i, (((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
            ∑ n ∈ s i, ‖c n‖ ^ 2) *
              ∑ k ∈ Finset.range R,
                (T * B) ^ (2 * k) / (k.factorial : ℝ) := by
  classical
  let F : ℝ := ∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  let D : ι → ℝ := fun i ↦ ((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2
  let E : ℝ := ∑ i, D i * ∑ n ∈ s i, ‖c n‖ ^ 2
  let wk : ℕ → ℝ := fun k ↦ T ^ (2 * k) / (k.factorial : ℝ)
  let bk : ℕ → ℝ := fun k ↦ (T * B) ^ (2 * k) / (k.factorial : ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD (i : ι) : 0 ≤ D i := by dsimp [D]; positivity
  have hwk (k : ℕ) : 0 ≤ wk k := by dsimp [wk]; positivity
  have hblock (k : ℕ) :
      L * (∫ t in (0 : ℝ)..T,
          unweightedPrimitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k) t) ≤
        C * ∑ i, D i * ∑ n ∈ s i,
          ‖c n * (d n : ℂ) ^ k‖ ^ 2 := by
    simpa only [unweightedPrimitiveBlockFrequencyMass, C, D] using
      mul_intervalIntegral_primitive_blockPolynomial_variable_le_of_amplifier
        Q A L hL hcoeff H s m0 hs
          (fun n ↦ c n * (d n : ℂ) ^ k) x hδ hT hsep hprime hrough
  have hmono0 :
      (∫ t in (0 : ℝ)..T,
          unweightedPrimitiveHybridTaylorMass R Q x s c d t) ≤
        ∫ t in (0 : ℝ)..T,
          F * ∑ k ∈ Finset.range R, wk k *
            unweightedPrimitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t := by
    apply intervalIntegral.integral_mono_on hT
    · exact (continuous_unweightedPrimitiveHybridTaylorMass
        R Q x s c d).intervalIntegrable 0 T
    · apply Continuous.intervalIntegrable
      apply continuous_const.mul
      apply continuous_finsetSum (Finset.range R)
      intro k hk
      exact continuous_const.mul
        (continuous_unweightedPrimitiveBlockFrequencyMass Q x s
          (fun n ↦ c n * (d n : ℂ) ^ k))
    · intro t ht
      exact unweightedPrimitiveHybridTaylorMass_le_blockFrequencyMass_endpoint
        R Q x s c d ht.1 ht.2
  have hmono := mul_le_mul_of_nonneg_left hmono0 hL
  calc
    L * (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridTaylorMass R Q x s c d t) ≤
        L * (∫ t in (0 : ℝ)..T,
          F * ∑ k ∈ Finset.range R, wk k *
            unweightedPrimitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t) := hmono
    _ = F * ∑ k ∈ Finset.range R, wk k *
          (L * (∫ t in (0 : ℝ)..T,
            unweightedPrimitiveBlockFrequencyMass Q x s
              (fun n ↦ c n * (d n : ℂ) ^ k) t)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      · intro k hk
        exact (continuous_const.mul
          (continuous_unweightedPrimitiveBlockFrequencyMass Q x s
            (fun n ↦ c n * (d n : ℂ) ^ k))).intervalIntegrable 0 T
    _ ≤ F * ∑ k ∈ Finset.range R, wk k *
          (C * ∑ i, D i * ∑ n ∈ s i,
            ‖c n * (d n : ℂ) ^ k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hF
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hblock k) (hwk k)
    _ ≤ F * ∑ k ∈ Finset.range R, wk k *
          (C * (B ^ (2 * k) * E)) := by
      apply mul_le_mul_of_nonneg_left _ hF
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (hwk k)
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [E] using
        sum_weight_mul_norm_offset_pow_sq_le D hD s c d hB hd k
    _ = F * C * E * ∑ k ∈ Finset.range R, bk k := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [wk, bk]
      rw [mul_pow]
      ring
    _ = _ := by rfl

/-- Exact hybrid estimate obtained by letting the Taylor order tend to
infinity while retaining the amplifier gain. -/
theorem mul_intervalIntegral_unweightedPrimitiveHybridMass_variable_le
    {ι : Type*} [Fintype ι]
    (Q A : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ) (d : ℕ → ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B)
    (hprime : ∀ i n, n ∈ s i → n.Prime)
    (hrough : ∀ i n, n ∈ s i → Q * A < n) :
    L * (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridMass Q x s c d t) ≤
      Real.exp 1 * Real.exp ((T * B) ^ 2) *
        (T + 2 * Real.pi * δ⁻¹) *
          ∑ i, (((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
            ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  let E : ℝ := ∑ i, (((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
    ∑ n ∈ s i, ‖c n‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlim := tendsto_intervalIntegral_unweightedPrimitiveHybridTaylorMass
    Q x s c d hT hB hd
  have hlimL :
      Tendsto (fun R ↦ L * (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveHybridTaylorMass R Q x s c d t)) atTop
        (𝓝 (L * (∫ t in (0 : ℝ)..T,
          unweightedPrimitiveHybridMass Q x s c d t))) :=
    tendsto_const_nhds.mul hlim
  apply le_of_tendsto' hlimL
  intro R
  refine (mul_intervalIntegral_unweightedPrimitiveHybridTaylorMass_variable_le
    R Q A L hL hcoeff H s m0 hs x hδ hT hsep c d hB hd
      hprime hrough).trans ?_
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
