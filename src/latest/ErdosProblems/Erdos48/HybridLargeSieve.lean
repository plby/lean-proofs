/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.HybridHilbert
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.CharacterLargeSieve

/-!
# A block form of the hybrid character large sieve

The continuous Montgomery--Vaughan theorem controls the variation between
separated block frequencies.  The ordinary primitive-character large sieve
then controls the coefficient carried by each block.  This is the finite
Hilbert-space core of the hybrid large sieve; the remaining analytic step is
to decompose a Dirichlet polynomial into sufficiently short blocks.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

/-- Weighted Cauchy--Schwarz for the squared norm of a finite sum.  The
weights are kept explicit so that Taylor coefficients can be paired with
reciprocal factorials. -/
theorem norm_finset_sum_sq_le_sum_mul_sum_sq_div
    {κ : Type*} (S : Finset κ) (a : κ → ℝ)
    (ha : ∀ k ∈ S, 0 < a k) (z : κ → ℂ) :
    ‖∑ k ∈ S, z k‖ ^ 2 ≤
      (∑ k ∈ S, a k) * ∑ k ∈ S, ‖z k‖ ^ 2 / a k := by
  by_cases hSempty : S = ∅
  · simp [hSempty]
  have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
  have hsumPos : 0 < ∑ k ∈ S, a k := by
    exact Finset.sum_pos' (fun k hk ↦ (ha k hk).le)
      ⟨hS.choose, hS.choose_spec, ha hS.choose hS.choose_spec⟩
  have hnorm : ‖∑ k ∈ S, z k‖ ≤ ∑ k ∈ S, ‖z k‖ :=
    norm_sum_le S z
  have hsquare : ‖∑ k ∈ S, z k‖ ^ 2 ≤
      (∑ k ∈ S, ‖z k‖) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcauchy := Finset.sq_sum_div_le_sum_sq_div S
    (fun k ↦ ‖z k‖) ha
  rw [div_le_iff₀ hsumPos] at hcauchy
  exact hsquare.trans (by simpa [mul_comm] using hcauchy)

/-- The Taylor-polynomial block expansion used before passing to the full
hybrid Dirichlet polynomial. -/
noncomputable def blockTaylorPolynomial
    {ι : Type*} [Fintype ι]
    (R : ℕ) (x : ι → ℝ) (u : ℕ → ι → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range R,
    (Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ) *
      realFrequencyPolynomial x (u k) t

/-- Uniform weighted Cauchy bound for a finite Taylor block expansion. -/
theorem norm_blockTaylorPolynomial_sq_le
    {ι : Type*} [Fintype ι]
    (R : ℕ) (x : ι → ℝ) (u : ℕ → ι → ℂ) (t : ℝ) :
    ‖blockTaylorPolynomial R x u t‖ ^ 2 ≤
      (∑ k ∈ Finset.range R, ((k.factorial : ℝ))⁻¹) *
        ∑ k ∈ Finset.range R,
          ‖(Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ) *
              realFrequencyPolynomial x (u k) t‖ ^ 2 /
            ((k.factorial : ℝ))⁻¹ := by
  unfold blockTaylorPolynomial
  apply norm_finset_sum_sq_le_sum_mul_sum_sq_div
  intro k hk
  positivity

/-- A finite weighted family of real-frequency polynomials satisfies the
same Montgomery--Vaughan mean estimate. -/
theorem intervalIntegral_weighted_sum_realFrequencyPolynomial_norm_sq_le
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (x : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r s, r ≠ s → δ ≤ |x r - x s|)
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (u : κ → ι → ℂ) :
    (∫ t in (0 : ℝ)..T,
        ∑ k : κ, w k * ‖realFrequencyPolynomial x (u k) t‖ ^ 2) ≤
      (T + 2 * Real.pi * δ⁻¹) *
        ∑ k : κ, w k * ∑ r : ι, ‖u k r‖ ^ 2 := by
  classical
  rw [intervalIntegral.integral_finsetSum]
  · calc
      (∑ k : κ, ∫ t in (0 : ℝ)..T,
          w k * ‖realFrequencyPolynomial x (u k) t‖ ^ 2) =
          ∑ k : κ, w k *
            (∫ t in (0 : ℝ)..T,
              ‖realFrequencyPolynomial x (u k) t‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∑ k : κ, w k *
          ((T + 2 * Real.pi * δ⁻¹) *
            ∑ r : ι, ‖u k r‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral_realFrequencyPolynomial_norm_sq_le
            x hδ hT hsep (u k)) (hw k)
      _ = (T + 2 * Real.pi * δ⁻¹) *
          ∑ k : κ, w k * ∑ r : ι, ‖u k r‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  · intro k _
    exact ((continuous_const.mul
      ((continuous_realFrequencyPolynomial x (u k)).norm.pow 2))).intervalIntegrable 0 T

/-- Hybrid large-sieve estimate after a Dirichlet polynomial has been split
into blocks of a common additive length `N`.  The blocks need not be
disjoint; in applications they form a partition. -/
theorem intervalIntegral_weighted_primitive_blockPolynomial_le
    {ι : Type*} [Fintype ι]
    (Q N : ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + N))
    (c : ℕ → ℂ) (x : ι → ℝ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|) :
    (∫ v in (0 : ℝ)..T,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              ‖realFrequencyPolynomial x
                (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) ≤
      (T + 2 * Real.pi * δ⁻¹) *
        ((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ i : ι, ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  classical
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  let E : ℝ := ∑ i : ι, ∑ n ∈ s i, ‖c n‖ ^ 2
  have hweight (q : ℕ) : 0 ≤ (q : ℝ) / (q.totient : ℝ) := by positivity
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
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q,
                ‖realFrequencyPolynomial x
                  (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) =
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
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
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            (∫ v in (0 : ℝ)..T,
              ‖realFrequencyPolynomial x
                (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2)) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              (C * ∑ i : ι,
                ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (hweight q)
      exact Finset.sum_le_sum fun psi _ ↦ hmean q psi
    _ = C * ∑ i : ι,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2 := by
      let A : ℕ → ι → ℝ := fun q i ↦
        ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2
      have hpsi (q : ℕ) :
          (∑ psi : primitiveCharacters q,
              C * ∑ i : ι, ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2) =
            C * ∑ i : ι, A q i := by
        calc
          (∑ psi : primitiveCharacters q,
              C * ∑ i : ι, ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2) =
              ∑ psi : primitiveCharacters q, ∑ i : ι,
                C * ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro psi _
            rw [Finset.mul_sum]
          _ = ∑ i : ι, ∑ psi : primitiveCharacters q,
                C * ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2 :=
            Finset.sum_comm
          _ = C * ∑ i : ι, A q i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      simp_rw [hpsi]
      calc
        (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) * (C * ∑ i : ι, A q i)) =
            ∑ q ∈ Finset.Ioc 0 Q, ∑ i : ι,
              C * ((q : ℝ) / (q.totient : ℝ) * A q i) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [← mul_assoc, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = ∑ i : ι, ∑ q ∈ Finset.Ioc 0 Q,
              C * ((q : ℝ) / (q.totient : ℝ) * A q i) :=
          Finset.sum_comm
        _ = C * ∑ i : ι, ∑ q ∈ Finset.Ioc 0 Q,
              (q : ℝ) / (q.totient : ℝ) * A q i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ ≤ C * ∑ i : ι,
        (((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ s i, ‖c n‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun i _ ↦
          sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
            Q (m0 i) N (s i) (hs i) c
      · dsimp [C]
        positivity
    _ = (T + 2 * Real.pi * δ⁻¹) *
        ((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ i : ι, ∑ n ∈ s i, ‖c n‖ ^ 2 := by
      dsimp [C, E]
      rw [← Finset.mul_sum]
      ring

/-- Variable-length form of the block hybrid large sieve.  Keeping the
containing length inside the block sum is essential when the additive block
length is proportional to its location: after multiplication by the
vertical frequency factor, `H i + Q²` is then comparable to the integers in
the block, with no global dyadic-shell loss. -/
theorem intervalIntegral_weighted_primitive_blockPolynomial_variable_le
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (c : ℕ → ℂ) (x : ι → ℝ) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|) :
    (∫ v in (0 : ℝ)..T,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              ‖realFrequencyPolynomial x
                (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) ≤
      (T + 2 * Real.pi * δ⁻¹) *
        ∑ i : ι, (((H i : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  classical
  let C : ℝ := T + 2 * Real.pi * δ⁻¹
  have hweight (q : ℕ) : 0 ≤ (q : ℝ) / (q.totient : ℝ) := by
    positivity
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
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q,
                ‖realFrequencyPolynomial x
                  (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2) =
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
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
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            (∫ v in (0 : ℝ)..T,
              ‖realFrequencyPolynomial x
                (fun i ↦ ∑ n ∈ s i, c n * psi.1 n) v‖ ^ 2)) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              (C * ∑ i : ι,
                ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (hweight q)
      exact Finset.sum_le_sum fun psi _ ↦ hmean q psi
    _ = C * ∑ i : ι,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              ‖∑ n ∈ s i, c n * psi.1 n‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      ring
    _ ≤ C * ∑ i : ι,
        ((((H i : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ s i, ‖c n‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun i _ ↦
          sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
            Q (m0 i) (H i) (s i) (hs i) c
      · dsimp [C]
        positivity
    _ = _ := by rfl

end Erdos48
