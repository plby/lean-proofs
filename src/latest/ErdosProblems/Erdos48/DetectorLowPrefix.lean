/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.BadRootMass
import ErdosProblems.Erdos48.DetectorPropagation

/-!
# Removing the short initial segment of the zero detector

The hybrid large sieve needs a detector supported beyond a power of the
conductor-height parameter.  Binary shells and Chebyshev's elementary upper
bound show that the initial segment of the positive majorant is only a fixed
multiple of the corresponding power of its logarithmic length.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

open BoundedGaps.Maynard

private theorem sum_vonMangoldt_subset_Icc_le
    {s : Finset ℕ} {X : ℕ} (hs : s ⊆ Finset.Icc 0 X) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n) ≤
      (Real.log 4 + 4) * (X : ℝ) := by
  calc
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n) ≤
        ∑ n ∈ Finset.Icc 0 X, ArithmeticFunction.vonMangoldt n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
    _ = Chebyshev.psi (X : ℝ) := by
      rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    _ ≤ (Real.log 4 + 4) * (X : ℝ) :=
      Chebyshev.psi_le_const_mul_self (by positivity)

private theorem weightedMajorant_shell_le
    {eta : ℝ} (heta : 0 < eta) (k M a : ℕ)
    (ha : a ∈ Finset.Icc 1 M) :
    (∑ n ∈ badRootLogShell (Finset.Icc 2 (2 ^ M)) a,
        weightedVonMangoldtMajorant eta k n) ≤
      2 * (Real.log 4 + 4) *
        (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ k := by
  let G : ℝ := (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ k
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hpoint : ∀ n ∈ badRootLogShell (Finset.Icc 2 (2 ^ M)) a,
      weightedVonMangoldtMajorant eta k n ≤
        G * ((2 : ℝ) ^ a)⁻¹ * ArithmeticFunction.vonMangoldt n := by
    intro n hn
    have hnData := Finset.mem_filter.mp
      (show n ∈ (Finset.Icc 2 (2 ^ M)).filter
          (fun m ↦ Nat.log 2 m = a) by
        simpa only [badRootLogShell] using hn)
    have hnBounds := Finset.mem_Icc.mp hnData.1
    have haPow : 2 ^ a ≤ n := by
      rw [← hnData.2]
      exact Nat.pow_log_le_self 2 (by omega)
    have hnUpper : n < 2 ^ (a + 1) := by
      rw [← hnData.2]
      exact Nat.lt_pow_succ_log_self (by omega) n
    have haM : a ≤ M := (Finset.mem_Icc.mp ha).2
    have hnReal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlogNonneg : 0 ≤ Real.log n := Real.log_nonneg hnOne
    have hlogLe : Real.log n ≤ ((M + 1 : ℕ) : ℝ) * Real.log 2 := by
      calc
        Real.log n ≤ Real.log ((2 ^ (a + 1) : ℕ) : ℝ) := by
          apply Real.log_le_log hnReal
          exact_mod_cast hnUpper.le
        _ = ((a + 1 : ℕ) : ℝ) * Real.log 2 := by
          rw [show (((2 ^ (a + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (a + 1) by
            norm_cast, Real.log_pow]
        _ ≤ ((M + 1 : ℕ) : ℝ) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Nat.add_le_add_right haM 1
          · positivity
    have hlogPow : Real.log n ^ k ≤ G := by
      exact pow_le_pow_left₀ hlogNonneg hlogLe k
    have hrpow : (n : ℝ) ^ (-(1 + eta)) ≤ ((2 : ℝ) ^ a)⁻¹ := by
      calc
        (n : ℝ) ^ (-(1 + eta)) ≤ (n : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
        _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ (((2 ^ a : ℕ) : ℝ))⁻¹ := by
          exact inv_anti₀ (by positivity) (by exact_mod_cast haPow)
        _ = ((2 : ℝ) ^ a)⁻¹ := by norm_cast
    unfold weightedVonMangoldtMajorant
    have hLambda : 0 ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    calc
      Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + eta)) ≤
          G * ArithmeticFunction.vonMangoldt n * ((2 : ℝ) ^ a)⁻¹ := by
        gcongr
      _ = G * ((2 : ℝ) ^ a)⁻¹ *
          ArithmeticFunction.vonMangoldt n := by ring
  calc
    (∑ n ∈ badRootLogShell (Finset.Icc 2 (2 ^ M)) a,
        weightedVonMangoldtMajorant eta k n) ≤
        ∑ n ∈ badRootLogShell (Finset.Icc 2 (2 ^ M)) a,
          G * ((2 : ℝ) ^ a)⁻¹ *
            ArithmeticFunction.vonMangoldt n := by
      exact Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = G * ((2 : ℝ) ^ a)⁻¹ *
        (∑ n ∈ badRootLogShell (Finset.Icc 2 (2 ^ M)) a,
          ArithmeticFunction.vonMangoldt n) := by
      rw [Finset.mul_sum]
    _ ≤ G * ((2 : ℝ) ^ a)⁻¹ *
        ((Real.log 4 + 4) * ((2 ^ (a + 1) : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · apply sum_vonMangoldt_subset_Icc_le
        intro n hn
        have hnData := Finset.mem_filter.mp
          (show n ∈ (Finset.Icc 2 (2 ^ M)).filter
              (fun m ↦ Nat.log 2 m = a) by
            simpa only [badRootLogShell] using hn)
        have hnUpper : n < 2 ^ (a + 1) := by
          rw [← hnData.2]
          exact Nat.lt_pow_succ_log_self (by omega) n
        exact Finset.mem_Icc.mpr ⟨by omega, hnUpper.le⟩
      · positivity
    _ = 2 * (Real.log 4 + 4) * G := by
      rw [show ((2 ^ (a + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (a + 1) by norm_cast,
        pow_succ]
      field_simp
    _ = _ := rfl

/-- A binary-power prefix of the positive detector majorant has the expected
logarithmic order.  The deliberately coarse constant is uniform in `eta`.
-/
theorem sum_weightedVonMangoldtMajorant_Icc_two_pow_le
    (eta : ℝ) (heta : 0 < eta) (k M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 ^ M),
        weightedVonMangoldtMajorant eta k n) ≤
      2 * (Real.log 4 + 4) * (M : ℝ) *
        (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ k := by
  classical
  let E : Finset ℕ := Finset.Icc 2 (2 ^ M)
  have hE : ∀ n ∈ E, 2 ≤ n ∧ n ≤ 2 ^ M := by
    intro n hn
    exact Finset.mem_Icc.mp hn
  have hremoveOne :
      (∑ n ∈ Finset.Icc 1 (2 ^ M),
          weightedVonMangoldtMajorant eta k n) =
        ∑ n ∈ E, weightedVonMangoldtMajorant eta k n := by
    have hpow : 1 ≤ 2 ^ M := Nat.one_le_pow M 2 (by omega)
    rw [show Finset.Icc 1 (2 ^ M) = insert 1 E by
      ext n
      simp only [E, Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert]
    · simp [weightedVonMangoldtMajorant]
    · simp [E]
  rw [hremoveOne, ← biUnion_badRootLogShell hE,
    Finset.sum_biUnion (pairwiseDisjoint_badRootLogShell E (Nat.log 2 (2 ^ M))),
    Nat.log_pow (by omega : 1 < 2)]
  calc
    (∑ a ∈ Finset.Icc 1 M,
        ∑ n ∈ badRootLogShell E a,
          weightedVonMangoldtMajorant eta k n) ≤
        ∑ _a ∈ Finset.Icc 1 M,
          2 * (Real.log 4 + 4) *
            (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ k := by
      exact Finset.sum_le_sum fun a ha ↦
        weightedMajorant_shell_le heta k M a ha
    _ = ((Finset.Icc 1 M).card : ℝ) *
        (2 * (Real.log 4 + 4) *
          (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ k) := by simp
    _ ≤ (M : ℝ) *
        (2 * (Real.log 4 + 4) *
          (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ k) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show (Finset.Icc 1 M).card ≤ M by
          rw [Nat.card_Icc]
          omega)
      · positivity
    _ = _ := by ring

end

end Erdos48
