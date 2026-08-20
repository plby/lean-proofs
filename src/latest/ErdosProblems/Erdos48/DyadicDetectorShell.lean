/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AdditiveBlockPartition
import ErdosProblems.Erdos48.BandLimitedDetector

/-!
# Hybrid mean bound on one dyadic detector shell

This file specializes the negative-phase hybrid large sieve to the quotient
blocks of one binary shell.  The result retains the freely chosen additive
block length, so the subsequent optimization can choose it from the height.
-/

namespace Erdos48

open Complex
open scoped BigOperators

noncomputable section

open BoundedGaps.Maynard

/-- The `a`-th binary shell of the band `(Y,N]`. -/
noncomputable def detectorDyadicShell (Y N a : ℕ) : Finset ℕ :=
  (Finset.Ioc Y N).filter fun n ↦ Nat.log 2 (n - 1) = a

/-- Primitive-character mean square of a negative-phase polynomial on one
finite support. -/
noncomputable def primitiveNegativeDirichletMass
    (Q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        ‖∑ n ∈ s, c n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2

theorem detectorDyadicShell_subset (Y N a : ℕ) (hY : 1 ≤ Y) :
    detectorDyadicShell Y N a ⊆ Finset.Ioc (2 ^ a) (2 * 2 ^ a) := by
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hnPos : 0 < n - 1 := by
    have := (Finset.mem_Ioc.mp hnData.1).1
    omega
  have hlower : 2 ^ a ≤ n - 1 := by
    rw [← hnData.2]
    exact Nat.pow_log_le_self 2 hnPos.ne'
  have hupper : n - 1 < 2 ^ (a + 1) := by
    rw [← hnData.2]
    exact Nat.lt_pow_succ_log_self (by omega) (n - 1)
  rw [Finset.mem_Ioc]
  rw [pow_succ] at hupper
  omega

theorem disjoint_detectorDyadicShell_of_ne (Y N : ℕ) {a b : ℕ}
    (hab : a ≠ b) :
    Disjoint (detectorDyadicShell Y N a) (detectorDyadicShell Y N b) := by
  change Disjoint (detectorDyadicShell Y N a) (detectorDyadicShell Y N b)
  rw [Finset.disjoint_left]
  intro n hna hnb
  have haEq := (Finset.mem_filter.mp hna).2
  have hbEq := (Finset.mem_filter.mp hnb).2
  exact hab (haEq.symm.trans hbEq)

theorem pairwiseDisjoint_detectorDyadicShell (Y N : ℕ) :
    ((Finset.range (Nat.log 2 N + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (detectorDyadicShell Y N) := by
  intro a ha b hb hab
  exact disjoint_detectorDyadicShell_of_ne Y N hab

/-- All binary shells through `log₂ N` partition `(Y,N]`. -/
theorem biUnion_detectorDyadicShell (Y N : ℕ) :
    (Finset.range (Nat.log 2 (N - 1) + 1)).biUnion
        (detectorDyadicShell Y N) = Finset.Ioc Y N := by
  classical
  ext n
  constructor
  · intro hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨a, ha, hna⟩ := hn
    exact (Finset.mem_filter.mp hna).1
  · intro hn
    have hnUpper : n ≤ N := (Finset.mem_Ioc.mp hn).2
    have hsubLe : n - 1 ≤ N - 1 := Nat.sub_le_sub_right hnUpper 1
    have hlogLe : Nat.log 2 (n - 1) ≤ Nat.log 2 (N - 1) :=
      Nat.log_mono_right hsubLe
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 (n - 1), Finset.mem_range.mpr (by omega), ?_⟩
    rw [detectorDyadicShell, Finset.mem_filter]
    exact ⟨hn, rfl⟩

private theorem primitiveNegativeDirichletBlockMass_shortBlock_eq
    (Q : ℕ) (s : Finset ℕ) (A H : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    primitiveNegativeDirichletBlockMass Q (shortBlock s A H) c t =
      primitiveNegativeDirichletMass Q s c t := by
  classical
  unfold primitiveNegativeDirichletBlockMass primitiveNegativeDirichletMass
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun z : ℝ ↦ (q : ℝ) / (q.totient : ℝ) * z)
  apply Finset.sum_congr rfl
  intro psi hpsi
  congr 2
  rw [← Finset.sum_biUnion (pairwiseDisjoint_shortBlock s A H),
    biUnion_shortBlock]

private theorem sum_shortBlock_energy_eq
    (s : Finset ℕ) (A H : ℕ) (c : ℕ → ℂ) :
    (∑ i : {i // i ∈ shortBlockIndices s A H},
        ∑ n ∈ shortBlock s A H i, ‖c n‖ ^ 2) =
      ∑ n ∈ s, ‖c n‖ ^ 2 := by
  classical
  rw [← Finset.sum_biUnion (pairwiseDisjoint_shortBlock s A H),
    biUnion_shortBlock]

/-- Raw hybrid mean-square estimate on one dyadic shell, for any positive
additive block length. -/
theorem intervalIntegral_primitiveNegativeDirichletMass_shell_le
    (Q Y N a H : ℕ) (hY : 1 ≤ Y) (hH : 0 < H) (c : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
        primitiveNegativeDirichletMass Q
          (detectorDyadicShell Y N a) c t) ≤
      Real.exp 1 *
        Real.exp ((T * ((H : ℝ) / (2 ^ a : ℕ))) ^ 2) *
        (T + 2 * Real.pi * (((H : ℝ) / (2 * 2 ^ a : ℕ))⁻¹)) *
        ((H : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2 := by
  let s := detectorDyadicShell Y N a
  let A := 2 ^ a
  have hA : 1 ≤ A := Nat.one_le_pow a 2 (by omega)
  have hs : s ⊆ Finset.Ioc A (2 * A) := by
    simpa only [s, A] using detectorDyadicShell_subset Y N a hY
  let ι := {i // i ∈ shortBlockIndices s A H}
  have hmain := intervalIntegral_primitiveNegativeDirichletBlockMass_le
    (ι := ι) Q H (shortBlock s A H) (shortBlockStart A H)
      (fun i ↦ shortBlock_subset_Ioc s A H hH hs i)
      (shortBlockCenter A H)
      (show 0 < (H : ℝ) / (2 * A : ℕ) by positivity) hT
      (shortBlockCenter_separated hA hH hs) c
      (fun i j hij ↦ by
        have hp := pairwiseDisjoint_shortBlock s A H
        exact hp (Finset.mem_univ i) (Finset.mem_univ j) hij)
      (show 0 ≤ (H : ℝ) / A by positivity)
      (fun i n hn ↦ shortBlock_log_offset_le hA hH hs i n hn)
  have hmass : primitiveNegativeDirichletBlockMass Q (shortBlock s A H) c =
      primitiveNegativeDirichletMass Q s c := by
    funext t
    exact primitiveNegativeDirichletBlockMass_shortBlock_eq Q s A H c t
  rw [hmass, sum_shortBlock_energy_eq] at hmain
  simpa only [s, A] using hmain

/-- The dyadic shell energy of an order-`k` detector is bounded by a simple
pointwise estimate. -/
theorem sum_detectorDyadicShell_weighted_energy_le
    (Y N a k : ℕ) (hY : 1 ≤ Y) (eta : ℝ) (heta : 0 ≤ eta) :
    (∑ n ∈ detectorDyadicShell Y N a,
        ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2) ≤
      (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
        (2 ^ a : ℕ) ^ (-(1 + 2 * eta)) := by
  let A : ℕ := 2 ^ a
  have hA : 1 ≤ A := Nat.one_le_pow a 2 (by omega)
  have hcard : (detectorDyadicShell Y N a).card ≤ A := by
    apply (Finset.card_le_card (detectorDyadicShell_subset Y N a hY)).trans
    rw [Nat.card_Ioc]
    omega
  have hpoint : ∀ n ∈ detectorDyadicShell Y N a,
      ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 ≤
        ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
          (A : ℝ) ^ (-(2 + 2 * eta)) := by
    intro n hn
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have hnPosNat : 0 < n := by omega
    have hnOneNat : 1 ≤ n := by omega
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hnPosNat
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnOneNat
    have hlogNonneg : 0 ≤ Real.log n := Real.log_nonneg hnOne
    have hlogLe : Real.log n ≤ (a + 1 : ℕ) * Real.log 2 := by
      calc
        Real.log n ≤ Real.log ((2 ^ (a + 1) : ℕ) : ℝ) := by
          apply Real.log_le_log hnPos
          rw [pow_succ]
          exact_mod_cast (show n ≤ 2 ^ a * 2 by simpa [mul_comm] using hnBounds.2)
        _ = ((a + 1 : ℕ) : ℝ) * Real.log 2 := by
          rw [show ((2 ^ (a + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (a + 1) by norm_cast,
            Real.log_pow]
    have hLambda : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    have hlogWeight : Real.log n ^ k *
        ArithmeticFunction.vonMangoldt n ≤
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (k + 1) := by
      calc
        Real.log n ^ k * ArithmeticFunction.vonMangoldt n ≤
            Real.log n ^ k * Real.log n := by gcongr
        _ = Real.log n ^ (k + 1) := by rw [pow_succ]
        _ ≤ (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (k + 1) :=
          pow_le_pow_left₀ hlogNonneg hlogLe (k + 1)
    unfold weightedVonMangoldtMajorant
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
    have hrpow : (n : ℝ) ^ (-(2 + 2 * eta)) ≤
        (A : ℝ) ^ (-(2 + 2 * eta)) := by
      apply Real.rpow_le_rpow_of_nonpos
      · exact_mod_cast hA
      · exact_mod_cast hnBounds.1.le
      · linarith
    calc
      (Real.log n ^ k * ArithmeticFunction.vonMangoldt n) ^ 2 *
          ((n : ℝ) ^ (-(1 + eta))) ^ 2 ≤
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (k + 1)) ^ 2 *
            (n : ℝ) ^ (-(2 + 2 * eta)) := by
        have hsq : ((n : ℝ) ^ (-(1 + eta))) ^ 2 =
            (n : ℝ) ^ (-(2 + 2 * eta)) := by
          calc
            ((n : ℝ) ^ (-(1 + eta))) ^ 2 =
                ((n : ℝ) ^ (-(1 + eta))) ^ (2 : ℝ) :=
              (Real.rpow_natCast _ 2).symm
            _ = (n : ℝ) ^ (-(1 + eta) * 2) :=
              (Real.rpow_mul hnPos.le _ _).symm
            _ = (n : ℝ) ^ (-(2 + 2 * eta)) := by congr 1 <;> ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hlogWeight 2) (by positivity)
      _ ≤ ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (k + 1)) ^ 2 *
          (A : ℝ) ^ (-(2 + 2 * eta)) := by gcongr
      _ = ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
          (A : ℝ) ^ (-(2 + 2 * eta)) := by
        rw [← pow_mul]
        congr 2
        omega
  calc
    (∑ n ∈ detectorDyadicShell Y N a,
        ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2) ≤
        ∑ _n ∈ detectorDyadicShell Y N a,
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
            (A : ℝ) ^ (-(2 + 2 * eta)) := by
      exact Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = ((detectorDyadicShell Y N a).card : ℝ) *
        (((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
          (A : ℝ) ^ (-(2 + 2 * eta))) := by simp
    _ ≤ (A : ℝ) *
        (((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
          (A : ℝ) ^ (-(2 + 2 * eta))) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
        (A : ℝ) ^ (-(1 + 2 * eta)) := by
      have hApos : (0 : ℝ) < A := by positivity
      calc
        (A : ℝ) *
            (((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
              (A : ℝ) ^ (-(2 + 2 * eta))) =
            ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
              ((A : ℝ) ^ (1 : ℝ) * (A : ℝ) ^ (-(2 + 2 * eta))) := by
          rw [Real.rpow_one]
          ring
        _ = ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
            (A : ℝ) ^ ((1 : ℝ) + -(2 + 2 * eta)) := by
          rw [Real.rpow_add hApos]
        _ = _ := by ring_nf
    _ = _ := by rfl

end

end Erdos48
