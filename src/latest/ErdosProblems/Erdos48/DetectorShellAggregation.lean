/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.OptimizedDyadicDetector

/-!
# Aggregating the dyadic detector shells

The band detector is the sum of its nonempty binary shells.  Finite
Cauchy--Schwarz costs only the number of shells, after which the optimized
hybrid estimate can be applied shell by shell.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- The nonempty shells in the binary partition of `(Y,N]`. -/
noncomputable def detectorActiveShells (Y N : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (N - 1) + 1)).filter fun a ↦
    (detectorDyadicShell Y N a).Nonempty

theorem detectorActiveShells_subset (Y N : ℕ) :
    detectorActiveShells Y N ⊆
      Finset.range (Nat.log 2 (N - 1) + 1) := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

theorem detectorActiveShells_card_le (Y N : ℕ) :
    (detectorActiveShells Y N).card ≤ Nat.log 2 (N - 1) + 1 := by
  exact (Finset.card_le_card (detectorActiveShells_subset Y N)).trans_eq
    (Finset.card_range _)

theorem pairwiseDisjoint_detectorActiveShells (Y N : ℕ) :
    ((detectorActiveShells Y N : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (detectorDyadicShell Y N) := by
  intro a ha b hb hab
  exact disjoint_detectorDyadicShell_of_ne Y N hab

theorem biUnion_detectorActiveShells (Y N : ℕ) :
    (detectorActiveShells Y N).biUnion (detectorDyadicShell Y N) =
      Finset.Ioc Y N := by
  classical
  ext n
  constructor
  · intro hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨a, ha, hna⟩ := hn
    exact (Finset.mem_filter.mp hna).1
  · intro hn
    have hall : n ∈
        (Finset.range (Nat.log 2 (N - 1) + 1)).biUnion
          (detectorDyadicShell Y N) := by
      rw [biUnion_detectorDyadicShell]
      exact hn
    rw [Finset.mem_biUnion] at hall ⊢
    obtain ⟨a, ha, hna⟩ := hall
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, ⟨n, hna⟩⟩, hna⟩

private theorem norm_finset_sum_sq_le_card_mul_sum_norm_sq
    {α : Type*} (S : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ S, f x‖ ^ 2 ≤
      (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by
  calc
    ‖∑ x ∈ S, f x‖ ^ 2 ≤ (∑ x ∈ S, ‖f x‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ _x ∈ S, (1 : ℝ) ^ 2) *
        ∑ x ∈ S, ‖f x‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ ↦ (1 : ℝ)) (fun x ↦ ‖f x‖)
    _ = (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by simp

theorem continuous_primitiveNegativeDirichletMass
    (Q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (primitiveNegativeDirichletMass Q s c) := by
  unfold primitiveNegativeDirichletMass
  fun_prop

/-- Pointwise Cauchy--Schwarz after decomposing the complete band into its
nonempty binary shells. -/
theorem primitiveNegativeDirichletMass_band_le_shells
    (Q Y N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t ≤
      ((detectorActiveShells Y N).card : ℝ) *
        ∑ a ∈ detectorActiveShells Y N,
          primitiveNegativeDirichletMass Q
            (detectorDyadicShell Y N a) c t := by
  classical
  let S := detectorActiveShells Y N
  have hpoly (q : ℕ) (psi : primitiveCharacters q) :
      (∑ n ∈ Finset.Ioc Y N, c n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) =
        ∑ a ∈ S, ∑ n ∈ detectorDyadicShell Y N a,
          c n * psi.1 n *
            Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
    rw [← Finset.sum_biUnion (pairwiseDisjoint_detectorActiveShells Y N),
      biUnion_detectorActiveShells]
  unfold primitiveNegativeDirichletMass
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ‖∑ n ∈ Finset.Ioc Y N, c n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ((S.card : ℝ) *
              ∑ a ∈ S,
                ‖∑ n ∈ detectorDyadicShell Y N a,
                  c n * psi.1 n *
                    Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro psi hpsi
        rw [hpoly q psi]
        exact norm_finset_sum_sq_le_card_mul_sum_norm_sq S _
      · positivity
    _ = (S.card : ℝ) *
        ∑ a ∈ S,
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q,
                ‖∑ n ∈ detectorDyadicShell Y N a,
                  c n * psi.1 n *
                    Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      ring
    _ = _ := by rfl

/-- Integral form of the shell decomposition. -/
theorem intervalIntegral_primitiveNegativeDirichletMass_band_le_shells
    (Q Y N T : ℕ) (c : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t) ≤
      ((detectorActiveShells Y N).card : ℝ) *
        ∑ a ∈ detectorActiveShells Y N,
          ∫ t in (0 : ℝ)..(T : ℝ),
            primitiveNegativeDirichletMass Q
              (detectorDyadicShell Y N a) c t := by
  classical
  let S := detectorActiveShells Y N
  have hmono :
      (∫ t in (0 : ℝ)..(T : ℝ),
          primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t) ≤
        ∫ t in (0 : ℝ)..(T : ℝ),
          (S.card : ℝ) * ∑ a ∈ S,
            primitiveNegativeDirichletMass Q
              (detectorDyadicShell Y N a) c t := by
    apply intervalIntegral.integral_mono_on (by positivity)
    · exact (continuous_primitiveNegativeDirichletMass Q
        (Finset.Ioc Y N) c).intervalIntegrable 0 T
    · apply Continuous.intervalIntegrable
      apply continuous_const.mul
      apply continuous_finsetSum S
      intro a ha
      exact continuous_primitiveNegativeDirichletMass Q
        (detectorDyadicShell Y N a) c
    · intro t ht
      simpa only [S] using
        primitiveNegativeDirichletMass_band_le_shells Q Y N c t
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t) ≤
        ∫ t in (0 : ℝ)..(T : ℝ),
          (S.card : ℝ) * ∑ a ∈ S,
            primitiveNegativeDirichletMass Q
              (detectorDyadicShell Y N a) c t := hmono
    _ = (S.card : ℝ) *
        ∑ a ∈ S,
          ∫ t in (0 : ℝ)..(T : ℝ),
            primitiveNegativeDirichletMass Q
              (detectorDyadicShell Y N a) c t := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum]
      intro a ha
      exact (continuous_primitiveNegativeDirichletMass Q
        (detectorDyadicShell Y N a) c).intervalIntegrable 0 T
    _ = _ := by rfl

/-- Aggregated optimized hybrid bound for a detector band whose lower
endpoint dominates both height and conductor squared. -/
theorem intervalIntegral_weightedDetectorBand_le_shellSum
    (Q Y N T k : ℕ) (hY : 1 ≤ Y)
    (hheight : 2 * (T + 1) ≤ Y) (hconductor : 2 * Q ^ 2 ≤ Y)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
      ((detectorActiveShells Y N).card : ℝ) *
        ∑ a ∈ detectorActiveShells Y N,
          (2 * Real.exp 2 * (1 + 8 * Real.pi)) * (T + 1 : ℕ) *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
              (2 ^ a : ℕ) ^ (-(2 * eta)) := by
  let c : ℕ → ℂ := fun n ↦
    (weightedVonMangoldtMajorant eta k n : ℂ)
  refine (intervalIntegral_primitiveNegativeDirichletMass_band_le_shells
    Q Y N T c).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro a ha
    have hnonempty := (Finset.mem_filter.mp ha).2
    obtain ⟨n, hn⟩ := hnonempty
    have hnBand := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have hheightTwo : 2 * (T + 1) < 2 * 2 ^ a :=
      hheight.trans_lt (hnBand.1.trans_le hnBounds.2)
    have hconductorTwo : 2 * Q ^ 2 < 2 * 2 ^ a :=
      hconductor.trans_lt (hnBand.1.trans_le hnBounds.2)
    have hAheight : T + 1 ≤ 2 ^ a :=
      ((Nat.mul_lt_mul_left (by omega : 0 < 2)).mp hheightTwo).le
    have hAconductor : Q ^ 2 ≤ 2 ^ a :=
      ((Nat.mul_lt_mul_left (by omega : 0 < 2)).mp hconductorTwo).le
    exact intervalIntegral_optimizedDetectorShell_le
      Q Y N a T k hY hAheight hAconductor eta heta
  · positivity

/-- A single uniform expression bounding the complete shell sum.  The two
factors of the number of shells come respectively from Cauchy--Schwarz and
from summing the individual shell estimates. -/
theorem intervalIntegral_weightedDetectorBand_le
    (Q Y N T k : ℕ) (hY : 1 ≤ Y)
    (hheight : 2 * (T + 1) ≤ Y) (hconductor : 2 * Q ^ 2 ≤ Y)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
      (2 * Real.exp 2 * (1 + 8 * Real.pi)) * (T + 1 : ℕ) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
        ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
          (2 * (k + 1))) *
        (((Y : ℝ) / 2) ^ (-(2 * eta))) := by
  let S := detectorActiveShells Y N
  let M : ℕ := Nat.log 2 (N - 1) + 1
  let C : ℝ := 2 * Real.exp 2 * (1 + 8 * Real.pi)
  let W : ℝ := (((M : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
    (((Y : ℝ) / 2) ^ (-(2 * eta)))
  have hmain := intervalIntegral_weightedDetectorBand_le_shellSum
    Q Y N T k hY hheight hconductor eta heta
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ ((T + 1 : ℕ) : ℝ) := by positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hterm : ∀ a ∈ S,
      C * (T + 1 : ℕ) *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            (2 ^ a : ℕ) ^ (-(2 * eta)) ≤
        C * (T + 1 : ℕ) * W := by
    intro a ha
    have haRange := (Finset.mem_filter.mp ha).1
    have haM : a + 1 ≤ M := by
      dsimp [M] at haRange ⊢
      exact Finset.mem_range.mp haRange
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogFactor :
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) ≤
          ((M : ℝ) * Real.log 2) ^ (2 * (k + 1)) := by
      apply pow_le_pow_left₀ (by positivity)
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast haM) hlog2
    have hnonempty := (Finset.mem_filter.mp ha).2
    obtain ⟨n, hn⟩ := hnonempty
    have hnBand := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have hbase : (0 : ℝ) < (Y : ℝ) / 2 := by positivity
    have hbaseA : (Y : ℝ) / 2 ≤ (2 ^ a : ℕ) := by
      have hYtwoA : Y ≤ 2 * 2 ^ a := hnBand.1.le.trans hnBounds.2
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
        exact_mod_cast (show Y ≤ 2 ^ a * 2 by simpa [mul_comm] using hYtwoA))
    have hrpow :
        ((2 ^ a : ℕ) : ℝ) ^ (-(2 * eta)) ≤
          ((Y : ℝ) / 2) ^ (-(2 * eta)) := by
      apply Real.rpow_le_rpow_of_nonpos hbase hbaseA
      linarith
    have hproduct :
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            ((2 ^ a : ℕ) : ℝ) ^ (-(2 * eta)) ≤
          ((M : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            ((Y : ℝ) / 2) ^ (-(2 * eta)) := by
      exact mul_le_mul hlogFactor hrpow (by positivity) (by positivity)
    dsimp [W]
    calc
      C * (T + 1 : ℕ) *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            (2 ^ a : ℕ) ^ (-(2 * eta)) =
          (C * (T + 1 : ℕ)) *
            ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
              (2 ^ a : ℕ) ^ (-(2 * eta))) := by ring
      _ ≤ (C * (T + 1 : ℕ)) *
          (((M : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            ((Y : ℝ) / 2) ^ (-(2 * eta))) :=
        mul_le_mul_of_nonneg_left hproduct (mul_nonneg hC hD)
      _ = _ := by ring
  have hsum :
      (∑ a ∈ S,
          C * (T + 1 : ℕ) *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
              (2 ^ a : ℕ) ^ (-(2 * eta))) ≤
        (S.card : ℝ) * (C * (T + 1 : ℕ) * W) := by
    calc
      _ ≤ ∑ _a ∈ S, C * (T + 1 : ℕ) * W :=
        Finset.sum_le_sum fun a ha ↦ hterm a ha
      _ = _ := by simp
  have hcard : (S.card : ℝ) ≤ M := by
    exact_mod_cast detectorActiveShells_card_le Y N
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
        (S.card : ℝ) *
          ∑ a ∈ S,
            C * (T + 1 : ℕ) *
              (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
                (2 ^ a : ℕ) ^ (-(2 * eta)) := by
      simpa only [S, C] using hmain
    _ ≤ (S.card : ℝ) * ((S.card : ℝ) *
          (C * (T + 1 : ℕ) * W)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (M : ℝ) ^ 2 * (C * (T + 1 : ℕ) * W) := by
      have hScard : 0 ≤ (S.card : ℝ) := by positivity
      have hM0 : 0 ≤ (M : ℝ) := by positivity
      have hsquare : (S.card : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
      calc
        (S.card : ℝ) * ((S.card : ℝ) *
            (C * (T + 1 : ℕ) * W)) =
          (S.card : ℝ) ^ 2 * (C * (T + 1 : ℕ) * W) := by ring
        _ ≤ (M : ℝ) ^ 2 * (C * (T + 1 : ℕ) * W) :=
          mul_le_mul_of_nonneg_right hsquare (by positivity)
    _ = C * (T + 1 : ℕ) * (M : ℝ) ^ 2 *
          (((M : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
            (((Y : ℝ) / 2) ^ (-(2 * eta))) := by
      dsimp [W]
      ring
    _ = _ := by rfl

/-- Aggregated sharp hybrid bound.  The lower endpoint dominates the product
of height and conductor squared, so every nonempty dyadic shell may use the
height-free optimized estimate. -/
theorem intervalIntegral_weightedDetectorBand_hybrid_le_shellSum
    (Q Y N T k : ℕ) (hQ : 1 ≤ Q) (hY : 1 ≤ Y)
    (hhybrid : 2 * (T + 1) * Q ^ 2 ≤ Y)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
      ((detectorActiveShells Y N).card : ℝ) *
        ∑ a ∈ detectorActiveShells Y N,
          (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
              (2 ^ a : ℕ) ^ (-(2 * eta)) := by
  let c : ℕ → ℂ := fun n ↦
    (weightedVonMangoldtMajorant eta k n : ℂ)
  refine (intervalIntegral_primitiveNegativeDirichletMass_band_le_shells
    Q Y N T c).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro a ha
    have hnonempty := (Finset.mem_filter.mp ha).2
    obtain ⟨n, hn⟩ := hnonempty
    have hnBand := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have htwice : 2 * ((T + 1) * Q ^ 2) < 2 * 2 ^ a :=
      by simpa only [mul_assoc] using
        hhybrid.trans_lt (hnBand.1.trans_le hnBounds.2)
    have hshell : (T + 1) * Q ^ 2 ≤ 2 ^ a := by
      exact ((Nat.mul_lt_mul_left (by omega : 0 < 2)).mp htwice).le
    exact intervalIntegral_optimizedDetectorShell_hybrid_le
      Q Y N a T k hY hQ hshell eta heta
  · positivity

/-- A single height-free expression bounding the complete detector band. -/
theorem intervalIntegral_weightedDetectorBand_hybrid_le
    (Q Y N T k : ℕ) (hQ : 1 ≤ Q) (hY : 1 ≤ Y)
    (hhybrid : 2 * (T + 1) * Q ^ 2 ≤ Y)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
      (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
        ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
          (2 * (k + 1))) *
        (((Y : ℝ) / 2) ^ (-(2 * eta))) := by
  let S := detectorActiveShells Y N
  let M : ℕ := Nat.log 2 (N - 1) + 1
  let C : ℝ := 2 * Real.exp 2 * (1 + 8 * Real.pi)
  let W : ℝ := (((M : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
    (((Y : ℝ) / 2) ^ (-(2 * eta)))
  have hmain := intervalIntegral_weightedDetectorBand_hybrid_le_shellSum
    Q Y N T k hQ hY hhybrid eta heta
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hterm : ∀ a ∈ S,
      C * (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            (2 ^ a : ℕ) ^ (-(2 * eta)) ≤ C * W := by
    intro a ha
    have haRange := (Finset.mem_filter.mp ha).1
    have haM : a + 1 ≤ M := by
      dsimp [M] at haRange ⊢
      exact Finset.mem_range.mp haRange
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogFactor :
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) ≤
          ((M : ℝ) * Real.log 2) ^ (2 * (k + 1)) := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast haM) hlog2
    have hnonempty := (Finset.mem_filter.mp ha).2
    obtain ⟨n, hn⟩ := hnonempty
    have hnBand := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have hbase : (0 : ℝ) < (Y : ℝ) / 2 := by positivity
    have hbaseA : (Y : ℝ) / 2 ≤ (2 ^ a : ℕ) := by
      have hYtwoA : Y ≤ 2 * 2 ^ a := hnBand.1.le.trans hnBounds.2
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
        exact_mod_cast (show Y ≤ 2 ^ a * 2 by simpa [mul_comm] using hYtwoA))
    have hrpow :
        ((2 ^ a : ℕ) : ℝ) ^ (-(2 * eta)) ≤
          ((Y : ℝ) / 2) ^ (-(2 * eta)) := by
      apply Real.rpow_le_rpow_of_nonpos hbase hbaseA
      linarith
    have hproduct :
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            ((2 ^ a : ℕ) : ℝ) ^ (-(2 * eta)) ≤
          ((M : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            ((Y : ℝ) / 2) ^ (-(2 * eta)) := by
      exact mul_le_mul hlogFactor hrpow (by positivity) (by positivity)
    dsimp [W]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hC
  have hsum :
      (∑ a ∈ S,
          C * (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            (2 ^ a : ℕ) ^ (-(2 * eta))) ≤
        (S.card : ℝ) * (C * W) := by
    calc
      _ ≤ ∑ _a ∈ S, C * W := Finset.sum_le_sum fun a ha ↦ hterm a ha
      _ = _ := by simp
  have hcard : (S.card : ℝ) ≤ M := by
    exact_mod_cast detectorActiveShells_card_le Y N
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
        (S.card : ℝ) *
          ∑ a ∈ S,
            C * (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
              (2 ^ a : ℕ) ^ (-(2 * eta)) := by
      simpa only [S, C] using hmain
    _ ≤ (S.card : ℝ) * ((S.card : ℝ) * (C * W)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (M : ℝ) ^ 2 * (C * W) := by
      have hsquare : (S.card : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
        nlinarith [show (0 : ℝ) ≤ S.card by positivity,
          show (0 : ℝ) ≤ M by positivity]
      calc
        (S.card : ℝ) * ((S.card : ℝ) * (C * W)) =
            (S.card : ℝ) ^ 2 * (C * W) := by ring
        _ ≤ (M : ℝ) ^ 2 * (C * W) :=
          mul_le_mul_of_nonneg_right hsquare (mul_nonneg hC hW)
    _ = _ := by
      dsimp [M, C, W]
      ring

end

end Erdos48
