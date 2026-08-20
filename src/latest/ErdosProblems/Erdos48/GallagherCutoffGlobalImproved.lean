/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherCutoffImproved

/-!
# Global amplified Gallagher cutoff energy

This module sums the amplified cutoff-band estimate uniformly over all
partial-summation endpoints.  It exposes the improved main logarithmic
term and the higher-prime-power tail separately.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

noncomputable def gallagherHigherPrimePowerShellTail
    (Y N : ℕ) : ℝ :=
  ∑ a ∈ detectorActiveShells Y N,
    ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
      Real.sqrt (2 * (2 ^ a : ℕ)) *
        ((2 ^ a : ℕ) : ℝ)⁻¹)

theorem detectorActiveShells_mono_right
    {Y m N : ℕ} (hmN : m ≤ N) :
    detectorActiveShells Y m ⊆ detectorActiveShells Y N := by
  intro a ha
  obtain ⟨haRange, n, hn⟩ := Finset.mem_filter.mp ha
  have hnData := Finset.mem_filter.mp hn
  have hnBand := Finset.mem_Ioc.mp hnData.1
  have hnN : n ∈ Finset.Ioc Y N :=
    Finset.mem_Ioc.mpr ⟨hnBand.1, hnBand.2.trans hmN⟩
  have hnNew : n ∈ detectorDyadicShell Y N a :=
    Finset.mem_filter.mpr ⟨hnN, hnData.2⟩
  have hsub : m - 1 ≤ N - 1 := Nat.sub_le_sub_right hmN 1
  have hlog : Nat.log 2 (m - 1) ≤ Nat.log 2 (N - 1) :=
    Nat.log_mono_right hsub
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by
      have := Finset.mem_range.mp haRange
      omega), ⟨n, hnNew⟩⟩

theorem sum_activeShell_log_le_logSquare
    (Y m N : ℕ) (hmN : m ≤ N) :
    (∑ a ∈ detectorActiveShells Y m,
        ((a + 1 : ℕ) : ℝ) * Real.log 2) ≤
      ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2 := by
  let M : ℕ := Nat.log 2 (N - 1) + 1
  have hsubset := detectorActiveShells_mono_right (Y := Y) hmN
  have haM : ∀ a ∈ detectorActiveShells Y m, a + 1 ≤ M := by
    intro a ha
    have haN := hsubset ha
    have haRange := Finset.mem_range.mp
      ((detectorActiveShells_subset Y N) haN)
    dsimp [M]
    omega
  have hterm : ∀ a ∈ detectorActiveShells Y m,
      ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤ (M : ℝ) * Real.log 2 := by
    intro a ha
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast haM a ha)
      (Real.log_nonneg (by norm_num))
  have hcard : ((detectorActiveShells Y m).card : ℝ) ≤ M := by
    exact_mod_cast (detectorActiveShells_card_le Y m).trans (by
      have hlog : Nat.log 2 (m - 1) ≤ Nat.log 2 (N - 1) :=
        Nat.log_mono_right (Nat.sub_le_sub_right hmN 1)
      dsimp [M]
      omega)
  calc
    _ ≤ ∑ _a ∈ detectorActiveShells Y m,
        (M : ℝ) * Real.log 2 := Finset.sum_le_sum hterm
    _ = ((detectorActiveShells Y m).card : ℝ) *
        ((M : ℝ) * Real.log 2) := by simp
    _ ≤ (M : ℝ) * ((M : ℝ) * Real.log 2) := by gcongr
    _ = _ := by dsimp [M]; ring

theorem gallagherHigherPrimePowerShellTail_mono_right
    {Y m N : ℕ} (hmN : m ≤ N) :
    gallagherHigherPrimePowerShellTail Y m ≤
      gallagherHigherPrimePowerShellTail Y N := by
  unfold gallagherHigherPrimePowerShellTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact detectorActiveShells_mono_right hmN
  · intro a ha hnot
    positivity

/-- Uniform amplified energy of all Abel partial sums.  The first term has
one fewer logarithm after division by the amplifier coefficient; the second
is the explicitly displayed higher-prime-power remainder. -/
theorem mul_intervalIntegral_unweightedPrimitiveCutoffEnergy_le
    (Q Amp Y N T : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q Amp)
    (hY : 1 ≤ Y)
    (hheight : 4 * (T + 1) ≤ Y)
    (hrough : Q * Amp ≤ Y)
    (hroughConductor : 2 * ((T + 1) * (Q * Amp) ^ 2) ≤ Y)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ Y) :
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveCutoffVonMangoldtEnergy Q Y N t) ≤
      (8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
          ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2 +
        8 * L * Real.exp 2 * (1 + 16 * Real.pi) *
          gallagherHigherPrimePowerShellTail Y N) *
        ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹ := by
  let P : ℝ := 8 * Real.exp 2 * (1 + 16 * Real.pi) *
    (Real.log 4 + 4) *
      ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2
  let H : ℝ := 8 * L * Real.exp 2 * (1 + 16 * Real.pi) *
    gallagherHigherPrimePowerShellTail Y N
  have hband (m : ℕ) (hm : m ∈ Finset.Icc Y N) :
      L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y m)
          cutoffVonMangoldtCoefficient t) ≤ P + H := by
    have hmN := (Finset.mem_Icc.mp hm).2
    have hmain := mul_intervalIntegral_unweightedCutoff_adaptive_le
      Q Amp Y m T L hL hcoeff hY hheight hrough hroughConductor hconductor
    have hp := sum_activeShell_log_le_logSquare Y m N hmN
    have hh := gallagherHigherPrimePowerShellTail_mono_right
      (Y := Y) hmN
    calc
      _ ≤ 8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
            ∑ a ∈ detectorActiveShells Y m,
              ((a + 1 : ℕ) : ℝ) * Real.log 2 +
          8 * L * Real.exp 2 * (1 + 16 * Real.pi) *
            gallagherHigherPrimePowerShellTail Y m := by
        simpa only [gallagherHigherPrimePowerShellTail] using hmain
      _ ≤ P + H := by
        apply add_le_add
        · dsimp [P]
          calc
            8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
                ∑ a ∈ detectorActiveShells Y m,
                  ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
              (8 * Real.exp 2 * (1 + 16 * Real.pi) *
                (Real.log 4 + 4)) *
                (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
                  Real.log 2) :=
              mul_le_mul_of_nonneg_left hp (by positivity)
            _ = _ := by ring
        · dsimp [H]
          exact mul_le_mul_of_nonneg_left hh (by positivity)
  unfold unweightedPrimitiveCutoffVonMangoldtEnergy
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    calc
      (∑ m ∈ Finset.Icc Y N,
          L * (∫ t in (0 : ℝ)..(T : ℝ),
            (m : ℝ)⁻¹ *
              unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y m)
                cutoffVonMangoldtCoefficient t)) =
        ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹ *
          (L * (∫ t in (0 : ℝ)..(T : ℝ),
            unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y m)
              cutoffVonMangoldtCoefficient t)) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [intervalIntegral.integral_const_mul]
          ring
      _ ≤ ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹ * (P + H) := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left (hband m hm) (by positivity)
      _ = (P + H) * ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = _ := by rfl
  · intro m hm
    exact (continuous_const.mul
      (continuous_unweightedPrimitiveNegativeDirichletMass Q
        (Finset.Ioc Y m) cutoffVonMangoldtCoefficient)).intervalIntegrable _ _

end Erdos48
