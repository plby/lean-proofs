/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperPowerfulCutoffNumerics
import ErdosProblems.Erdos446.UpperPowerfulFiberCover
import ErdosProblems.Erdos446.UpperPowerfulWeightedMass
import ErdosProblems.Erdos446.UpperBridgeAudit

/-!
# Erdős Problem 446: unconditional upper sieve/cluster reduction

This module assembles Ford's Lemma 3.2.  Large powerful parts are removed by
the convergent squarefull tail; small powerful parts are summed with the
uniform divisor-weighted powerful mass; and the varying logarithmic
denominator is finally removed by Lemma 3.3.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

local instance powerfulSieveAssemblyDecidable :
    DecidablePred Erdos469.Powerful := Classical.decPred _

/-- Ford's Lemma 3.2 in the exact normalization used by the upper bridge. -/
theorem exists_pos_dyadicUpperSieveClusterReduction :
    ∃ A : ℝ, ∃ Y : ℕ, 0 < A ∧
      DyadicUpperSieveClusterReduction A Y := by
  obtain ⟨K, hK, hfiber⟩ :=
    exists_pos_squarefreeCofactorFiber_le_targetDenominator
  obtain ⟨D, hD, hpowerMass⟩ :=
    exists_pos_sum_divisorCard_div_powerful_le
  obtain ⟨C, hC, hremove⟩ :=
    exists_pos_fordDyadicVariableDenominatorSum_le
  obtain ⟨Y₀, hnumeric⟩ := exists_fordPowerfulCutoff_numerics K hK
  let A₀ : ℝ := 2 * K + 1 + 12 * K * D
  let A : ℝ := A₀ * C
  let Y : ℕ := max 2 Y₀
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, Y, hA, ?_⟩
  intro y hy X hX
  have hyTwo : 2 ≤ y := (le_max_left 2 Y₀).trans hy
  have hyY₀ : Y₀ ≤ y := (le_max_right 2 Y₀).trans hy
  have hnum := hnumeric y hyY₀ X hX
  let Q : ℕ := fordPowerfulCutoff y
  rcases hnum with ⟨hQone, hQy, htail, hnum⟩
  let V : ℝ := fordVariableDenominatorSum y (2 * y)
  let G : ℝ := squarefreeClusterMass (2 * y) /
    Real.log (y : ℝ) ^ 2
  have hVpos : 0 < V := fordVariableDenominatorSum_pos hyTwo
  have hGlow : Real.log 2 / Real.log (y : ℝ) ^ 2 ≤ V :=
    log_two_div_log_sq_le_fordVariableDenominatorSum hyTwo
  have hQpos : 0 < Q := by omega
  have hyX : y ≤ X := by
    have hyy : y ≤ y * y := by nlinarith
    exact hyy.trans hX
  have hQX : Q ≤ X := hQy.trans hyX
  have hlarge := card_largePowerfulDivisorPrefix_real_le_dirichletTail
    (X := X) (y := y) (z := 2 * y) hQpos
  have hlarge' :
      ((largePowerfulDivisorPrefix X y (2 * y) Q).card : ℝ) ≤
        (X : ℝ) * V := by
    calc
      ((largePowerfulDivisorPrefix X y (2 * y) Q).card : ℝ) ≤
          (X : ℝ) * (Q : ℝ) ^ (-(7 / 16 : ℝ)) *
            Erdos469.powerfulNineSixteenthsMass := hlarge
      _ = (X : ℝ) * ((Q : ℝ) ^ (-(7 / 16 : ℝ)) *
            Erdos469.powerfulNineSixteenthsMass) := by ring
      _ ≤ (X : ℝ) *
          (Real.log 2 / Real.log (y : ℝ) ^ 2) := by
        gcongr
      _ ≤ (X : ℝ) * V := by gcongr
  have hfiberPoint : ∀ q ∈ smallPowerfulParts Q,
      ((squarefreeCofactorFiber X y (2 * y) q).card : ℝ) ≤
        12 * K * V * (X : ℝ) *
          ((q.divisors.card : ℝ) / (q : ℝ)) := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hqI := Finset.mem_Icc.mp hqData.1
    have hqpos : 0 < q := by omega
    let M : ℕ → ℕ := fun f ↦
      fordSquarefreeShellStart y (y / f)
    have hnumV : ∀ f ∈ q.divisors,
        let v := y / f
        let N := X / q + 1
        1 ≤ v ∧ v ≤ y ∧
        (y : ℝ) ^ (2 / 3 : ℝ) ≤ (v : ℝ) ∧
        4 * v ≤ M f ∧
        (y : ℝ) ^ (2 / 3 : ℝ) ≤ (M f / (4 * v) : ℕ) ∧
        ((2 * v + 1 : ℕ) : ℝ) ≤ K * V * (M f : ℝ) ∧
        2 * (M f : ℝ) ≤ K * V * (N : ℝ) ∧
        (((N / (2 * v + 1) : ℕ) + 1 : ℕ) : ℝ) ≤
          K * V * (N : ℝ) := by
      intro f hf
      obtain ⟨hv, hvy, hvscale, hMv, hscale, hendpoint,
          hMabsorb, hendabsorb⟩ := hnum q hqData.1 f hf
      refine ⟨hv, hvy, hvscale, hMv, hscale, ?_, ?_, ?_⟩
      · exact hendpoint.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGlow hK.le) (Nat.cast_nonneg _))
      · exact hMabsorb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGlow hK.le) (Nat.cast_nonneg _))
      · exact hendabsorb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGlow hK.le) (Nat.cast_nonneg _))
    have hbase := hfiber y X q M hyTwo hqpos hnumV
    have hdivpos : 0 < X / q := Nat.div_pos (hqI.2.trans hQX) hqpos
    have hNnat : X / q + 1 ≤ 2 * (X / q) := by omega
    have hNreal : ((X / q + 1 : ℕ) : ℝ) ≤
        2 * (X : ℝ) / (q : ℝ) := by
      calc
        ((X / q + 1 : ℕ) : ℝ) ≤
            ((2 * (X / q) : ℕ) : ℝ) := by exact_mod_cast hNnat
        _ = 2 * ((X / q : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 2 * ((X : ℝ) / (q : ℝ)) := by
          gcongr
          exact Nat.cast_div_le
        _ = 2 * (X : ℝ) / (q : ℝ) := by ring
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    calc
      ((squarefreeCofactorFiber X y (2 * y) q).card : ℝ) ≤
          6 * K * V * (X / q + 1 : ℕ) *
            (q.divisors.card : ℝ) := hbase
      _ ≤ 6 * K * V * (2 * (X : ℝ) / (q : ℝ)) *
            (q.divisors.card : ℝ) := by gcongr
      _ = 12 * K * V * (X : ℝ) *
          ((q.divisors.card : ℝ) / (q : ℝ)) := by
        field_simp [hqR.ne']
        ring
  have hsmall :
      (∑ q ∈ smallPowerfulParts Q,
        ((squarefreeCofactorFiber X y (2 * y) q).card : ℝ)) ≤
        12 * K * V * (X : ℝ) * D := by
    calc
      (∑ q ∈ smallPowerfulParts Q,
          ((squarefreeCofactorFiber X y (2 * y) q).card : ℝ)) ≤
          ∑ q ∈ smallPowerfulParts Q,
            12 * K * V * (X : ℝ) *
              ((q.divisors.card : ℝ) / (q : ℝ)) := by
        exact Finset.sum_le_sum fun q hq ↦ hfiberPoint q hq
      _ = 12 * K * V * (X : ℝ) *
          (∑ q ∈ smallPowerfulParts Q,
            ((q.divisors.card : ℝ) / (q : ℝ))) := by
        rw [Finset.mul_sum]
      _ ≤ 12 * K * V * (X : ℝ) * D := by
        have hm := hpowerMass Q
        change (∑ q ∈ smallPowerfulParts Q,
          ((q.divisors.card : ℝ) / (q : ℝ))) ≤ D at hm
        gcongr
  have honeI : 1 ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨le_rfl, hQone⟩
  have honeDiv : 1 ∈ (1 : ℕ).divisors := by simp
  have honeNum := hnum 1 honeI 1 honeDiv
  have honeEndpoint := honeNum.2.2.2.2.2.2.2
  have honeLeft : (1 : ℝ) ≤
      (((((X / 1 + 1) / (2 * (y / 1) + 1) : ℕ) + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.succ_pos ((X / 1 + 1) / (2 * (y / 1) + 1))
  have hXpos : 1 ≤ X := by omega
  have hXdouble : (X : ℝ) + 1 ≤ 2 * (X : ℝ) := by
    have hXposR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
    calc
      (X : ℝ) + 1 ≤ (X : ℝ) + (X : ℝ) := add_le_add_right hXposR _
      _ = 2 * (X : ℝ) := by ring
  have hone : (1 : ℝ) ≤ 2 * K * V * (X : ℝ) := by
    calc
      (1 : ℝ) ≤
          (((((X / 1 + 1) / (2 * (y / 1) + 1) : ℕ) + 1 : ℕ)) : ℝ) :=
        honeLeft
      _ ≤ K * (Real.log 2 / Real.log (y : ℝ) ^ 2) *
          ((X / 1 + 1 : ℕ) : ℝ) := honeEndpoint
      _ ≤ K * V * (2 * (X : ℝ)) := by
        norm_num
        gcongr
      _ = 2 * K * V * (X : ℝ) := by ring
  have hsplitNat :=
    divisorPrefixCount_le_largePowerfulCard_add_powerfulFibers
      (X := X) (y := y) (z := 2 * y) (Q := Q)
  have hsplit : (divisorPrefixCount X y (2 * y) : ℝ) ≤
      1 + (largePowerfulDivisorPrefix X y (2 * y) Q).card +
        ∑ q ∈ smallPowerfulParts Q,
          ((squarefreeCofactorFiber X y (2 * y) q).card : ℝ) := by
    exact_mod_cast hsplitNat
  have hcount : (divisorPrefixCount X y (2 * y) : ℝ) ≤
      A₀ * (X : ℝ) * V := by
    calc
      (divisorPrefixCount X y (2 * y) : ℝ) ≤
          1 + (largePowerfulDivisorPrefix X y (2 * y) Q).card +
            ∑ q ∈ smallPowerfulParts Q,
              ((squarefreeCofactorFiber X y (2 * y) q).card : ℝ) := hsplit
      _ ≤ 2 * K * V * (X : ℝ) + (X : ℝ) * V +
          12 * K * V * (X : ℝ) * D := by linarith
      _ = A₀ * (X : ℝ) * V := by
        dsimp [A₀]
        ring
  have hden := hremove y hyTwo
  unfold fordDyadicVariableDenominatorSum at hden
  have hXnonneg : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  calc
    (divisorPrefixCount X y (2 * y) : ℝ) ≤
        A₀ * (X : ℝ) * V := hcount
    _ ≤ A₀ * (X : ℝ) *
        (C * squarefreeClusterMass (2 * y) /
          Real.log (y : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hden (mul_nonneg hA₀.le hXnonneg)
    _ = A * (X : ℝ) * squarefreeClusterMass (2 * y) /
        Real.log (y : ℝ) ^ 2 := by
      dsimp [A]
      ring

end

end Erdos446
