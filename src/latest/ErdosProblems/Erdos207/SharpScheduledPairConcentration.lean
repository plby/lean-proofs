/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousAliveMartingaleConcentration
import ErdosProblems.Erdos207.PairAggregateDeletionDrift

/-!
# Pair concentration with clock-dependent sharp envelopes

This is the probabilistic realization of `SharpScheduledPairTrajectories`.
All four envelopes are read at the current stopped-process clock; no terminal
minimum or maximum is substituted into the drift or variance estimates.
-/

namespace Erdos207

open Finset

noncomputable section

theorem probability_timedStoppedGreedy_exists_pair_sharpScheduled_deviation_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V)
    (D d M u : ℕ → ℕ) (Kpair Kglobal Kinc JUpper : ℕ)
    (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (hDpos : ∀ i, i < n → 0 < D i)
    (hD : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → D i ≤ S.available.card)
    (hDgap : ∀ i, i < n → u i < D i)
    (hM : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → S.available.card ≤ M i)
    (hfloor : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → HasAvailablePairFloor (d i) S)
    (hupper : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → HasAvailablePairCutoff (u i) S)
    (hpairTwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → HasPairTwoAwayCutoff F Kpair S)
    (hglobal : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → HasTwoAwayCutoff F Kglobal S)
    (hinc : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hdone : ∀ i, i < n → 1 ≤ d i)
    (hsmall : ∀ i, i < n → 3 + Kpair < d i)
    (hupperJump : ∀ i, i < n →
      sharpScheduledPairUpperRate (M i) (d i) (u i) ≤ JUpper)
    (hlowerDeath : ∀ i, i < n →
      sharpScheduledPairLowerRate (D i) (u i) Kinc ≤ d i)
    (hvarianceUpper : ∀ i, i < n →
      sharpScheduledPairUpperVariance (D i) (u i) Kpair Kglobal
        (sharpScheduledPairUpperRate (M i) (d i) (u i)) ≤ v)
    (hvarianceLower : ∀ i, i < n →
      sharpScheduledPairLowerVariance (D i) (u i) Kpair Kinc
        (sharpScheduledPairLowerRate (D i) (u i) Kinc) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let qUpper := sharpScheduledPairUpperTarget S₀ M d u
    let qLower := sharpScheduledPairLowerTarget S₀ D u Kinc
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let qUpper := sharpScheduledPairUpperTarget S₀ M d u
  let qLower := sharpScheduledPairLowerTarget S₀ D u Kinc
  let upper : PairOn V → ℕ → GreedyStateOn V → ℝ := fun P i S ↦
    fixedPairUpperDeviation (qUpper P) S₀ P.1 i S
  let lower : PairOn V → ℕ → GreedyStateOn V → ℝ := fun P i S ↦
    fixedPairLowerDeviation (qLower P) S₀ P.1 i S
  apply probability_timedStoppedGreedy_exists_pair_two_observables_le_exp
    n F active S₀ upper lower JUpper (3 + Kpair) theta a v hInv₀
  · intro P i hi S hS hactive _halive S' hmass _hS' _halive'
    have hA : S.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos i hi).trans_le (hD i hi S hS hactive)
    have hdelta := (greedyKernel_fixedPair_increment_mem_interval
      hS hA (hupper i hi S hS hactive) (hglobal i hi S hS hactive)
        hmass (P := P.1)).2
    have hrate := hupperJump i hi
    have hdq : qUpper P (i + 1) - qUpper P i =
        -sharpScheduledPairUpperRate (M i) (d i) (u i) :=
      sharpScheduledPairUpperTarget_succ_sub S₀ M d u P i
    simp only [upper, fixedPairUpperDeviation]
    linarith
  · intro P i hi S hS hactive halive
    have hA : S.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos i hi).trans_le (hD i hi S hS hactive)
    have hrate := sharpScheduledPairUpperRate_le_current
      hA (hM i hi S hS hactive) (hfloor i hi S hS hactive)
        (hupper i hi S hS hactive) halive
    have hdrift :
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * d i - 2 - u i : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i := by
      rw [show qUpper P (i + 1) - qUpper P i =
        -sharpScheduledPairUpperRate (M i) (d i) (u i) by
          exact sharpScheduledPairUpperTarget_succ_sub S₀ M d u P i]
      linarith
    have hraw :=
      greedyKernel_expectationReal_fixedPairUpperIncrement_if_alive_le_zero_of_pairCutoff
        P.2 hS hA (hupper i hi S hS hactive)
          (hpairTwo i hi S hS hactive) (hfloor i hi S hS hactive)
          (hdone i hi) halive (hsmall i hi)
          (qUpper P (i + 1) - qUpper P i)
          (by
            rw [sharpScheduledPairUpperTarget_succ_sub]
            exact neg_nonpos.mpr (sharpScheduledPairUpperRate_nonneg _ _ _))
          hdrift
    have hfun : (fun S' ↦ if PairAlive P.1 S' then
          upper P (i + 1) S' - upper P i S else 0) =
        (fun S' ↦ if PairAlive P.1 S' then
          (fixedPairAvailableCountReal S₀ P.1 S' -
            fixedPairAvailableCountReal S₀ P.1 S) -
              (qUpper P (i + 1) - qUpper P i) else 0) := by
      funext S'
      split <;> simp only [upper, fixedPairUpperDeviation] <;> ring
    rw [hfun]
    exact hraw
  · intro P i hi S hS hactive _halive
    have hA : S.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos i hi).trans_le (hD i hi S hS hactive)
    let inc : GreedyStateOn V → ℝ := fun S' ↦
      fixedPairAvailableCountReal S₀ P.1 S' -
        fixedPairAvailableCountReal S₀ P.1 S
    let dq : ℝ := qUpper P (i + 1) - qUpper P i
    have hpoint : ∀ S',
        (if PairAlive P.1 S' then
            (upper P (i + 1) S' - upper P i S) ^ 2 else 0) ≤
          2 * (if PairAlive P.1 S' then (inc S') ^ 2 else 0) +
            2 * dq ^ 2 := by
      intro S'
      by_cases halive' : PairAlive P.1 S'
      · simp only [halive', if_true]
        have hobs : upper P (i + 1) S' - upper P i S = inc S' - dq := by
          simp only [upper, fixedPairUpperDeviation, inc, dq]
          ring
        rw [hobs]
        nlinarith [sq_nonneg (inc S' + dq)]
      · simp [halive', sq_nonneg dq]
    calc
      (greedyKernel F S).expectationReal (fun S' ↦
          if PairAlive P.1 S' then
            (upper P (i + 1) S' - upper P i S) ^ 2 else 0) ≤
        (greedyKernel F S).expectationReal (fun S' ↦
          2 * (if PairAlive P.1 S' then (inc S') ^ 2 else 0) +
            2 * dq ^ 2) := FiniteLaw.expectationReal_mono _ hpoint
      _ = 2 * (greedyKernel F S).expectationReal (fun S' ↦
            if PairAlive P.1 S' then (inc S') ^ 2 else 0) + 2 * dq ^ 2 := by
          rw [FiniteLaw.expectationReal_add,
            FiniteLaw.expectationReal_const_mul,
            FiniteLaw.expectationReal_const]
      _ ≤ 2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * u i + Kglobal : ℕ) : ℝ)))) + 2 * dq ^ 2 := by
          have hsquare :=
            greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_of_pairCutoff
              P.2 hS hA (hupper i hi S hS hactive)
                (hpairTwo i hi S hS hactive) (hglobal i hi S hS hactive)
          exact add_le_add (mul_le_mul_of_nonneg_left hsquare (by norm_num)) le_rfl
      _ ≤ sharpScheduledPairUpperVariance (D i) (u i) Kpair Kglobal
          (sharpScheduledPairUpperRate (M i) (d i) (u i)) := by
          rw [show dq = -sharpScheduledPairUpperRate (M i) (d i) (u i) by
            exact sharpScheduledPairUpperTarget_succ_sub S₀ M d u P i]
          simpa only [neg_sq] using sharpScheduledPairUpperVariance_current_le
            (P := P) (r := sharpScheduledPairUpperRate (M i) (d i) (u i))
              (hDpos i hi) (hD i hi S hS hactive) (hupper i hi S hS hactive)
      _ ≤ v := hvarianceUpper i hi
  · intro P i hi S hS hactive _halive S' hmass _hS' halive'
    have hA : S.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos i hi).trans_le (hD i hi S hS hactive)
    apply fixedPairLowerDeviation_alive_increment_le_of_pairCutoff
      P.2 hS hA (hpairTwo i hi S hS hactive)
    · rw [sharpScheduledPairLowerTarget_succ_sub]
      exact neg_nonpos.mpr (sharpScheduledPairLowerRate_nonneg _ _ _)
    · exact hmass
    · exact halive'
  · intro P i hi S hS hactive halive
    have hA : S.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos i hi).trans_le (hD i hi S hS hactive)
    have hdrift : qLower P (i + 1) - qLower P i ≤
        -((D i - u i : ℕ) : ℝ)⁻¹ *
          (((u i : ℝ) * (2 * u i : ℕ)) + Kinc) := by
      rw [sharpScheduledPairLowerTarget_succ_sub]
      simp only [sharpScheduledPairLowerRate]
      ring_nf
      exact le_refl _
    have hdqLower : -(d i : ℝ) ≤ qLower P (i + 1) - qLower P i := by
      rw [sharpScheduledPairLowerTarget_succ_sub]
      linarith [hlowerDeath i hi]
    have hraw :=
      greedyKernel_expectationReal_fixedPairLowerIncrement_if_alive_le_zero
        P.2 hS hA (hD i hi S hS hactive) (hDgap i hi)
          (hupper i hi S hS hactive) (hpairTwo i hi S hS hactive)
          (hinc i hi S hS hactive) (hfloor i hi S hS hactive) halive
          (hsmall i hi) (qLower P (i + 1) - qLower P i) hdqLower
          (by
            rw [sharpScheduledPairLowerTarget_succ_sub]
            exact neg_nonpos.mpr (sharpScheduledPairLowerRate_nonneg _ _ _))
          hdrift
    have hfun : (fun S' ↦ if PairAlive P.1 S' then
          lower P (i + 1) S' - lower P i S else 0) =
        (fun S' ↦ if PairAlive P.1 S' then
          (qLower P (i + 1) - qLower P i) -
            (fixedPairAvailableCountReal S₀ P.1 S' -
              fixedPairAvailableCountReal S₀ P.1 S) else 0) := by
      funext S'
      split <;> simp only [lower, fixedPairLowerDeviation] <;> ring
    rw [hfun]
    exact hraw
  · intro P i hi S hS hactive _halive
    have hA : S.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos i hi).trans_le (hD i hi S hS hactive)
    let inc : GreedyStateOn V → ℝ := fun S' ↦
      fixedPairAvailableCountReal S₀ P.1 S' -
        fixedPairAvailableCountReal S₀ P.1 S
    let dq : ℝ := qLower P (i + 1) - qLower P i
    have hpoint : ∀ S',
        (if PairAlive P.1 S' then
            (lower P (i + 1) S' - lower P i S) ^ 2 else 0) ≤
          2 * (if PairAlive P.1 S' then (inc S') ^ 2 else 0) +
            2 * dq ^ 2 := by
      intro S'
      by_cases halive' : PairAlive P.1 S'
      · simp only [halive', if_true]
        have hobs : lower P (i + 1) S' - lower P i S = dq - inc S' := by
          simp only [lower, fixedPairLowerDeviation, inc, dq]
          ring
        rw [hobs]
        nlinarith [sq_nonneg (inc S' + dq)]
      · simp [halive', sq_nonneg dq]
    calc
      (greedyKernel F S).expectationReal (fun S' ↦
          if PairAlive P.1 S' then
            (lower P (i + 1) S' - lower P i S) ^ 2 else 0) ≤
        (greedyKernel F S).expectationReal (fun S' ↦
          2 * (if PairAlive P.1 S' then (inc S') ^ 2 else 0) +
            2 * dq ^ 2) := FiniteLaw.expectationReal_mono _ hpoint
      _ = 2 * (greedyKernel F S).expectationReal (fun S' ↦
            if PairAlive P.1 S' then (inc S') ^ 2 else 0) + 2 * dq ^ 2 := by
          rw [FiniteLaw.expectationReal_add,
            FiniteLaw.expectationReal_const_mul,
            FiniteLaw.expectationReal_const]
      _ ≤ 2 * ((S.available.card : ℝ)⁻¹ *
            (((3 + Kpair : ℕ) : ℝ) *
              (((availableTrianglesContainingPair S P.1).card : ℝ) *
                (3 * u i : ℕ) + Kinc))) + 2 * dq ^ 2 := by
          have hsquare :=
            greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_mixedCutoffs
              P.2 hS hA (hupper i hi S hS hactive)
                (hpairTwo i hi S hS hactive) (hinc i hi S hS hactive)
          exact add_le_add (mul_le_mul_of_nonneg_left hsquare (by norm_num)) le_rfl
      _ ≤ sharpScheduledPairLowerVariance (D i) (u i) Kpair Kinc
          (sharpScheduledPairLowerRate (D i) (u i) Kinc) := by
          rw [show dq = -sharpScheduledPairLowerRate (D i) (u i) Kinc by
            exact sharpScheduledPairLowerTarget_succ_sub S₀ D u Kinc P i]
          simpa only [neg_sq] using sharpScheduledPairLowerVariance_current_le
            (P := P) (r := sharpScheduledPairLowerRate (D i) (u i) Kinc)
              (hDpos i hi) (hD i hi S hS hactive) (hupper i hi S hS hactive)
      _ ≤ v := hvarianceLower i hi
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

end

end Erdos207
