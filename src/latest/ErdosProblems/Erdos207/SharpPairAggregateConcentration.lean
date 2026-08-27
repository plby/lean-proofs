/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpPairConcentration
import ErdosProblems.Erdos207.PairAggregateDeletionDrift

/-! # Sharp lower-pair concentration with aggregate two-away drift -/

namespace Erdos207

open Finset

noncomputable section

/-- Lower-tail concentration in which the maximum two-away cutoff is used
only for the local surviving jump, while the drift and variance use the
aggregate incidence cutoff of the tracked pair star. -/
theorem probability_timedStoppedGreedy_fixedPair_sharp_alive_lower_le_exp_of_aggregateCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S0 : GreedyStateOn V) (P : Finset V) (hP : P.card = 2)
    (q : ℕ → ℝ) (Delta delta Kpair Kinc J : ℕ)
    (theta a v : ℝ)
    (hInv0 : GreedyInvariant F S0)
    (havailable : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → S.available.Nonempty)
    (hpair : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasAvailablePairCutoff Delta S)
    (hpairTwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasPairTwoAwayCutoff F Kpair S)
    (hinc : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hfloor : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasAvailablePairFloor delta S)
    (hqDeath : ∀ i, i < n → -(delta : ℝ) ≤ q (i + 1) - q i)
    (hqUpper : ∀ i, i < n → q (i + 1) - q i ≤ 0)
    (hjumpAlive : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → PairAlive P S →
      ∀ S', 0 < (greedyKernel F S).mass S' →
        PairTrajectoryInvariant F S0 S' → PairAlive P S' →
          fixedPairLowerDeviation q S0 P (i + 1) S' -
            fixedPairLowerDeviation q S0 P i S ≤ (J : ℝ))
    (hqDrift : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → PairAlive P S →
        q (i + 1) - q i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
                (3 * Delta : ℕ) + Kinc))
    (hvariance : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → PairAlive P S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((3 + Kpair : ℕ) : ℝ) *
              (((availableTrianglesContainingPair S P).card : ℝ) *
                (3 * Delta : ℕ) + Kinc))) +
          2 * (q (i + 1) - q i) ^ 2 ≤ v)
    (htheta : 0 < theta) (hthetaJ : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S0).probability
      (fun z ↦ PairAlive P z.2 ∧
        a ≤ fixedPairLowerDeviation q S0 P z.1.1 z.2 -
          fixedPairLowerDeviation q S0 P 0 S0) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  let obs : ℕ → GreedyStateOn V → ℝ :=
    fun i S ↦ fixedPairLowerDeviation q S0 P i S
  by_cases hAlive0 : PairAlive P S0
  · have hdriftFull : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S0 S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0 := by
      intro i hi S hS hactive halive
      calc
        (greedyKernel F S).expectationReal
            (fun S' ↦ obs (i + 1) S' - obs i S) =
          (q (i + 1) - q i) -
            (greedyKernel F S).expectationReal (fun S' ↦
              fixedPairAvailableCountReal S0 P S' -
                fixedPairAvailableCountReal S0 P S) := by
              have hfun : (fun S' ↦ obs (i + 1) S' - obs i S) =
                  (fun S' ↦ (q (i + 1) - q i) -
                    (fixedPairAvailableCountReal S0 P S' -
                      fixedPairAvailableCountReal S0 P S)) := by
                funext S'
                simp only [obs, fixedPairLowerDeviation]
                ring
              rw [hfun, FiniteLaw.expectationReal_sub,
                FiniteLaw.expectationReal_const]
        _ ≤ -(S.available.card : ℝ)⁻¹ *
              (((availableTrianglesContainingPair S P).card : ℝ) *
                  (3 * Delta : ℕ) + Kinc) -
            (greedyKernel F S).expectationReal (fun S' ↦
              fixedPairAvailableCountReal S0 P S' -
                fixedPairAvailableCountReal S0 P S) :=
          sub_le_sub_right (hqDrift i hi S hS hactive halive) _
        _ ≤ 0 := sub_nonpos.mpr
          (greedyKernel_expectationReal_fixedPair_increment_ge_aggregateCutoff
            hS (havailable i hi S hS hactive)
              (hpair i hi S hS hactive) (hinc i hi S hS hactive) hP)
    have hdrift : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S0 S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal (fun S' ↦
          if PairAlive P S' then obs (i + 1) S' - obs i S else 0) ≤ 0 := by
      intro i hi S hS hactive halive
      have hsupp := greedyKernel_supported_pairTrajectoryInvariant hS
      refine (FiniteLaw.expectationReal_mono_of_supported
        (greedyKernel F S) hsupp ?_).trans
          (hdriftFull i hi S hS hactive halive)
      intro S' hS'
      by_cases halive' : PairAlive P S'
      · simp [halive']
      · simp only [halive', if_false]
        change 0 ≤ fixedPairLowerDeviation q S0 P (i + 1) S' -
          fixedPairLowerDeviation q S0 P i S
        simp only [fixedPairLowerDeviation]
        rw [fixedPairAvailableCountReal_eq_current hS.2,
          fixedPairAvailableCountReal_eq_current hS'.2]
        have hempty : availableTrianglesContainingPair S' P = ∅ :=
          not_nonempty_iff_eq_empty.mp halive'
        rw [hempty, card_empty]
        have hdegree := hfloor i hi S hS hactive P hP halive
        have hdegreeReal : (delta : ℝ) ≤
            ((availableTrianglesContainingPair S P).card : ℝ) := by
          exact_mod_cast hdegree
        norm_num
        linarith [hqDeath i hi]
    have hsecond : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S0 S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal (fun S' ↦
          if PairAlive P S' then (obs (i + 1) S' - obs i S) ^ 2 else 0) ≤ v := by
      intro i hi S hS hactive halive
      let inc : GreedyStateOn V → ℝ := fun S' ↦
        fixedPairAvailableCountReal S0 P S' -
          fixedPairAvailableCountReal S0 P S
      let dq : ℝ := q (i + 1) - q i
      have hpoint : ∀ S',
          (if PairAlive P S' then (obs (i + 1) S' - obs i S) ^ 2 else 0) ≤
            2 * (if PairAlive P S' then (inc S') ^ 2 else 0) + 2 * dq ^ 2 := by
        intro S'
        by_cases halive' : PairAlive P S'
        · simp only [halive', if_true]
          have hobs : obs (i + 1) S' - obs i S = dq - inc S' := by
            simp only [obs, fixedPairLowerDeviation, inc, dq]
            ring
          rw [hobs]
          nlinarith [sq_nonneg (inc S' + dq)]
        · simp [halive', sq_nonneg dq]
      calc
        (greedyKernel F S).expectationReal (fun S' ↦
            if PairAlive P S' then (obs (i + 1) S' - obs i S) ^ 2 else 0) ≤
          (greedyKernel F S).expectationReal (fun S' ↦
            2 * (if PairAlive P S' then (inc S') ^ 2 else 0) +
              2 * dq ^ 2) := FiniteLaw.expectationReal_mono _ hpoint
        _ = 2 * (greedyKernel F S).expectationReal (fun S' ↦
              if PairAlive P S' then (inc S') ^ 2 else 0) + 2 * dq ^ 2 := by
            rw [FiniteLaw.expectationReal_add,
              FiniteLaw.expectationReal_const_mul,
              FiniteLaw.expectationReal_const]
        _ ≤ 2 * ((S.available.card : ℝ)⁻¹ *
              (((3 + Kpair : ℕ) : ℝ) *
                (((availableTrianglesContainingPair S P).card : ℝ) *
                  (3 * Delta : ℕ) + Kinc))) + 2 * dq ^ 2 := by
            have hsquare :=
              greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_mixedCutoffs
                hP hS (havailable i hi S hS hactive)
                  (hpair i hi S hS hactive) (hpairTwo i hi S hS hactive)
                    (hinc i hi S hS hactive)
            have hmul := mul_le_mul_of_nonneg_left hsquare
              (show (0 : ℝ) ≤ 2 by norm_num)
            exact add_le_add hmul le_rfl
        _ ≤ v := by simpa [dq] using hvariance i hi S hS hactive halive
    have htail :=
      FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
        (P := PairTrajectoryInvariant F S0) (alive := PairAlive P)
        n (fun _ ↦ greedyKernel F) active obs S0 theta (J : ℝ) a v
        (pairTrajectoryInvariant_initial hInv0) hAlive0 htheta
        (by positivity) hthetaJ hv
        (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
        (fun _i _hi S _hS hdead ↦ greedyKernel_supported_pairDead F S P hdead)
        (fun i hi S hS hactive halive S' hmass hS' halive' ↦
          hjumpAlive i hi S hS hactive halive S' hmass hS' halive')
        hdrift hsecond
    simpa [obs] using htail
  · have hzero := timedStoppedGreedy_probability_alive_eq_zero_of_initially_dead
        n F active S0 P hAlive0
        (fun z ↦ PairAlive P z.2 ∧
          a ≤ fixedPairLowerDeviation q S0 P z.1.1 z.2 -
            fixedPairLowerDeviation q S0 P 0 S0)
        (fun _z hz ↦ hz.1)
    rw [hzero]
    positivity

end

end Erdos207
