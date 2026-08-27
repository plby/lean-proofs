/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairExtensionTrajectory
import ErdosProblems.Erdos207.FiniteStoppedKernel

/-!
# Stopped concentration for pair-extension trajectories

For a fixed pair, compare its surviving extension count with a deterministic
target trajectory.  In an active region with pair-codegree, two-away, and
pair-floor bounds, the fixed count has the required drift, jump, and second
moment estimates.  The stopped finite-kernel exponential inequality therefore
gives upper and lower tail estimates without assuming any independence.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The fixed-pair count centered at a deterministic target trajectory. -/
def fixedPairUpperDeviation
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ → ℝ) (S₀ : GreedyStateOn V) (P : Finset V)
    (i : ℕ) (S : GreedyStateOn V) : ℝ :=
  fixedPairAvailableCountReal S₀ P S - q i

/-- Upper-tail concentration for one fixed pair-extension count.  The target
increment is required to lie inside the same deletion envelope as the random
increment, to dominate the negative three-pair drift, and to satisfy the
displayed conditional-variance budget. -/
theorem probability_timedStoppedGreedy_fixedPair_upperDeviation_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V)
    (q : ℕ → ℝ) (Δ δ K J : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (havailable : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → S.available.Nonempty)
    (hpair : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairCutoff Δ S)
    (htwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasTwoAwayCutoff F K S)
    (hfloor : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairFloor δ S)
    (hδ : 1 ≤ δ)
    (hqLower : ∀ i, i < n →
      -(J : ℝ) ≤ q (i + 1) - q i)
    (hqUpper : ∀ i, i < n → q (i + 1) - q i ≤ 0)
    (hqDrift : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * δ - 2 : ℕ)) ≤
          q (i + 1) - q i)
    (hvariance : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * Δ + K : ℕ) ^ 2)) +
            2 * (q (i + 1) - q i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaB : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ a ≤ fixedPairUpperDeviation q S₀ P z.1.1 z.2 -
        fixedPairUpperDeviation q S₀ P 0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  let obs : ℕ → GreedyStateOn V → ℝ :=
    fun i S ↦ fixedPairUpperDeviation q S₀ P i S
  have hjump : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
      ∀ S', 0 < (greedyKernel F S).mass S' →
        PairTrajectoryInvariant F S₀ S' →
          obs (i + 1) S' - obs i S ≤ (J : ℝ) := by
    intro i hi S hS hactive S' hmass _hS'
    have hinterval := greedyKernel_fixedPair_increment_mem_interval
      hS (havailable i hi S hS hactive) (hpair i hi S hS hactive)
        (htwo i hi S hS hactive) hmass (P := P)
    have hqlo := hqLower i hi
    have hobs : obs (i + 1) S' - obs i S =
        (fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S) -
            (q (i + 1) - q i) := by
      simp only [obs, fixedPairUpperDeviation]
      ring
    rw [hobs]
    linarith [hinterval.2]
  have hdrift : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
      (greedyKernel F S).expectationReal
        (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0 := by
    intro i hi S hS hactive
    have hA := havailable i hi S hS hactive
    calc
      (greedyKernel F S).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) =
        (greedyKernel F S).expectationReal
            (fun S' ↦ fixedPairAvailableCountReal S₀ P S' -
              fixedPairAvailableCountReal S₀ P S) -
          (q (i + 1) - q i) := by
            have hfun : (fun S' ↦ obs (i + 1) S' - obs i S) =
                (fun S' ↦
                  (fixedPairAvailableCountReal S₀ P S' -
                    fixedPairAvailableCountReal S₀ P S) -
                    (q (i + 1) - q i)) := by
              funext S'
              simp only [obs, fixedPairUpperDeviation]
              ring
            rw [hfun, FiniteLaw.expectationReal_sub,
              FiniteLaw.expectationReal_const]
      _ ≤ -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * δ - 2 : ℕ)) - (q (i + 1) - q i) :=
        sub_le_sub_right
          (greedyKernel_expectationReal_fixedPair_increment_le_threeFloor
            hS hA (hfloor i hi S hS hactive) hδ) _
      _ ≤ 0 := sub_nonpos.mpr (hqDrift i hi S hS hactive)
  have hsecond : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
      (greedyKernel F S).expectationReal
        (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ v := by
    intro i hi S hS hactive
    let inc : GreedyStateOn V → ℝ := fun S' ↦
      fixedPairAvailableCountReal S₀ P S' -
        fixedPairAvailableCountReal S₀ P S
    let dq : ℝ := q (i + 1) - q i
    have hpoint : ∀ S', (obs (i + 1) S' - obs i S) ^ 2 ≤
        2 * (inc S') ^ 2 + 2 * dq ^ 2 := by
      intro S'
      have hobs : obs (i + 1) S' - obs i S = inc S' - dq := by
        simp only [obs, fixedPairUpperDeviation, inc, dq]
        ring
      rw [hobs]
      nlinarith [sq_nonneg (inc S' + dq)]
    calc
      (greedyKernel F S).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤
        (greedyKernel F S).expectationReal
          (fun S' ↦ 2 * (inc S') ^ 2 + 2 * dq ^ 2) :=
            FiniteLaw.expectationReal_mono _ hpoint
      _ = 2 * (greedyKernel F S).expectationReal
            (fun S' ↦ (inc S') ^ 2) + 2 * dq ^ 2 := by
          rw [FiniteLaw.expectationReal_add,
            FiniteLaw.expectationReal_const_mul,
            FiniteLaw.expectationReal_const]
      _ ≤ 2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * Δ + K : ℕ) ^ 2)) + 2 * dq ^ 2 := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left
            · exact greedyKernel_expectationReal_fixedPair_sqIncrement_le_cutoffs
                hS (havailable i hi S hS hactive)
                  (hpair i hi S hS hactive) (htwo i hi S hS hactive)
            · norm_num
          · exact le_rfl
      _ ≤ v := by
          simpa [dq] using hvariance i hi S hS hactive
  have htail := FiniteLaw.probability_timedStoppedProcess_deviation_ge_le_exp
    (P := PairTrajectoryInvariant F S₀) n (fun _ ↦ greedyKernel F)
    active obs S₀ theta (J : ℝ) a v
    (pairTrajectoryInvariant_initial hInv₀) htheta (by positivity)
    hthetaB hv
    (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
    hjump hdrift hsecond
  simpa [obs] using htail

/-- The target-minus-count deviation used for the lower tail. -/
def fixedPairLowerDeviation
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ → ℝ) (S₀ : GreedyStateOn V) (P : Finset V)
    (i : ℕ) (S : GreedyStateOn V) : ℝ :=
  q i - fixedPairAvailableCountReal S₀ P S

/-- Lower-tail concentration for one fixed pair-extension count, restricted
to paths on which the pair is still alive.  Dead outcomes have zero
exponential weight, so their catastrophic final deletion does not constrain
the jump parameter. -/
theorem probability_timedStoppedGreedy_fixedPair_lowerDeviation_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V) (hP : P.card = 2)
    (q : ℕ → ℝ) (Δ δ K J : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (havailable : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → S.available.Nonempty)
    (hpair : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairCutoff Δ S)
    (htwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasTwoAwayCutoff F K S)
    (hfloor : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairFloor δ S)
    (hqDeath : ∀ i, i < n → -(δ : ℝ) ≤ q (i + 1) - q i)
    (hqUpper : ∀ i, i < n → q (i + 1) - q i ≤ 0)
    (hjumpAlive : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
      ∀ S', 0 < (greedyKernel F S).mass S' →
        PairTrajectoryInvariant F S₀ S' → PairAlive P S' →
          fixedPairLowerDeviation q S₀ P (i + 1) S' -
            fixedPairLowerDeviation q S₀ P i S ≤ (J : ℝ))
    (hqDrift : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        q (i + 1) - q i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * Δ + K : ℕ)))
    (hvariance : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * Δ + K : ℕ) ^ 2)) +
            2 * (q (i + 1) - q i) ^ 2 ≤ v)
    (htheta : 0 < theta) (hthetaJ : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ PairAlive P z.2 ∧
        a ≤ fixedPairLowerDeviation q S₀ P z.1.1 z.2 -
          fixedPairLowerDeviation q S₀ P 0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  let obs : ℕ → GreedyStateOn V → ℝ :=
    fun i S ↦ fixedPairLowerDeviation q S₀ P i S
  by_cases hAlive₀ : PairAlive P S₀
  · have hdriftFull : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0 := by
      intro i hi S hS hactive hAlive
      have hA := havailable i hi S hS hactive
      calc
        (greedyKernel F S).expectationReal
            (fun S' ↦ obs (i + 1) S' - obs i S) =
          (q (i + 1) - q i) -
            (greedyKernel F S).expectationReal
              (fun S' ↦ fixedPairAvailableCountReal S₀ P S' -
                fixedPairAvailableCountReal S₀ P S) := by
              have hfun : (fun S' ↦ obs (i + 1) S' - obs i S) =
                  (fun S' ↦ (q (i + 1) - q i) -
                    (fixedPairAvailableCountReal S₀ P S' -
                      fixedPairAvailableCountReal S₀ P S)) := by
                funext S'
                simp only [obs, fixedPairLowerDeviation]
                ring
              rw [hfun, FiniteLaw.expectationReal_sub,
                FiniteLaw.expectationReal_const]
        _ ≤ -(S.available.card : ℝ)⁻¹ *
              (((availableTrianglesContainingPair S P).card : ℝ) *
                (3 * Δ + K : ℕ)) -
            (greedyKernel F S).expectationReal
              (fun S' ↦ fixedPairAvailableCountReal S₀ P S' -
                fixedPairAvailableCountReal S₀ P S) :=
          sub_le_sub_right (hqDrift i hi S hS hactive hAlive) _
        _ ≤ 0 := sub_nonpos.mpr
          (greedyKernel_expectationReal_fixedPair_increment_ge_cutoffs
            hS hA (hpair i hi S hS hactive) (htwo i hi S hS hactive))
    have hsecondFull : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ v := by
      intro i hi S hS hactive hAlive
      let inc : GreedyStateOn V → ℝ := fun S' ↦
        fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S
      let dq : ℝ := q (i + 1) - q i
      have hpoint : ∀ S', (obs (i + 1) S' - obs i S) ^ 2 ≤
          2 * (inc S') ^ 2 + 2 * dq ^ 2 := by
        intro S'
        have hobs : obs (i + 1) S' - obs i S = dq - inc S' := by
          simp only [obs, fixedPairLowerDeviation, inc, dq]
          ring
        rw [hobs]
        nlinarith [sq_nonneg (inc S' + dq)]
      calc
        (greedyKernel F S).expectationReal
            (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤
          (greedyKernel F S).expectationReal
            (fun S' ↦ 2 * (inc S') ^ 2 + 2 * dq ^ 2) :=
              FiniteLaw.expectationReal_mono _ hpoint
        _ = 2 * (greedyKernel F S).expectationReal
              (fun S' ↦ (inc S') ^ 2) + 2 * dq ^ 2 := by
            rw [FiniteLaw.expectationReal_add,
              FiniteLaw.expectationReal_const_mul,
              FiniteLaw.expectationReal_const]
        _ ≤ 2 * ((S.available.card : ℝ)⁻¹ *
              (((availableTrianglesContainingPair S P).card : ℝ) *
                (3 * Δ + K : ℕ) ^ 2)) + 2 * dq ^ 2 := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left
              · exact greedyKernel_expectationReal_fixedPair_sqIncrement_le_cutoffs
                  hS (havailable i hi S hS hactive)
                    (hpair i hi S hS hactive) (htwo i hi S hS hactive)
              · norm_num
            · exact le_rfl
        _ ≤ v := by simpa [dq] using hvariance i hi S hS hactive hAlive
    have htail :=
      FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
        (P := PairTrajectoryInvariant F S₀) (alive := PairAlive P)
        n (fun _ ↦ greedyKernel F) active obs S₀ theta (J : ℝ) a v
        (pairTrajectoryInvariant_initial hInv₀) hAlive₀ htheta
        (by positivity) hthetaJ hv
        (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
        (fun _i _hi S _hS hdead ↦ by
          intro S' hmass halive
          rcases greedyKernel_supported_step_or_self F S S' hmass with
            rfl | ⟨T, _hT, rfl⟩
          · exact hdead halive
          · exact hdead (halive.mono
              (availableTrianglesContainingPair_step_subset F S P T)))
        (fun i hi S hS hactive hAlive S' hmass hS' hAlive' ↦
          hjumpAlive i hi S hS hactive hAlive S' hmass hS' hAlive')
        (fun i hi S hS hactive hAlive ↦ by
          have hsupp := greedyKernel_supported_pairTrajectoryInvariant hS
          refine (FiniteLaw.expectationReal_mono_of_supported
            (greedyKernel F S) hsupp ?_).trans
              (hdriftFull i hi S hS hactive hAlive)
          intro S' hS'
          by_cases hAlive' : PairAlive P S'
          · simp [hAlive']
          · simp only [hAlive', if_false]
            change 0 ≤ fixedPairLowerDeviation q S₀ P (i + 1) S' -
              fixedPairLowerDeviation q S₀ P i S
            simp only [fixedPairLowerDeviation]
            rw [fixedPairAvailableCountReal_eq_current hS.2,
              fixedPairAvailableCountReal_eq_current hS'.2]
            have hempty : availableTrianglesContainingPair S' P = ∅ :=
              not_nonempty_iff_eq_empty.mp hAlive'
            rw [hempty, card_empty]
            have hdegree := hfloor i hi S hS hactive P hP hAlive
            have hdegreeReal : (δ : ℝ) ≤
                ((availableTrianglesContainingPair S P).card : ℝ) := by
              exact_mod_cast hdegree
            norm_num
            linarith [hqDeath i hi])
        (fun i hi S hS hactive _hAlive ↦ by
          refine (FiniteLaw.expectationReal_mono (greedyKernel F S) ?_).trans
            (hsecondFull i hi S hS hactive _hAlive)
          intro S'
          by_cases hAlive' : PairAlive P S'
          · simp [hAlive']
          · simp [hAlive', sq_nonneg (obs (i + 1) S' - obs i S)])
    simpa [obs] using htail
  · have hdeadSupport :
        (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
          active S₀).SupportedOn (fun z ↦ ¬ PairAlive P z.2) := by
      exact FiniteLaw.timedStoppedProcessLaw_supported n
        (P := fun S ↦ ¬ PairAlive P S)
        (fun _ ↦ greedyKernel F) active S₀ hAlive₀
        (fun _i _hi S hdead ↦ by
          intro S' hmass halive
          rcases greedyKernel_supported_step_or_self F S S' hmass with
            rfl | ⟨T, _hT, rfl⟩
          · exact hdead halive
          · exact hdead (halive.mono
              (availableTrianglesContainingPair_step_subset F S P T)))
    have hzero : (FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ PairAlive P z.2 ∧
          a ≤ fixedPairLowerDeviation q S₀ P z.1.1 z.2 -
            fixedPairLowerDeviation q S₀ P 0 S₀) = 0 := by
      unfold FiniteLaw.probability
      apply Finset.sum_eq_zero
      intro z _hz
      by_cases hzbad : PairAlive P z.2 ∧
          a ≤ fixedPairLowerDeviation q S₀ P z.1.1 z.2 -
            fixedPairLowerDeviation q S₀ P 0 S₀
      · have hmass : (FiniteLaw.timedStoppedProcessLaw n
            (fun _ ↦ greedyKernel F) active S₀).mass z = 0 := by
          apply le_antisymm
          · apply not_lt.mp
            intro hpos
            exact (hdeadSupport z hpos hzbad.1).elim
          · exact zero_le
        simp [hzbad, hmass]
      · simp [hzbad]
    rw [hzero]
    positivity

end

end Erdos207
