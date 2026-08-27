/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AlivePairVariance
import ErdosProblems.Erdos207.PairAliveStoppedProcess

/-!
# Sharp survival-weighted pair concentration

Both one-sided pair-star estimates below discard the transition which covers
the tracked pair.  Consequently their conditional second moment uses the
linear envelope `(3+K)(3Δ+K)d/|A|`, rather than the square of the global
deletion bound.  For the upper tail we also subtract the at-most-`d²`
incidences contributed by pair-covering selectors from the three-pair drift.
-/

namespace Erdos207

open Finset

noncomputable section

/-- If a pair is initially dead, every event requiring it to be alive at the
end of a stopped greedy trajectory has probability zero. -/
theorem timedStoppedGreedy_probability_alive_eq_zero_of_initially_dead
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V)
    (hdead₀ : ¬ PairAlive P S₀)
    (Q : FiniteLaw.TimedState (GreedyStateOn V) n → Prop)
    (hQ : ∀ z, Q z → PairAlive P z.2) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀).probability Q = 0 := by
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hsupp : L.SupportedOn (fun z ↦ ¬ PairAlive P z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported n
      (P := fun S ↦ ¬ PairAlive P S)
      (fun _ ↦ greedyKernel F) active S₀ hdead₀
      (fun _i _hi S hdead ↦ greedyKernel_supported_pairDead F S P hdead)
  apply le_antisymm
  · rw [← L.probability_false]
    exact L.probability_mono_of_supported hsupp
      (fun z hzdead hzQ ↦ (hzdead (hQ z hzQ)).elim)
  · exact zero_le

/-- Upper-tail concentration for one pair with the survival-masked variance
and the surviving-selector drift `d(3δ-2-Δ)/|A|`. -/
theorem probability_timedStoppedGreedy_fixedPair_sharp_alive_upper_le_exp_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V) (hP : P.card = 2)
    (q : ℕ → ℝ) (Δ δ Kpair Kglobal J : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (havailable : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → S.available.Nonempty)
    (hpair : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairCutoff Δ S)
    (hpairTwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasPairTwoAwayCutoff F Kpair S)
    (htwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasTwoAwayCutoff F Kglobal S)
    (hfloor : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairFloor δ S)
    (hδ : 1 ≤ δ) (hsmall : 3 + Kpair < δ)
    (hqLower : ∀ i, i < n → -(J : ℝ) ≤ q (i + 1) - q i)
    (hqUpper : ∀ i, i < n → q (i + 1) - q i ≤ 0)
    (hqDrift : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          q (i + 1) - q i)
    (hvariance : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (q (i + 1) - q i) ^ 2 ≤ v)
    (htheta : 0 < theta) (hthetaJ : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ PairAlive P z.2 ∧
        a ≤ fixedPairUpperDeviation q S₀ P z.1.1 z.2 -
          fixedPairUpperDeviation q S₀ P 0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  let obs : ℕ → GreedyStateOn V → ℝ :=
    fun i S ↦ fixedPairUpperDeviation q S₀ P i S
  by_cases hAlive₀ : PairAlive P S₀
  · have hjump : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        ∀ S', 0 < (greedyKernel F S).mass S' →
          PairTrajectoryInvariant F S₀ S' → PairAlive P S' →
            obs (i + 1) S' - obs i S ≤ (J : ℝ) := by
      intro i hi S hS hactive _halive S' hmass _hS' _halive'
      have hinc := (greedyKernel_fixedPair_increment_mem_interval
        hS (havailable i hi S hS hactive) (hpair i hi S hS hactive)
          (htwo i hi S hS hactive) hmass (P := P)).2
      have hdq := hqLower i hi
      simp only [obs, fixedPairUpperDeviation]
      linarith
    have hdrift : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal (fun S' ↦
          if PairAlive P S' then obs (i + 1) S' - obs i S else 0) ≤ 0 := by
      intro i hi S hS hactive halive
      have hrewrite : (fun S' ↦
          if PairAlive P S' then obs (i + 1) S' - obs i S else 0) =
          (fun S' ↦ if PairAlive P S' then
            (fixedPairAvailableCountReal S₀ P S' -
              fixedPairAvailableCountReal S₀ P S) -
                (q (i + 1) - q i) else 0) := by
        funext S'
        simp only [obs, fixedPairUpperDeviation]
        split <;> ring
      rw [hrewrite]
      exact greedyKernel_expectationReal_fixedPairUpperIncrement_if_alive_le_zero_of_pairCutoff
        hP hS (havailable i hi S hS hactive) (hpair i hi S hS hactive)
        (hpairTwo i hi S hS hactive) (hfloor i hi S hS hactive) hδ halive
        hsmall (q (i + 1) - q i) (hqUpper i hi)
        (hqDrift i hi S hS hactive halive)
    have hsecond : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal (fun S' ↦
          if PairAlive P S' then (obs (i + 1) S' - obs i S) ^ 2 else 0) ≤ v := by
      intro i hi S hS hactive _halive
      let inc : GreedyStateOn V → ℝ := fun S' ↦
        fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S
      let dq : ℝ := q (i + 1) - q i
      have hpoint : ∀ S',
          (if PairAlive P S' then (obs (i + 1) S' - obs i S) ^ 2 else 0) ≤
            2 * (if PairAlive P S' then (inc S') ^ 2 else 0) + 2 * dq ^ 2 := by
        intro S'
        by_cases halive' : PairAlive P S'
        · simp only [halive', if_true]
          have hobs : obs (i + 1) S' - obs i S = inc S' - dq := by
            simp only [obs, fixedPairUpperDeviation, inc, dq]
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
              (((availableTrianglesContainingPair S P).card : ℝ) *
                (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
              2 * dq ^ 2 := by
            have hsquare :=
              greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_of_pairCutoff
                hP hS (havailable i hi S hS hactive)
                  (hpair i hi S hS hactive) (hpairTwo i hi S hS hactive)
                    (htwo i hi S hS hactive)
            have hmul : 2 * (greedyKernel F S).expectationReal (fun S' ↦
                  if PairAlive P S' then (inc S') ^ 2 else 0) ≤
                2 * ((S.available.card : ℝ)⁻¹ *
                  (((availableTrianglesContainingPair S P).card : ℝ) *
                    (((3 + Kpair : ℕ) : ℝ) *
                      ((3 * Δ + Kglobal : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hsquare (by norm_num)
            exact add_le_add hmul le_rfl
        _ ≤ v := by simpa [dq] using hvariance i hi S hS hactive _halive
    have htail :=
      FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
        (P := PairTrajectoryInvariant F S₀) (alive := PairAlive P)
        n (fun _ ↦ greedyKernel F) active obs S₀ theta (J : ℝ) a v
        (pairTrajectoryInvariant_initial hInv₀) hAlive₀ htheta
        (by positivity) hthetaJ hv
        (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
        (fun _i _hi S _hS hdead ↦ greedyKernel_supported_pairDead F S P hdead)
        hjump hdrift hsecond
    simpa [obs] using htail
  · have hzero := timedStoppedGreedy_probability_alive_eq_zero_of_initially_dead
        n F active S₀ P hAlive₀
        (fun z ↦ PairAlive P z.2 ∧
          a ≤ fixedPairUpperDeviation q S₀ P z.1.1 z.2 -
            fixedPairUpperDeviation q S₀ P 0 S₀)
        (fun _z hz ↦ hz.1)
    rw [hzero]
    positivity

/-- Compatibility form using one cutoff for both global and pair-local
two-away counts. -/
theorem probability_timedStoppedGreedy_fixedPair_sharp_alive_upper_le_exp
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
    (hδ : 1 ≤ δ) (hsmall : 3 + K < δ)
    (hqLower : ∀ i, i < n → -(J : ℝ) ≤ q (i + 1) - q i)
    (hqUpper : ∀ i, i < n → q (i + 1) - q i ≤ 0)
    (hqDrift : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          q (i + 1) - q i)
    (hvariance : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)))) +
            2 * (q (i + 1) - q i) ^ 2 ≤ v)
    (htheta : 0 < theta) (hthetaJ : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ PairAlive P z.2 ∧
        a ≤ fixedPairUpperDeviation q S₀ P z.1.1 z.2 -
          fixedPairUpperDeviation q S₀ P 0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  exact probability_timedStoppedGreedy_fixedPair_sharp_alive_upper_le_exp_of_pairCutoff
    n F active S₀ P hP q Δ δ K K J theta a v hInv₀ havailable hpair
      (fun i hi S hS ha ↦ (htwo i hi S hS ha).hasPairTwoAwayCutoff)
      htwo hfloor hδ hsmall hqLower hqUpper hqDrift hvariance
      htheta hthetaJ hv

/-- Lower-tail concentration for one pair with the same survival-masked
linear variance envelope. -/
theorem probability_timedStoppedGreedy_fixedPair_sharp_alive_lower_le_exp_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V) (hP : P.card = 2)
    (q : ℕ → ℝ) (Δ δ Kpair Kglobal J : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (havailable : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → S.available.Nonempty)
    (hpair : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairCutoff Δ S)
    (hpairTwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasPairTwoAwayCutoff F Kpair S)
    (htwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasTwoAwayCutoff F Kglobal S)
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
              (3 * Δ + Kglobal : ℕ)))
    (hvariance : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
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
      intro i hi S hS hactive halive
      calc
        (greedyKernel F S).expectationReal
            (fun S' ↦ obs (i + 1) S' - obs i S) =
          (q (i + 1) - q i) -
            (greedyKernel F S).expectationReal (fun S' ↦
              fixedPairAvailableCountReal S₀ P S' -
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
                (3 * Δ + Kglobal : ℕ)) -
            (greedyKernel F S).expectationReal (fun S' ↦
              fixedPairAvailableCountReal S₀ P S' -
                fixedPairAvailableCountReal S₀ P S) :=
          sub_le_sub_right (hqDrift i hi S hS hactive halive) _
        _ ≤ 0 := sub_nonpos.mpr
          (greedyKernel_expectationReal_fixedPair_increment_ge_cutoffs
            hS (havailable i hi S hS hactive)
              (hpair i hi S hS hactive) (htwo i hi S hS hactive))
    have hdrift : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
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
        change 0 ≤ fixedPairLowerDeviation q S₀ P (i + 1) S' -
          fixedPairLowerDeviation q S₀ P i S
        simp only [fixedPairLowerDeviation]
        rw [fixedPairAvailableCountReal_eq_current hS.2,
          fixedPairAvailableCountReal_eq_current hS'.2]
        have hempty : availableTrianglesContainingPair S' P = ∅ :=
          not_nonempty_iff_eq_empty.mp halive'
        rw [hempty, card_empty]
        have hdegree := hfloor i hi S hS hactive P hP halive
        have hdegreeReal : (δ : ℝ) ≤
            ((availableTrianglesContainingPair S P).card : ℝ) := by
          exact_mod_cast hdegree
        norm_num
        linarith [hqDeath i hi]
    have hsecond : ∀ i, i < n → ∀ S,
        PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        (greedyKernel F S).expectationReal (fun S' ↦
          if PairAlive P S' then (obs (i + 1) S' - obs i S) ^ 2 else 0) ≤ v := by
      intro i hi S hS hactive halive
      let inc : GreedyStateOn V → ℝ := fun S' ↦
        fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S
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
              (((availableTrianglesContainingPair S P).card : ℝ) *
                (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
              2 * dq ^ 2 := by
            have hsquare :=
              greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_of_pairCutoff
                hP hS (havailable i hi S hS hactive)
                  (hpair i hi S hS hactive) (hpairTwo i hi S hS hactive)
                    (htwo i hi S hS hactive)
            have hmul : 2 * (greedyKernel F S).expectationReal (fun S' ↦
                  if PairAlive P S' then (inc S') ^ 2 else 0) ≤
                2 * ((S.available.card : ℝ)⁻¹ *
                  (((availableTrianglesContainingPair S P).card : ℝ) *
                    (((3 + Kpair : ℕ) : ℝ) *
                      ((3 * Δ + Kglobal : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hsquare (by norm_num)
            exact add_le_add hmul le_rfl
        _ ≤ v := by simpa [dq] using hvariance i hi S hS hactive halive
    have htail :=
      FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
        (P := PairTrajectoryInvariant F S₀) (alive := PairAlive P)
        n (fun _ ↦ greedyKernel F) active obs S₀ theta (J : ℝ) a v
        (pairTrajectoryInvariant_initial hInv₀) hAlive₀ htheta
        (by positivity) hthetaJ hv
        (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
        (fun _i _hi S _hS hdead ↦ greedyKernel_supported_pairDead F S P hdead)
        (fun i hi S hS hactive halive S' hmass hS' halive' ↦
          hjumpAlive i hi S hS hactive halive S' hmass hS' halive')
        hdrift hsecond
    simpa [obs] using htail
  · have hzero := timedStoppedGreedy_probability_alive_eq_zero_of_initially_dead
        n F active S₀ P hAlive₀
        (fun z ↦ PairAlive P z.2 ∧
          a ≤ fixedPairLowerDeviation q S₀ P z.1.1 z.2 -
            fixedPairLowerDeviation q S₀ P 0 S₀)
        (fun _z hz ↦ hz.1)
    rw [hzero]
    positivity

/-- Compatibility form of the sharp lower tail using one global/local
two-away cutoff. -/
theorem probability_timedStoppedGreedy_fixedPair_sharp_alive_lower_le_exp
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
              (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)))) +
            2 * (q (i + 1) - q i) ^ 2 ≤ v)
    (htheta : 0 < theta) (hthetaJ : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ PairAlive P z.2 ∧
        a ≤ fixedPairLowerDeviation q S₀ P z.1.1 z.2 -
          fixedPairLowerDeviation q S₀ P 0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  exact probability_timedStoppedGreedy_fixedPair_sharp_alive_lower_le_exp_of_pairCutoff
    n F active S₀ P hP q Δ δ K K J theta a v hInv₀ havailable hpair
      (fun i hi S hS ha ↦ (htwo i hi S hS ha).hasPairTwoAwayCutoff)
      htwo hfloor hqDeath hqUpper hjumpAlive hqDrift hvariance
      htheta hthetaJ hv

end

end Erdos207
