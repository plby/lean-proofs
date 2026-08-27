/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KilledKernelRestriction
import ErdosProblems.Erdos207.StoppedPairExtensionConcentration

/-!
# Stopping a pair trajectory when the pair is covered

An available pair-star is monotone decreasing.  Therefore, once it becomes
empty, a greedy trajectory can never return to the region where that pair is
still uncovered.  The killed-kernel comparison shows that adding this
pair-specific stop does not alter probabilities of events on states where the
pair-star remains nonempty.  This removes covered pairs from the lower-tail
union bound, exactly as in the KSSS differential-equation argument.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The ordinary greedy kernel cannot revive a dead pair. -/
theorem greedyKernel_supported_pairDead
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (P : Finset V) (hdead : ¬ PairAlive P S) :
    (greedyKernel F S).SupportedOn (fun S' ↦ ¬ PairAlive P S') := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with
    rfl | ⟨T, _hT, rfl⟩
  · exact hdead
  · intro halive
    exact hdead (halive.mono
      (availableTrianglesContainingPair_step_subset F S P T))

/-- The global timed stopped kernel also cannot revive a dead pair. -/
theorem timedStoppedGreedyKernel_supported_pairDead
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop) (P : Finset V)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hdead : ¬ PairAlive P z.2) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).SupportedOn
      (fun z' ↦ ¬ PairAlive P z'.2) := by
  classical
  unfold FiniteLaw.timedStoppedKernel
  split_ifs with hactive
  · exact (greedyKernel_supported_pairDead F z.2 P hdead).map
      (fun S' ↦ (FiniteLaw.advanceTime z.1 hactive.1, S'))
      (fun _S' hS' ↦ hS')
  · exact FiniteLaw.supportedOn_pure _ hdead

/-- Killing the global timed kernel outside the alive pair-star is exactly
the timed kernel whose active predicate includes pair-aliveness. -/
theorem killKernel_timedStoppedGreedy_eq_pairAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop) (P : Finset V) (i : ℕ) :
    FiniteLaw.killKernel
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ PairAlive P z.2)
      (fun _ z ↦ FiniteLaw.timedStoppedKernel n
        (fun _ ↦ greedyKernel F) active z) i =
      fun z ↦ FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F)
        (fun j S ↦ active j S ∧ PairAlive P S) z := by
  classical
  funext z
  unfold FiniteLaw.killKernel FiniteLaw.timedStoppedKernel
  by_cases halive : PairAlive P z.2
  · simp only [halive, if_true]
    by_cases hrun : z.1.1 < n ∧ active z.1.1 z.2
    · rw [dif_pos hrun]
      rw [dif_pos ⟨hrun.1, hrun.2, trivial⟩]
    · rw [dif_neg hrun]
      rw [dif_neg (fun h ↦ hrun ⟨h.1, h.2.1⟩)]
  · simp only [halive, if_false]
    rw [dif_neg (fun h ↦ h.2.2.elim)]

/-- The common process and the process additionally stopped when one pair is
covered assign equal probability to every event supported on states where
that pair is still alive. -/
theorem timedStoppedProcess_probability_eq_pairAliveStopped
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V)
    (Q : FiniteLaw.TimedState (GreedyStateOn V) n → Prop)
    (hQ : ∀ z, Q z → PairAlive P z.2) :
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀).probability Q =
    (FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F)
        (fun i S ↦ active i S ∧ PairAlive P S) S₀).probability Q := by
  classical
  let alive : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ PairAlive P z.2
  let Kglobal : ℕ → FiniteLaw.TimedState (GreedyStateOn V) n →
      FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) :=
    fun _ z ↦ FiniteLaw.timedStoppedKernel n
      (fun _ ↦ greedyKernel F) active z
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n :=
    (⟨0, by omega⟩, S₀)
  have hdead : ∀ i z, ¬ alive z →
      (Kglobal i z).SupportedOn (fun z' ↦ ¬ alive z') := by
    intro i z hz
    exact timedStoppedGreedyKernel_supported_pairDead
      n F active P z hz
  have hcompare :=
    FiniteLaw.evolveKernels_probability_killKernel_eq_of_subset_alive
      alive Kglobal (FiniteLaw.pure z₀) hdead n Q
      (fun z hz ↦ hQ z hz)
  have hkernel : FiniteLaw.killKernel alive Kglobal =
      fun _ z ↦ FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F)
        (fun i S ↦ active i S ∧ PairAlive P S) z := by
    funext i
    exact killKernel_timedStoppedGreedy_eq_pairAlive n F active P i
  rw [hkernel] at hcompare
  simpa [FiniteLaw.timedStoppedProcessLaw, Kglobal, z₀] using hcompare

/-- Upper-tail concentration on the common stopped law, restricted to states
where the fixed pair is still alive.  The pair-specific killed process lets the
upper target keep decreasing only while the pair is relevant. -/
theorem probability_timedStoppedGreedy_fixedPair_alive_upperDeviation_ge_le_exp
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
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * δ - 2 : ℕ)) ≤
          q (i + 1) - q i)
    (hvariance : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * Δ + K : ℕ) ^ 2)) +
            2 * (q (i + 1) - q i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaB : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ PairAlive P z.2 ∧
        a ≤ fixedPairUpperDeviation q S₀ P z.1.1 z.2 -
          fixedPairUpperDeviation q S₀ P 0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  let activeP : ℕ → GreedyStateOn V → Prop :=
    fun i S ↦ active i S ∧ PairAlive P S
  let bad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    a ≤ fixedPairUpperDeviation q S₀ P z.1.1 z.2 -
      fixedPairUpperDeviation q S₀ P 0 S₀
  let aliveBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ PairAlive P z.2 ∧ bad z
  have heq := timedStoppedProcess_probability_eq_pairAliveStopped
    n F active S₀ P aliveBad (fun z hz ↦ hz.1)
  have hmono :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        activeP S₀).probability aliveBad ≤
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        activeP S₀).probability bad := by
    apply FiniteLaw.probability_mono
    exact fun _z hz ↦ hz.2
  have hmonoReal :
      ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        activeP S₀).probability aliveBad : ℝ) ≤
      ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        activeP S₀).probability bad : ℝ) := by
    exact_mod_cast hmono
  rw [heq]
  refine hmonoReal.trans ?_
  exact probability_timedStoppedGreedy_fixedPair_upperDeviation_ge_le_exp
    n F activeP S₀ P q Δ δ K J theta a v hInv₀
    (fun i hi S hS hactive ↦ havailable i hi S hS hactive.1)
    (fun i hi S hS hactive ↦ hpair i hi S hS hactive.1)
    (fun i hi S hS hactive ↦ htwo i hi S hS hactive.1)
    (fun i hi S hS hactive ↦ hfloor i hi S hS hactive.1)
    hδ hqLower hqUpper
    (fun i hi S hS hactive ↦ hqDrift i hi S hS hactive.1 hactive.2)
    (fun i hi S hS hactive ↦ hvariance i hi S hS hactive.1 hactive.2)
    htheta hthetaB hv

/-- Compatibility alias for the survival-weighted lower-tail theorem. -/
theorem probability_timedStoppedGreedy_fixedPair_alive_lowerDeviation_ge_le_exp
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
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) :=
  probability_timedStoppedGreedy_fixedPair_lowerDeviation_ge_le_exp
    n F active S₀ P hP q Δ δ K J theta a v hInv₀ havailable
    hpair htwo hfloor hqDeath hqUpper hjumpAlive hqDrift hvariance
    htheta hthetaJ hv

end

end Erdos207
