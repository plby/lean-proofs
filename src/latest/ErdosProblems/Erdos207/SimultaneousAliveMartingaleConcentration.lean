/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpScheduledPairTrajectories

/-!
# Simultaneous concentration for scheduled alive-pair martingales

This wrapper deliberately exposes only the three genuine martingale
obligations (jump, drift, and conditional second moment).  Consequently the
pair cutoffs used to prove those obligations may vary with the process
clock.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

theorem probability_timedStoppedGreedy_fixedPair_alive_observable_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : PairOn V)
    (obs : ℕ → GreedyStateOn V → ℝ)
    (J : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (hjump : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      ∀ S', 0 < (greedyKernel F S).mass S' →
        PairTrajectoryInvariant F S₀ S' → PairAlive P.1 S' →
          obs (i + 1) S' - obs i S ≤ (J : ℝ))
    (hdrift : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P.1 S' then obs (i + 1) S' - obs i S else 0) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P.1 S' then (obs (i + 1) S' - obs i S) ^ 2 else 0) ≤ v)
    (htheta : 0 < theta) (hthetaJ : theta * (J : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        active S₀).probability (fun z ↦
      PairAlive P.1 z.2 ∧ a ≤ obs z.1.1 z.2 - obs 0 S₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  by_cases hAlive₀ : PairAlive P.1 S₀
  · exact FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
      (P := PairTrajectoryInvariant F S₀) (alive := PairAlive P.1)
      n (fun _ ↦ greedyKernel F) active obs S₀ theta (J : ℝ) a v
      (pairTrajectoryInvariant_initial hInv₀) hAlive₀ htheta
      (by positivity) hthetaJ hv
      (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
      (fun _i _hi S _hS hdead ↦
        greedyKernel_supported_pairDead F S P.1 hdead)
      hjump hdrift hsecond
  · have hzero := timedStoppedGreedy_probability_alive_eq_zero_of_initially_dead
      n F active S₀ P.1 hAlive₀
      (fun z ↦ PairAlive P.1 z.2 ∧ a ≤ obs z.1.1 z.2 - obs 0 S₀)
      (fun _z hz ↦ hz.1)
    rw [hzero]
    positivity

/-- Union bound for an upper and a lower observable on every unordered
pair.  The observables may have different jump bounds but share a common
variance budget and exponential parameter. -/
theorem probability_timedStoppedGreedy_exists_pair_two_observables_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V)
    (upper lower : PairOn V → ℕ → GreedyStateOn V → ℝ)
    (JUpper JLower : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (hjumpUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      ∀ S', 0 < (greedyKernel F S).mass S' →
        PairTrajectoryInvariant F S₀ S' → PairAlive P.1 S' →
          upper P (i + 1) S' - upper P i S ≤ (JUpper : ℝ))
    (hdriftUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P.1 S' then
          upper P (i + 1) S' - upper P i S else 0) ≤ 0)
    (hsecondUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P.1 S' then
          (upper P (i + 1) S' - upper P i S) ^ 2 else 0) ≤ v)
    (hjumpLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      ∀ S', 0 < (greedyKernel F S).mass S' →
        PairTrajectoryInvariant F S₀ S' → PairAlive P.1 S' →
          lower P (i + 1) S' - lower P i S ≤ (JLower : ℝ))
    (hdriftLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P.1 S' then
          lower P (i + 1) S' - lower P i S else 0) ≤ 0)
    (hsecondLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
      (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P.1 S' then
          (lower P (i + 1) S' - lower P i S) ^ 2 else 0) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * (JLower : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        a ≤ upper P z.1.1 z.2 - upper P 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        a ≤ lower P z.1.1 z.2 - lower P 0 S₀)) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let upperBad : PairOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ PairAlive P.1 z.2 ∧
      a ≤ upper P z.1.1 z.2 - upper P 0 S₀
  let lowerBad : PairOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ PairAlive P.1 z.2 ∧
      a ≤ lower P z.1.1 z.2 - lower P 0 S₀
  let epsilon : ℝ := Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)
  have hupper : ∀ P : PairOn V, (L.probability (upperBad P) : ℝ) ≤ epsilon := by
    intro P
    exact probability_timedStoppedGreedy_fixedPair_alive_observable_le_exp
      n F active S₀ P (upper P) JUpper theta a v hInv₀
      (hjumpUpper P) (hdriftUpper P) (hsecondUpper P)
      htheta hthetaUpper hv
  have hlower : ∀ P : PairOn V, (L.probability (lowerBad P) : ℝ) ≤ epsilon := by
    intro P
    exact probability_timedStoppedGreedy_fixedPair_alive_observable_le_exp
      n F active S₀ P (lower P) JLower theta a v hInv₀
      (hjumpLower P) (hdriftLower P) (hsecondLower P)
      htheta hthetaLower hv
  have hpairBad : ∀ P : PairOn V,
      (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) ≤
        2 * epsilon := by
    intro P
    have hor := L.probability_or_le (upperBad P) (lowerBad P)
    have horReal :
        (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) ≤
          (L.probability (upperBad P) : ℝ) +
            (L.probability (lowerBad P) : ℝ) := by
      exact_mod_cast hor
    calc
      _ ≤ (L.probability (upperBad P) : ℝ) +
          (L.probability (lowerBad P) : ℝ) := horReal
      _ ≤ epsilon + epsilon := add_le_add (hupper P) (hlower P)
      _ = 2 * epsilon := by ring
  have hunion := L.probability_exists_le (univ : Finset (PairOn V))
    (fun P z ↦ upperBad P z ∨ lowerBad P z)
  have hunionRealRaw :
      (L.probability (fun z ↦ ∃ P : PairOn V, P ∈ (univ : Finset (PairOn V)) ∧
        (upperBad P z ∨ lowerBad P z)) : ℝ) ≤
        ∑ P : PairOn V,
          (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) := by
    exact_mod_cast hunion
  have hunionReal :
      (L.probability (fun z ↦ ∃ P : PairOn V,
        upperBad P z ∨ lowerBad P z) : ℝ) ≤
        ∑ P : PairOn V,
          (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) := by
    simpa only [mem_univ, true_and] using hunionRealRaw
  calc
    (L.probability (fun z ↦ ∃ P : PairOn V,
        upperBad P z ∨ lowerBad P z) : ℝ) ≤
      ∑ P : PairOn V,
        (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) := hunionReal
    _ ≤ ∑ _P : PairOn V, 2 * epsilon := by
      apply sum_le_sum
      intro P _hP
      exact hpairBad P
    _ = (Fintype.card (PairOn V) : ℝ) * (2 * epsilon) := by simp
    _ = _ := rfl

end

end Erdos207
