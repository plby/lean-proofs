/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborKernelBounds
import ErdosProblems.Erdos207.NeighborConcentrationOptimization
import ErdosProblems.Erdos207.NeighborPowerScale

/-! # Geometric auxiliary degree tails for the actual refined stopped law -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSPowerParameters.uncovered_neighbor_power_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (hInv₀ : GreedyInvariant F S₀)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hcoefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t)
    (U : Finset V) (v : V) (sigma : ℝ) (hsigma : |sigma| = 1)
    (hsize : (t : ℝ) ^ (2 * ksssPowerErrorExponent b B + 2 * b + 3) ≤ (U.card : ℝ))
    (hband : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      |((uncoveredNeighbors Q₀ U v S).card : ℝ) - uncoveredNeighborTarget E U.card i| ≤
        uncoveredNeighborErrorEnvelope E U.card t (ksssPowerErrorExponent b B) B i) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability (fun w ↦
      8 * (U.card : ℝ) * t / (t : ℝ) ^ ksssPowerErrorExponent b B ≤
        uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma w.1.1 w.2 -
          uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma 0 S₀) : ℝ) ≤
      (1 / 2 : ℝ) ^ t := by
  classical
  let N : ℝ := Fintype.card V
  let M : ℝ := U.card
  let s := ksssPowerErrorExponent b B
  let obs := fun i : ℕ ↦ uncoveredNeighborCenteredObservable Q₀ U v E t s B sigma (i : ℝ)
  let variance := 64 * M / N ^ 2 * (t : ℝ) ^ (2 * b)
  let margin := 8 * M * t / (t : ℝ) ^ s
  have hNpos : 0 < N := by
    have hN1 : (1 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast P.ambient_pos
    linarith
  have htR : (32 : ℝ) ≤ t := by exact_mod_cast P.scale_large
  have htpos : (0 : ℝ) < t := by linarith
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hMN : M ≤ N := by dsimp only [M, N]; exact_mod_cast card_le_univ U
  have hvariance0 : 0 ≤ variance := by dsimp only [variance]; positivity
  have hsteps : (n : ℝ) ≤ N ^ 2 := by dsimp only [N]; exact_mod_cast P.horizon
  have hscale : (t : ℝ) ^ ksssPowerDenominatorExponent q b B k Rmin ≤ N := by
    dsimp only [N]
    exact_mod_cast P.power_scale
  have hgap : 2 * b + 1 ≤ ksssPowerDenominatorExponent q b B k Rmin := by
    dsimp only [ksssPowerDenominatorExponent]
    omega
  have hpoint : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      (greedyKernel F S).SupportedOn (fun S' ↦ |obs (i + 1) S' - obs i S| ≤ 3) ∧
      (greedyKernel F S).expectationReal (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0 ∧
      (greedyKernel F S).expectationReal (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ variance := by
    intro i hi S hS ha
    have hs := hactive i S ha
    have hscalar := P.scalar_bounds i (Nat.cast_nonneg _) hs.2.2.2
    have hsmall := neighbor_clock_small_of_power_scale N M t (E * ksssEdgeDensity E i)
      (ksssPowerDenominatorExponent q b B k Rmin) b hNpos hMN htR hscale hgap hscalar.clock_lower
    have hkernel := hs.2.1.uncovered_neighbor_jump_variance hs.1 hscalar P.edge_pos hNpos htpos
      (Nat.cast_nonneg _) hs.2.2.2 hcoefficient U v sigma hsigma hsmall
    have hdrift := hs.2.1.uncovered_neighbor_centered_drift hs.1 hscalar P.edge_pos hNpos htpos
      (Nat.cast_nonneg _) P.coefficient_nonneg P.coefficient_bound hratio P.coefficient_budget.poisson
      U v sigma hsigma (hband i hi S hS ha)
    have hvarBound : 64 * M / (E * ksssEdgeDensity E i) ≤ variance := by
      calc
        _ ≤ 64 * M / (N ^ 2 / (t : ℝ) ^ (2 * b)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hscalar.clock_lower
        _ = _ := by dsimp only [variance]; field_simp
    exact ⟨by simpa only [obs, Nat.cast_add, Nat.cast_one] using hkernel.1,
      by simpa only [obs, Nat.cast_add, Nat.cast_one] using hdrift,
      by simpa only [obs, Nat.cast_add, Nat.cast_one] using hkernel.2.trans hvarBound⟩
  have hbudget := neighbor_concentration_power_budget N M t margin n variance s b hNpos (by linarith)
    hsize hsteps hvariance0 le_rfl le_rfl
  have htail := FiniteLaw.probability_timedStoppedProcess_deviation_ge_le_exp
    (P := GreedyInvariant F) n (fun _ ↦ greedyKernel F) active obs S₀
    (neighborConcentrationTheta M t s) 3 margin variance hInv₀ hbudget.1 (by norm_num)
    hbudget.2.1 hvariance0 (fun _ _ S hS ↦ greedyKernel_supported hS)
    (fun i hi S hS ha S' hmass _ ↦ (le_abs_self _).trans ((hpoint i hi S hS ha).1 S' hmass))
    (fun i hi S hS ha ↦ (hpoint i hi S hS ha).2.1)
    (fun i hi S hS ha ↦ (hpoint i hi S hS ha).2.2)
  have htotal := htail.trans (neighbor_concentration_exponential_le_half N M margin variance n t s b hNpos
    (by linarith [P.scale_large]) hsize hsteps hvariance0 le_rfl le_rfl)
  simpa only [obs, margin, M, s, Nat.cast_zero] using htotal

end

end Erdos207
