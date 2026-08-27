/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternKernelPower
import ErdosProblems.Erdos207.RelativePatternPowerOptimization
import ErdosProblems.Erdos207.PatternConcentration

/-! # Relative pattern concentration for the actual refined stopped greedy law -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSPowerParameters.pattern_relative_power_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (Q : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (hInv₀ : GreedyInvariant F S₀) (hQ₀ : PatternUncovered Q S₀)
    (req : KSSSPatternPowerRequirements q b B k Rmin (graphSupportFinset Q).card (graphEdges Q).card t coeff)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (sigma J : ℝ) (hsigma : |sigma| = 1) (hJ : 1 ≤ J)
    (hsize : J * (t : ℝ) ^ (2 * ksssPowerErrorExponent b B +
      (b * (graphSupportFinset Q).card + (graphEdges Q).card) + 2 * b + 1) ≤ (U.card : ℝ))
    (hband : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PatternUncovered Q S →
      ((properPatternExtensions S.available Q U).card : ℝ) ≤
        2 * ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card i)
    (hLoss : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PatternUncovered Q S →
      ∀ T ∈ patternSurvivalSelectors Q S, ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J) :
    let target := ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card
    let envelope := relativePatternEnvelope E t (ksssPowerErrorExponent b B) B
    let obs := patternRelativeCenteredObservable Q U target envelope sigma
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability (fun z ↦
      PatternUncovered Q z.2 ∧ 8 * (t : ℝ) ^ 2 / (t : ℝ) ^ ksssPowerErrorExponent b B ≤
        obs z.1.1 z.2 - obs 0 S₀) : ℝ) ≤ (1 / 2 : ℝ) ^ t := by
  let N : ℝ := Fintype.card V
  let M : ℝ := U.card
  let s := ksssPowerErrorExponent b B
  let d := b * (graphSupportFinset Q).card + (graphEdges Q).card
  let target := ksssPatternTrajectory (ksssOrders q) a E M (graphSupportFinset Q).card (graphEdges Q).card
  let envelope := relativePatternEnvelope E t s B
  let obs := fun i : ℕ ↦ patternRelativeCenteredObservable Q U target envelope sigma (i : ℝ)
  let jump := (t : ℝ) ^ (d + 1) * J / M
  let variance := (t : ℝ) ^ (d + 2 * b + 1) * J / (M * N ^ 2)
  let margin := 8 * (t : ℝ) ^ 2 / (t : ℝ) ^ s
  have hNpos : 0 < N := by
    have hN1 : (1 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast P.ambient_pos
    linarith
  have hMpos : 0 < M := by dsimp only [M]; exact_mod_cast card_pos.mpr hU
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by linarith [P.scale_large])
  have htpos : (0 : ℝ) < t := by linarith
  have hJpos : 0 < J := by linarith
  have hjump0 : 0 ≤ jump := by dsimp only [jump]; positivity
  have hv0 : 0 ≤ variance := by dsimp only [variance]; positivity
  have hsteps : (n : ℝ) ≤ N ^ 2 := by dsimp only [N]; exact_mod_cast P.horizon
  have hbudget := relative_pattern_concentration_power_budget N M J t n jump variance margin s b d
    hNpos hJpos ht1 hsize hsteps hv0 le_rfl le_rfl le_rfl
  have hpoint := fun i (hi : i < n) S hS ha hQ hR ↦
    P.pattern_relative_kernel_power Q₀ Q U hU req hratio i S hS (hactive i S ha) hR sigma J hsigma hJ
      (hband i hi S hS ha hQ) (hLoss i hi S hS ha hQ)
  have htail := probability_timedStoppedGreedy_pattern_observable_le_exp n F active S₀ Q obs jump
    ((t : ℝ) ^ s) margin variance hInv₀ hQ₀ ?_ ?_ ?_ ?_ hjump0 hbudget.1 hbudget.2.1 hv0
  · simpa only [obs, Nat.cast_zero] using htail.trans
      (relative_pattern_concentration_exponential_le_half N M J jump variance margin n t s b d
        hNpos hJpos (by linarith [P.scale_large]) hsize hsteps hv0 le_rfl le_rfl le_rfl)
  · intro i _ S _ ha _
    have hs := hactive i S ha
    have hscalar := P.scalar_bounds i (Nat.cast_nonneg _) hs.2.2.2
    have hlo := hs.2.1.scalar_availability_lower hscalar hs.1.pair_card hs.1.cover hs.1.count hNpos.le htpos
    exact finset_nonempty_of_real_card_lower S.available (by positivity) hlo
  · intro i hi S hS ha hQ T hT
    have hh := (hpoint i hi S hS ha hQ ⟨T, hT⟩).1 T hT
    exact (le_abs_self _).trans (by simpa only [obs, Nat.cast_add, Nat.cast_one] using hh)
  · intro i hi S hS ha hQ hR
    simpa only [obs, Nat.cast_add, Nat.cast_one] using (hpoint i hi S hS ha hQ hR).2.1
  · intro i hi S hS ha hQ hR
    simpa only [obs, Nat.cast_add, Nat.cast_one] using (hpoint i hi S hS ha hQ hR).2.2

end

end Erdos207
