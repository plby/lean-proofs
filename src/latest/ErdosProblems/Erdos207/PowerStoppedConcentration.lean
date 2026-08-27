/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerConcentrationOptimization
import ErdosProblems.Erdos207.RootObservableConcentration
import ErdosProblems.Erdos207.UncoveredPairConcentration

/-! # Geometric tails for surviving observables in the actual stopped law -/

namespace Erdos207

open Finset

noncomputable section

theorem power_concentration_exponential_le_half
    (N margin : ℝ) (n t R z H m v : ℕ)
    (hN : 1 ≤ N) (ht : 4 ≤ t) (hscale : (t : ℝ) ^ R ≤ N) (hn : (n : ℝ) ≤ N ^ 2)
    (hmargin : N ^ (z + 1) / (2 * (t : ℝ) ^ m) ≤ margin)
    (hH : v + m + 1 ≤ H) (hR : H + m + 2 ≤ R) :
    Real.exp (-powerConcentrationTheta N t z H * margin +
      powerConcentrationTheta N t z H ^ 2 * (n : ℝ) * (N ^ (2 * z) / N * (t : ℝ) ^ v)) ≤
        (1 / 2 : ℝ) ^ t := by
  have hNpos : 0 < N := by linarith
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have he := power_concentration_exponent_le_neg_scale N t margin n
    (N ^ (2 * z) / N * (t : ℝ) ^ v) R z H m v hN htR hscale (Nat.cast_nonneg _) hn
    (by positivity) le_rfl hmargin hH hR
  exact (Real.exp_le_exp.mpr he).trans (exp_neg_nat_le_half_pow t)

theorem probability_timedStoppedGreedy_root_power_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (root : TripleOn V) (obs : ℕ → GreedyStateOn V → ℝ)
    (N margin : ℝ) (t R z H m v j : ℕ)
    (hN : 1 ≤ N) (ht : 4 ≤ t) (hscale : (t : ℝ) ^ R ≤ N) (hn : (n : ℝ) ≤ N ^ 2)
    (hmargin : N ^ (z + 1) / (2 * (t : ℝ) ^ m) ≤ margin)
    (hj : j ≤ H) (hH : v + m + 1 ≤ H) (hR : H + m + 2 ≤ R)
    (hInv₀ : GreedyInvariant F S₀) (hroot₀ : root ∈ S₀.available)
    (hjump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ T ∈ S.available \ greedyClosedThreats F S root,
        obs (i + 1) (greedyStep F S T) - obs i S ≤ N ^ z * (t : ℝ) ^ j)
    (hdrift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ hSel : (S.available \ greedyClosedThreats F S root).Nonempty,
        (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hSel).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ hSel : (S.available \ greedyClosedThreats F S root).Nonempty,
        (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hSel).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ N ^ (2 * z) / N * (t : ℝ) ^ v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ root ∈ w.2.available ∧ margin ≤ obs w.1.1 w.2 - obs 0 S₀) : ℝ) ≤
      (1 / 2 : ℝ) ^ t := by
  have hNpos : 0 < N := by linarith
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htail := probability_timedStoppedGreedy_root_observable_le_exp n F active S₀ root obs
    (N ^ z * (t : ℝ) ^ j) (powerConcentrationTheta N t z H) margin
    (N ^ (2 * z) / N * (t : ℝ) ^ v) hInv₀ hroot₀ hjump hdrift hsecond (by positivity)
    (powerConcentrationTheta_pos N t z H hNpos htpos)
    (powerConcentrationTheta_jump_le_one N t _ z H j hNpos
      (by exact_mod_cast (show 1 ≤ t by omega)) hj le_rfl) (by positivity)
  exact htail.trans (power_concentration_exponential_le_half N margin n t R z H m v
    hN ht hscale hn hmargin hH hR)

theorem probability_timedStoppedGreedy_uncovered_pair_power_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V) (hP : P.card = 2) (obs : ℕ → GreedyStateOn V → ℝ)
    (N margin : ℝ) (t R H m v j : ℕ)
    (hN : 1 ≤ N) (ht : 4 ≤ t) (hscale : (t : ℝ) ^ R ≤ N) (hn : (n : ℝ) ≤ N ^ 2)
    (hmargin : N / (2 * (t : ℝ) ^ m) ≤ margin)
    (hj : j ≤ H) (hH : v + m + 1 ≤ H) (hR : H + m + 2 ≤ R)
    (hInv₀ : GreedyInvariant F S₀) (hpair₀ : PairUncovered P S₀)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S → S.available.Nonempty)
    (hjump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S →
      ∀ T ∈ S.available \ availableTrianglesContainingPair S P,
        obs (i + 1) (greedyStep F S T) - obs i S ≤ (t : ℝ) ^ j)
    (hdrift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S →
      ∀ hSel : (S.available \ availableTrianglesContainingPair S P).Nonempty,
        (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P) hSel).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S →
      ∀ hSel : (S.available \ availableTrianglesContainingPair S P).Nonempty,
        (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P) hSel).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ 1 / N * (t : ℝ) ^ v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ PairUncovered P w.2 ∧ margin ≤ obs w.1.1 w.2 - obs 0 S₀) : ℝ) ≤
      (1 / 2 : ℝ) ^ t := by
  have hNpos : 0 < N := by linarith
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hThetaM : powerConcentrationTheta N t 0 H * (t : ℝ) ^ j ≤ 1 := by
    simpa only [pow_zero, one_mul] using powerConcentrationTheta_jump_le_one N t ((t : ℝ) ^ j)
      0 H j hNpos (by exact_mod_cast (show 1 ≤ t by omega)) hj (by simp)
  have htail := probability_timedStoppedGreedy_uncovered_pair_observable_le_exp n F active S₀ P hP obs
    ((t : ℝ) ^ j) (powerConcentrationTheta N t 0 H) margin (1 / N * (t : ℝ) ^ v)
    hInv₀ hpair₀ havailable hjump hdrift hsecond (by positivity)
    (powerConcentrationTheta_pos N t 0 H hNpos htpos) hThetaM (by positivity)
  have hbound := power_concentration_exponential_le_half N margin n t R 0 H m v
    hN ht hscale hn (by simpa only [zero_add, pow_one] using hmargin) hH hR
  exact htail.trans (by simpa only [mul_zero, pow_zero] using hbound)

end

end Erdos207
