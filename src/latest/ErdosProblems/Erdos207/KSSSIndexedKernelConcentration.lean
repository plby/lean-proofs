/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSIndexedSelectors

/-! # One indexed geometric-tail theorem for the actual frozen greedy law -/

namespace Erdos207

open Finset

noncomputable section

def ksssIndexedCenteredObservable
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (a : ℕ → ℝ) (E A scale : ℝ) (B : ℕ) (sigma : ℝ)
    (index : KSSSTrajectoryIndex V q) (time : ℕ) (S : GreedyStateOn V) : ℝ :=
  ksssCenteredTrajectoryObservable F a E A scale B sigma time S index

structure KSSSIndexedKernelPowerBounds
    {V : Type*} [Fintype V] [DecidableEq V] (q n : ℕ)
    (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop) (Q₀ : Finset (Finset V))
    (a : ℕ → ℝ) (E A scale : ℝ) (B : ℕ) (sigma N : ℝ) (t j v : ℕ) : Prop where
  available : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty
  jump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
    ∀ index : KSSSTrajectoryIndex V q, ksssTrajectoryTracked S (ksssResidualPairs Q₀ S) index →
      ∀ T ∈ ksssTrajectorySelectors F S index,
        ksssIndexedCenteredObservable F a E A scale B sigma index (i + 1) (greedyStep F S T) -
          ksssIndexedCenteredObservable F a E A scale B sigma index i S ≤
            N ^ ksssTrajectoryDimension index * (t : ℝ) ^ j
  drift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
    ∀ index : KSSSTrajectoryIndex V q, ksssTrajectoryTracked S (ksssResidualPairs Q₀ S) index →
      ∀ hSel : (ksssTrajectorySelectors F S index).Nonempty,
        (restrictedGreedyKernel F S (ksssTrajectorySelectors F S index) hSel).expectationReal
          (fun S' ↦ ksssIndexedCenteredObservable F a E A scale B sigma index (i + 1) S' -
            ksssIndexedCenteredObservable F a E A scale B sigma index i S) ≤ 0
  second : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
    ∀ index : KSSSTrajectoryIndex V q, ksssTrajectoryTracked S (ksssResidualPairs Q₀ S) index →
      ∀ hSel : (ksssTrajectorySelectors F S index).Nonempty,
        (restrictedGreedyKernel F S (ksssTrajectorySelectors F S index) hSel).expectationReal
          (fun S' ↦ (ksssIndexedCenteredObservable F a E A scale B sigma index (i + 1) S' -
            ksssIndexedCenteredObservable F a E A scale B sigma index i S) ^ 2) ≤
              N ^ (2 * ksssTrajectoryDimension index) / N * (t : ℝ) ^ v

theorem probability_ksss_indexed_deviation_power_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    (q n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (Q₀ : Finset (Finset V)) (a : ℕ → ℝ)
    (E A sigma N : ℝ) (B t R s b H j v : ℕ)
    (hN : 1 ≤ N) (ht : 4 ≤ t) (hscale : (t : ℝ) ^ R ≤ N) (hn : (n : ℝ) ≤ N ^ 2)
    (hratio : N / (t : ℝ) ^ b ≤ A / E)
    (hj : j ≤ H) (hH : v + (s + b * q) + 1 ≤ H) (hR : H + (s + b * q) + 2 ≤ R)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (h : KSSSIndexedKernelPowerBounds q n F active Q₀ a E A (N / (t : ℝ) ^ s) B sigma N t j v)
    (index : KSSSTrajectoryIndex V q) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ ksssTrajectoryTracked w.2 (ksssResidualPairs Q₀ w.2) index ∧
        ksssInitialMargin E A (N / (2 * (t : ℝ) ^ s)) index ≤
          ksssIndexedCenteredObservable F a E A (N / (t : ℝ) ^ s) B sigma index w.1.1 w.2 -
            ksssIndexedCenteredObservable F a E A (N / (t : ℝ) ^ s) B sigma index 0 S₀) : ℝ) ≤
      (1 / 2 : ℝ) ^ t := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hmargin := ksssInitialMargin_power_lower E A N t s b (by linarith) ht1 hratio index
  by_cases hinitial : ksssTrajectoryTracked S₀ Q₀ index
  · rcases index with P | ⟨i, root⟩
    · let obs := ksssIndexedCenteredObservable F a E A (N / (t : ℝ) ^ s) B sigma (.inl P : KSSSTrajectoryIndex V q)
      have hpair := probability_timedStoppedGreedy_uncovered_pair_power_tail n F active S₀ P.1 P.2 obs
        N (ksssInitialMargin E A (N / (2 * (t : ℝ) ^ s)) (.inl P : KSSSTrajectoryIndex V q))
        t R H (s + b * q) v j hN ht hscale hn
        (by simpa only [ksssTrajectoryDimension, zero_add, pow_one] using hmargin) hj hH hR
        hInv₀ (pairUncovered_of_chosen_empty P.1 S₀ hchosen₀)
        (fun time htime S hS hactive _ ↦ h.available time htime S hS hactive)
        (fun time htime S hS hactive halive T hT ↦ by
          have htracked := (ksssTracked_residual_pair_iff (q := q) Q₀ S P).mpr ⟨hinitial, halive⟩
          simpa only [ksssTrajectoryDimension, pow_zero, one_mul] using
            h.jump time htime S hS hactive (.inl P) htracked T hT)
        (fun time htime S hS hactive halive hSel ↦
          h.drift time htime S hS hactive (.inl P)
            ((ksssTracked_residual_pair_iff Q₀ S P).mpr ⟨hinitial, halive⟩) hSel)
        (fun time htime S hS hactive halive hSel ↦ by
          have htracked := (ksssTracked_residual_pair_iff (q := q) Q₀ S P).mpr ⟨hinitial, halive⟩
          simpa only [ksssTrajectoryDimension, ksssTrajectorySelectors, obs, mul_zero, pow_zero] using
            h.second time htime S hS hactive (.inl P) htracked hSel)
      have hmono : (L.probability (fun w ↦
          ksssTrajectoryTracked w.2 (ksssResidualPairs Q₀ w.2) (.inl P : KSSSTrajectoryIndex V q) ∧
            ksssInitialMargin E A (N / (2 * (t : ℝ) ^ s)) (.inl P : KSSSTrajectoryIndex V q) ≤
              obs w.1.1 w.2 - obs 0 S₀) : ℝ) ≤
          (L.probability (fun w ↦ PairUncovered P.1 w.2 ∧
            ksssInitialMargin E A (N / (2 * (t : ℝ) ^ s)) (.inl P : KSSSTrajectoryIndex V q) ≤
              obs w.1.1 w.2 - obs 0 S₀) : ℝ) := by
        apply NNReal.coe_le_coe.mpr
        apply L.probability_mono
        intro w hw
        exact ⟨(mem_sdiff.mp hw.1).2, hw.2⟩
      exact hmono.trans hpair
    · exact probability_timedStoppedGreedy_root_power_tail n F active S₀ root
        (ksssIndexedCenteredObservable F a E A (N / (t : ℝ) ^ s) B sigma (.inr (i, root)))
        N (ksssInitialMargin E A (N / (2 * (t : ℝ) ^ s)) (.inr (i, root)))
        t R (i.order - 4 - i.chosen) H (s + b * q) v j hN ht hscale hn hmargin hj hH hR hInv₀ hinitial
        (fun time htime S hS hactive hroot T hT ↦ h.jump time htime S hS hactive (.inr (i, root)) hroot T hT)
        (fun time htime S hS hactive hroot hSel ↦ h.drift time htime S hS hactive (.inr (i, root)) hroot hSel)
        (fun time htime S hS hactive hroot hSel ↦ h.second time htime S hS hactive (.inr (i, root)) hroot hSel)
  · have hzero := probability_ksssTracked_of_not_initial_eq_zero n F active S₀ Q₀ hInv₀ index
      (fun w ↦ ksssInitialMargin E A (N / (2 * (t : ℝ) ^ s)) index ≤
        ksssIndexedCenteredObservable F a E A (N / (t : ℝ) ^ s) B sigma index w.1.1 w.2 -
          ksssIndexedCenteredObservable F a E A (N / (t : ℝ) ^ s) B sigma index 0 S₀) hinitial
    rw [hzero]
    positivity

end

end Erdos207
