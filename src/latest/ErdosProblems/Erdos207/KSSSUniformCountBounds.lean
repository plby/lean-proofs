/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSDyadicPairBounds
import ErdosProblems.Erdos207.KSSSPairStateDrift

/-! # Uniform ambient powers for configuration envelopes and actual counts -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssConfigurationScale_le_ambient
    (E A time N : ℝ) (hE : 0 < E) (hA : 0 ≤ A) (ht : 0 ≤ time)
    (hclock : 3 * time < E) (hratio : A / E ≤ N) : ksssConfigurationScale E A time ≤ N := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hp1 := ksssEdgeDensity_le_one hE ht
  have hp2 : ksssEdgeDensity E time ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hp.le hp1 2
  calc
    _ = ksssEdgeDensity E time ^ 2 * (A / E) := by unfold ksssConfigurationScale; ring
    _ ≤ 1 * (A / E) := mul_le_mul_of_nonneg_right hp2 (div_nonneg hA hE.le)
    _ ≤ N := by simpa only [one_mul] using hratio

theorem ksssErrorEnvelope_le_ambient
    (orders : Finset ℕ) (a : ℕ → ℝ) (E A scale time N : ℝ) (B : ℕ)
    (hE : 0 < E) (hA : 0 ≤ A) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hN : 0 ≤ N) (hratio : A / E ≤ N)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time / 4) :
    ksssErrorEnvelope E scale B time ≤ N := by
  have hx := ksssPairTrajectory_le_three_ratio orders a E A time hE hA ht hclock ha
  linarith

theorem ksssConfigurationErrorEnvelope_le_ambient_power
    (E A scale time N : ℝ) (B z : ℕ)
    (hE : 0 < E) (hA : 0 ≤ A) (hs : 0 ≤ scale) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (hratio : A / E ≤ N) (he : ksssErrorEnvelope E scale B time ≤ N) :
    ksssConfigurationErrorEnvelope E A scale B z time ≤ N ^ (z + 1) := by
  have hp := ksssEdgeDensity_pos hE hclock
  have henv : 0 ≤ ksssErrorEnvelope E scale B time := by unfold ksssErrorEnvelope; positivity
  have hN : 0 ≤ N := henv.trans he
  have hw := ksssConfigurationScale_le_ambient E A time N hE hA ht hclock hratio
  calc
    _ = ksssErrorEnvelope E scale B time * ksssConfigurationScale E A time ^ z := rfl
    _ ≤ N * N ^ z := mul_le_mul he
      (pow_le_pow_left₀ (ksssConfigurationScale_nonneg hE hA) hw z)
      (pow_nonneg (ksssConfigurationScale_nonneg hE hA) z) hN
    _ = _ := by rw [pow_succ]; ring

theorem ksssConfigurationTrajectory_le_ambient_power
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E A time N : ℝ) (d c : ℕ)
    (hE : 0 < E) (hA : 0 ≤ A) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (had : 0 ≤ a d) (hab : a d * E ^ d ≤ b d)
    (hcd : c ≤ d) (hratio : A / E ≤ N) :
    ksssConfigurationTrajectory orders a E A d c time ≤ (d.choose c : ℝ) * b d * N ^ (d - c) := by
  have hcoef : 0 ≤ b d := (mul_nonneg had (pow_nonneg hE.le d)).trans hab
  have hw := ksssConfigurationScale_le_ambient E A time N hE hA ht hclock hratio
  have hw0 := ksssConfigurationScale_nonneg (t := time) hE hA
  apply (ksssConfigurationTrajectory_le_scale orders a b E A time d c hE hA ht hclock ha had hab hcd).trans
  gcongr

theorem ksssConfiguration_actual_count_le_ambient_power
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E A scale time N v : ℝ) (B d c : ℕ)
    (hE : 0 < E) (hA : 0 ≤ A) (hs : 0 ≤ scale) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (had : 0 ≤ a d) (hab : a d * E ^ d ≤ b d)
    (hc : c + 1 ≤ d) (hN : 0 ≤ N) (hratio : A / E ≤ N)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time / 4)
    (hv : |v - ksssConfigurationTrajectory orders a E A d c time| ≤
      ksssConfigurationErrorEnvelope E A scale B (d - c - 1) time) :
    v ≤ ((d.choose c : ℝ) * b d + 1) * N ^ (d - c) := by
  have hy := ksssConfigurationTrajectory_le_ambient_power orders a b E A time N d c
    hE hA ht hclock ha had hab (by omega) hratio
  have he := ksssErrorEnvelope_le_ambient orders a E A scale time N B hE hA ht hclock ha hN hratio hsmall
  have hh := ksssConfigurationErrorEnvelope_le_ambient_power E A scale time N B (d - c - 1)
    hE hA hs ht hclock hratio he
  have hdeg : d - c - 1 + 1 = d - c := by omega
  rw [hdeg] at hh
  have hvupper := (abs_le.mp hv).2
  nlinarith only [hy, hh, hvupper]

theorem KSSSOnTrajectories.configuration_count_le_ambient_power
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q : Finset (Finset V)}
    {a b : ℕ → ℝ} {E A scale time N t : ℝ} {B : ℕ}
    (h : KSSSOnTrajectories F S q Q a E A scale B time)
    (hE : 0 < E) (hA : 0 ≤ A) (hs : 0 ≤ scale) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ b d)
    (hN : 0 ≤ N) (hratio : A / E ≤ N)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory (ksssOrders q) a E A time / 4)
    (j c : ℕ) (hj : j ∈ Icc 4 q) (hc : c + 4 ≤ j)
    (hcoef : ((j - 3).choose c : ℝ) * b (j - 3) + 1 ≤ t)
    {root : TripleOn V} (hroot : root ∈ S.available) :
    ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root c).card : ℝ) ≤
      t * N ^ (j - c - 3) := by
  have hd : j - 3 ∈ ksssOrders q := by
    have hj' := mem_Icc.mp hj
    simp only [ksssOrders, mem_Icc]
    omega
  have hidx : j - 4 - c = j - 3 - c - 1 := by omega
  have hv := h.2 root hroot j hj c hc
  rw [hidx] at hv
  have hbound := ksssConfiguration_actual_count_le_ambient_power (ksssOrders q) a b E A scale time N
    ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root c).card : ℝ) B (j - 3) c
    hE hA hs htime hclock ha (ha _ hd) (hab _ hd) (by omega) hN hratio hsmall hv
  have hdeg : j - 3 - c = j - c - 3 := by omega
  rw [hdeg] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hN _))

theorem ksss_closed_threat_count_le_ambient
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E A scale time N M k t : ℝ) (B : ℕ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E ^ d ≤ b d)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hratio : A / E ≤ N)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time / 4)
    (hthreat : |M - ksssThreatTrajectory orders a E A time| ≤ k * ksssErrorEnvelope E scale B time)
    (hcoef : 3 * (ksssThreatCoefficient orders b + k) ≤ t) : M ≤ t * N := by
  have hx := ksssPairTrajectory_pos orders a hE hA hclock
  have hpair := ksssPairTrajectory_le_three_ratio orders a E A time hE hA.le htime hclock ha
  have hH := ksssThreatTrajectory_bounds orders a b horders ha hab hE hA htime hclock
  have hb : ∀ d ∈ orders, 0 ≤ b d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC := ksssThreatCoefficient_nonneg orders b hb
  have herror : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time := by linarith
  have he := mul_le_mul_of_nonneg_left herror hk
  have hM := (abs_le.mp hthreat).2
  have hHupper : ksssThreatTrajectory orders a E A time ≤
      ksssThreatCoefficient orders b * ksssPairTrajectory orders a E A time := hH.2
  have hupper : M ≤ (ksssThreatCoefficient orders b + k) * ksssPairTrajectory orders a E A time := by
    nlinarith only [hM, hHupper, he]
  calc
    _ ≤ (ksssThreatCoefficient orders b + k) * (3 * N) := by
      apply hupper.trans
      exact mul_le_mul_of_nonneg_left (by linarith only [hpair, hratio]) (add_nonneg hC hk)
    _ = (3 * (ksssThreatCoefficient orders b + k)) * N := by ring
    _ ≤ t * N := mul_le_mul_of_nonneg_right hcoef hN

end

end Erdos207
