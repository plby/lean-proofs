/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationActualProducts
import ErdosProblems.Erdos207.ConfigurationScaledDrift
import ErdosProblems.Erdos207.KSSSConfigurationSlopeSource

/-! # Configuration drift from the coupled trajectory and crude events -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ksssConfigurationSuccDriftCoefficient (q : ℕ) (b : ℕ → ℝ) (d c : ℕ) : ℝ :=
  configurationDriftScaleCoefficient (d - c : ℕ) (d - (c + 1) : ℕ)
    (ksssConfigurationProductCoefficient (ksssOrders q) b d (c + 1) + 1) 1
    ((q : ℝ) + 5) ((d - (c + 1)) + (d - (c + 1)).choose 2 : ℕ)
    (Real.exp (∑ k ∈ ksssOrders q, b k) / 3) (ksssThreatCoefficient (ksssOrders q) b)
    (1 / 3 + ksssThreatCoefficient (ksssOrders q) b + ((q : ℝ) + 5))
    (ksssConfigurationSuccTargetCoefficient (ksssOrders q) b d c)

def ksssConfigurationZeroDriftCoefficient (q : ℕ) (b : ℕ → ℝ) (d : ℕ) : ℝ :=
  configurationDriftScaleCoefficient 0 d
    (ksssConfigurationProductCoefficient (ksssOrders q) b d 0 + 1) 0
    ((q : ℝ) + 5) (d + d.choose 2 : ℕ) 0 (ksssThreatCoefficient (ksssOrders q) b)
    (1 / 3 + ksssThreatCoefficient (ksssOrders q) b + ((q : ℝ) + 5))
    ((d : ℝ) * ksssConfigurationProductCoefficient (ksssOrders q) b d 0 *
      ksssThreatCoefficient (ksssOrders q) b)

theorem KSSSOnTrajectories.configuration_succ_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q : Finset (Finset V)}
    {a b : ℕ → ℝ} {E A scale time : ℝ} {B K₀ : ℕ} {K : CrudeThresholds}
    (h : KSSSOnTrajectories F S q Q a E A scale B time)
    (hcrude : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hE : 0 < E) (hA : 0 < A) (hs : 0 ≤ scale) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ b d)
    (he : 2 ≤ ksssErrorEnvelope E scale B time)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory (ksssOrders q) a E A time / 4)
    (hcommon : (K.common : ℝ) ≤ ksssErrorEnvelope E scale B time)
    (hlarge : 12 * (ksssThreatCoefficient (ksssOrders q) b + ((q : ℝ) + 5)) ≤
      E * ksssEdgeDensity E time)
    (hxe : ksssPairTrajectory (ksssOrders q) a E A time ≤
      (E * ksssEdgeDensity E time) * ksssErrorEnvelope E scale B time)
    (hoverlap : 9 + 6 * K.pair + K.common ≤ (K₀ : ℝ≥0))
    (hK : (K₀ : ℝ) ≤ ksssErrorEnvelope E scale B time)
    (d c : ℕ) (hd : d ∈ ksssOrders q) (hc : c + 2 ≤ d)
    (root : TripleOn V) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hgain : (∑ D ∈ greedyConfigurationClass (forbiddenFamilyOfOrder F (d + 3)) S root c,
      ((greedyConfigurationRedundantWitnesses F S D).card : ℝ)) ≤
      ksssPairTrajectory (ksssOrders q) a E A time *
        ksssConfigurationErrorEnvelope E A scale B (d - (c + 1) - 1) time) :
    |(restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass (forbiddenFamilyOfOrder F (d + 3)) S' root (c + 1)).card : ℝ) -
          (greedyConfigurationClass (forbiddenFamilyOfOrder F (d + 3)) S root (c + 1)).card) -
      ksssConfigurationSlope (ksssOrders q) a E A d (c + 1) time| ≤
      ksssConfigurationSuccDriftCoefficient q b d c *
        ksssConfigurationErrorEnvelope E A scale B (d - (c + 1) - 1) time /
          (E * ksssEdgeDensity E time) := by
  let orders := ksssOrders q
  let x := ksssPairTrajectory orders a E A time
  let H := ksssThreatTrajectory orders a E A time
  let L := E * ksssEdgeDensity E time
  let e := ksssErrorEnvelope E scale B time
  let z := d - (c + 1) - 1
  let hcfg := ksssConfigurationErrorEnvelope E A scale B z time
  let W := Real.exp (∑ k ∈ orders, b k) / 3
  let C := ksssThreatCoefficient orders b
  have hp := ksssEdgeDensity_pos hE hclock
  have hx : 0 < x := ksssPairTrajectory_pos orders a hE hA hclock
  have hb : ∀ k ∈ orders, 0 ≤ b k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have horders : ∀ k ∈ orders, 1 ≤ k := fun k hk ↦ (mem_Icc.mp hk).1
  have hC : 0 ≤ C := ksssThreatCoefficient_nonneg orders b hb
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hH := ksssThreatTrajectory_bounds orders a b horders ha hab hE hA ht hclock
  have hH0 : 0 ≤ H := by dsimp only [H]; linarith only [hx, hH.1]
  have hHabs : |H| ≤ C * x := by rw [abs_of_nonneg hH0]; exact hH.2
  have hglobal := h.availability_error hQ hcover
  rw [hQcard] at hglobal
  have hthreat : ∀ U ∈ S.available, |((greedyClosedThreats F S U).card : ℝ) - H| ≤
      ((q : ℝ) + 5) * e := fun U hU ↦
    h.closed_threat_error hcrude hS hpack hcard hcover he hcommon hU
  have hinter : ∀ U ∈ S.available, ∀ U' ∈ S.available, U ≠ U' → (U.1 ∩ U'.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S U').card ≤ K₀ := by
    intro U hU U' hU' _ hdis
    exact_mod_cast (hcrude.closed_inter hS hpack hU hU' hdis).trans hoverlap
  have hj : d + 3 ∈ Icc 4 q := by have hd' := mem_Icc.mp hd; simp only [mem_Icc]; omega
  have hid : d + 3 - 3 = d := by omega
  have hprevIndex : d + 3 - 4 - c = z + 1 := by dsimp only [z]; omega
  have hcurrIndex : d + 3 - 4 - (c + 1) = z := by dsimp only [z]; omega
  have hprev := h.2 root hroot (d + 3) hj c (by omega)
  simp only [hid, hprevIndex] at hprev
  have hcurr := h.2 root hroot (d + 3) hj (c + 1) (by omega)
  simp only [hid, hcurrIndex] at hcurr
  have hprod := ksssConfiguration_actual_product orders a b E A scale time
    ((greedyConfigurationClass (forbiddenFamilyOfOrder F (d + 3)) S root (c + 1)).card : ℝ)
    B d (c + 1) hE hA hs ht hclock ha hab hd hc (by dsimp only [x] at hx; linarith) hcurr
  have hprevProd := ksssConfigurationErrorEnvelope_succ_le_pair orders a b E A scale time B z
    hE hA hs ht hclock ha hab
  have htarget := ksssConfiguration_succ_target_product orders a b E A scale time B d c
    hE hA hs ht hclock horders ha hab hd hc
  have hFcoef : 0 ≤ ksssConfigurationProductCoefficient orders b d (c + 1) + 1 := by
    unfold ksssConfigurationProductCoefficient
    have hd0 := hb d hd
    positivity
  have hTcoef : 0 ≤ ksssConfigurationSuccTargetCoefficient orders b d c := by
    unfold ksssConfigurationSuccTargetCoefficient ksssConfigurationProductCoefficient
    have hd0 := hb d hd
    change 0 ≤ _ + _ * _ * C
    positivity
  have hh : 0 ≤ hcfg := by
    dsimp only [hcfg]
    unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
    positivity
  have hraw := restrictedGreedyKernel_configuration_succ_source_scale root d c K₀
    L x e hcfg H (ksssConfigurationTrajectory orders a E A d c time)
    (ksssConfigurationTrajectory orders a E A d (c + 1) time)
    (ksssConfigurationErrorEnvelope E A scale B (z + 1) time)
    (ksssConfigurationProductCoefficient orders b d (c + 1) + 1) 1 ((q : ℝ) + 5) W C
    (ksssConfigurationSuccTargetCoefficient orders b d c) hS hroot hR
    (fun D hD ↦ by have hm := (mem_forbiddenFamilyOfOrder.mp hD).2; omega)
    (fun D hD ↦ hpack D (mem_forbiddenFamilyOfOrder.mp hD).1) hc
    (mul_pos hE hp) hx hh hFcoef (by norm_num) (by positivity) hW hC hTcoef
    hsmall hlarge hxe hglobal hHabs hthreat hinter hK
    (by simpa only [one_mul] using hgain) hprev hcurr hprod hprevProd htarget
  have hAvail : ksssAvailableTrajectory orders a E A time = L * x / 3 := by
    dsimp only [L, x]
    unfold ksssPairTrajectory
    field_simp
  rw [ksssConfigurationSlope_succ_source orders a E A time horders hE.ne' hp.ne'
    (ksssAvailableTrajectory_pos orders a hE hA hclock).ne' (by omega), hAvail]
  exact hraw

theorem KSSSOnTrajectories.configuration_zero_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q : Finset (Finset V)}
    {a b : ℕ → ℝ} {E A scale time : ℝ} {B K₀ : ℕ} {K : CrudeThresholds}
    (h : KSSSOnTrajectories F S q Q a E A scale B time)
    (hcrude : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hE : 0 < E) (hA : 0 < A) (hs : 0 ≤ scale) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ b d)
    (he : 2 ≤ ksssErrorEnvelope E scale B time)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory (ksssOrders q) a E A time / 4)
    (hcommon : (K.common : ℝ) ≤ ksssErrorEnvelope E scale B time)
    (hlarge : 12 * (ksssThreatCoefficient (ksssOrders q) b + ((q : ℝ) + 5)) ≤
      E * ksssEdgeDensity E time)
    (hxe : ksssPairTrajectory (ksssOrders q) a E A time ≤
      (E * ksssEdgeDensity E time) * ksssErrorEnvelope E scale B time)
    (hoverlap : 9 + 6 * K.pair + K.common ≤ (K₀ : ℝ≥0))
    (hK : (K₀ : ℝ) ≤ ksssErrorEnvelope E scale B time)
    (d : ℕ) (hd : d ∈ ksssOrders q)
    (root : TripleOn V) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty) :
    |(restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass (forbiddenFamilyOfOrder F (d + 3)) S' root 0).card : ℝ) -
          (greedyConfigurationClass (forbiddenFamilyOfOrder F (d + 3)) S root 0).card) -
      ksssConfigurationSlope (ksssOrders q) a E A d 0 time| ≤
      ksssConfigurationZeroDriftCoefficient q b d *
        ksssConfigurationErrorEnvelope E A scale B (d - 1) time /
          (E * ksssEdgeDensity E time) := by
  let orders := ksssOrders q
  let x := ksssPairTrajectory orders a E A time
  let H := ksssThreatTrajectory orders a E A time
  let L := E * ksssEdgeDensity E time
  let e := ksssErrorEnvelope E scale B time
  let hcfg := ksssConfigurationErrorEnvelope E A scale B (d - 1) time
  let C := ksssThreatCoefficient orders b
  have hp := ksssEdgeDensity_pos hE hclock
  have hx : 0 < x := ksssPairTrajectory_pos orders a hE hA hclock
  have hb : ∀ k ∈ orders, 0 ≤ b k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have horders : ∀ k ∈ orders, 1 ≤ k := fun k hk ↦ (mem_Icc.mp hk).1
  have hC : 0 ≤ C := ksssThreatCoefficient_nonneg orders b hb
  have hH := ksssThreatTrajectory_bounds orders a b horders ha hab hE hA ht hclock
  have hH0 : 0 ≤ H := by dsimp only [H]; linarith only [hx, hH.1]
  have hHabs : |H| ≤ C * x := by rw [abs_of_nonneg hH0]; exact hH.2
  have hglobal := h.availability_error hQ hcover
  rw [hQcard] at hglobal
  have hthreat : ∀ U ∈ S.available, |((greedyClosedThreats F S U).card : ℝ) - H| ≤
      ((q : ℝ) + 5) * e := fun U hU ↦
    h.closed_threat_error hcrude hS hpack hcard hcover he hcommon hU
  have hinter : ∀ U ∈ S.available, ∀ U' ∈ S.available, U ≠ U' → (U.1 ∩ U'.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S U').card ≤ K₀ := by
    intro U hU U' hU' _ hdis
    exact_mod_cast (hcrude.closed_inter hS hpack hU hU' hdis).trans hoverlap
  have hd1 := horders d hd
  have hj : d + 3 ∈ Icc 4 q := by have hd' := mem_Icc.mp hd; simp only [mem_Icc]; omega
  have hid : d + 3 - 3 = d := by omega
  have hcurrIndex : d + 3 - 4 - 0 = d - 1 := by omega
  have hcurr := h.2 root hroot (d + 3) hj 0 (by omega)
  simp only [hid, hcurrIndex] at hcurr
  have hprod := ksssConfiguration_actual_product orders a b E A scale time
    ((greedyConfigurationClass (forbiddenFamilyOfOrder F (d + 3)) S root 0).card : ℝ)
    B d 0 hE hA hs ht hclock ha hab hd hd1 (by dsimp only [x] at hx; linarith) hcurr
  have htarget := ksssConfiguration_zero_target_product orders a b E A scale time B d
    hE hA hs ht hclock horders ha hab hd
  have hprod0 : 0 ≤ ksssConfigurationProductCoefficient orders b d 0 := by
    unfold ksssConfigurationProductCoefficient
    have hd0 := hb d hd
    positivity
  have hh : 0 ≤ hcfg := by
    dsimp only [hcfg]
    unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
    positivity
  have hraw := restrictedGreedyKernel_configuration_zero_source_scale root d K₀
    L x e hcfg H (ksssConfigurationTrajectory orders a E A d 0 time)
    (ksssConfigurationProductCoefficient orders b d 0 + 1) ((q : ℝ) + 5) C
    ((d : ℝ) * ksssConfigurationProductCoefficient orders b d 0 * C) hS hroot hR
    (fun D hD ↦ by have hm := (mem_forbiddenFamilyOfOrder.mp hD).2; omega)
    (fun D hD ↦ hpack D (mem_forbiddenFamilyOfOrder.mp hD).1)
    (mul_pos hE hp) hx hh (by positivity) (by positivity) hC (by positivity)
    hsmall hlarge hxe hglobal hHabs hthreat hinter hK hcurr hprod htarget
  have hAvail : ksssAvailableTrajectory orders a E A time = L * x / 3 := by
    dsimp only [L, x]
    unfold ksssPairTrajectory
    field_simp
  rw [ksssConfigurationSlope_zero_source orders a E A time horders hE.ne' hp.ne'
    (ksssAvailableTrajectory_pos orders a hE hA hclock).ne' hd1, hAvail]
  simpa only [neg_mul, neg_div, sub_neg_eq_add, ksssConfigurationZeroDriftCoefficient,
    orders, H, L, x, C, hcfg] using hraw

end

end Erdos207
