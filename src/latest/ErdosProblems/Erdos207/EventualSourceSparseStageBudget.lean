/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceSparseStageBudget
import ErdosProblems.Erdos207.EventualSparsePriorBudgets
import ErdosProblems.Erdos207.SourceAugmentedCoefficientPower

/-! # Construct all frozen-stage scalar inputs at uniform thresholds -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_source_sparse_stage_budget
    (q stage Bexp physical c v d R m lower : ℕ)
    (Caux Cdegree Cprior B0 eta0 : ℝ≥0)
    (hb : 2 ≤ physical) (hc : 1 ≤ c) (hm : 1 ≤ m) (hd : physical+1 ≤ d) (hvd : v ≤ d)
    (hCaux : 1 ≤ Caux) (hCprior : 1 ≤ Cprior) (heta0 : 0 < eta0)
    (henvelope : 4*q ≤ Bexp)
    (hpair : ksssPairDriftCoefficient q (fun a ↦ 9*24^a) +
      ksssPairTaylorCoefficient (ksssOrders q) (fun a ↦ 9*24^a) ≤ 3*(Bexp : ℝ))
    (hconfiguration : ∀ a : CrudeOrderIndex q 4,
      ksssIndexedConfigurationDriftCoefficient q (fun j ↦ 9*24^j) a +
        ksssConfigurationTaylorCoefficient (ksssOrders q) (fun j ↦ 9*24^j)
          (a.order-3) a.chosen ≤ 3*(Bexp : ℝ)/2) :
    ∃ Tphysical Tanalytic : ℕ, 8 ≤ Tphysical ∧ lower ≤ Tanalytic ∧ 49152 ≤ Tanalytic ∧
      ∀ t u : ℕ, Tphysical ≤ t → Tanalytic ≤ u → u ≤ t → t^d ≤ u^c →
      ∀ n N : ℕ, u ^ ksssPowerDenominatorExponent q (2*c) Bexp ((26*q+12)*c) c ≤ n →
        n ≤ N → N ≤ u^R →
      ∀ p eta beta : ℝ≥0, 1/(t : ℝ≥0)^physical ≤ p → p ≤ 2/(t : ℝ≥0)^physical →
        eta0 ≤ eta → eta ≤ 1 → beta ≤ B0/(u : ℝ≥0)^sourceStageRequiredError q c R m →
      ∀ z : ℕ → ℝ≥0, (∀ j ∈ Icc 4 q, z j ≤ (t : ℝ≥0)^v) →
        SourceSparseStageBudget q stage (2*c) Bexp ((26*q+12)*c) u c c R m n N
          p eta Caux Cprior beta B0 (1/(t : ℝ≥0)^2) z ∧
        sourceAllAuxiliaryDegreeFailure q (3*R+3*c) u (3*c) Cdegree B0 ≤ 1/(t : ℝ≥0)^2 ∧
        1/(u : ℝ≥0)^(c*m) ≤ 1/(t : ℝ≥0)^m ∧
        1/(u : ℝ≥0)^(2*c) ≤ p ∧ p ≤ 1/u ∧ Caux ≤ u := by
  let coefficientLower : ℕ := lower+49152+2^q+q+⌈sourceCrudeUniformCoefficient stage q (Icc 4 q).card 1 1⌉₊+⌈Caux⌉₊
  obtain ⟨Tc, hTc, hcoefficient⟩ := exists_ksss_power_coefficient_threshold q Bexp coefficientLower
    (fun a ↦ 9*24^a)
  obtain ⟨Ta, hTa, hTa2, hbudgets⟩ := eventually_source_sparse_prior_budgets q c R m Tc Cdegree Cprior B0 hc hm
  let Tp := 8+⌈(24+2*Caux)/eta0⌉₊
  have htwoq : (1 : ℕ) ≤ 2^q := Nat.one_le_pow _ _ (by norm_num)
  have hTmin : 49152 ≤ Ta := by dsimp only [coefficientLower] at hTc; omega
  have hlower : lower ≤ Ta := by dsimp only [coefficientLower] at hTc; omega
  refine ⟨Tp, Ta, by dsimp only [Tp]; omega, hlower, hTmin, ?_⟩
  intro t u ht hu hut hpower n N hscale hnN hN p eta beta hpLo hpHi heta heta1 hbeta z hz
  have ht8 : 8 ≤ t := by dsimp only [Tp] at ht; omega
  have htNN : (8 : ℝ≥0) ≤ t := by exact_mod_cast ht8
  have ht1 : (1 : ℝ≥0) ≤ t := (by norm_num : (1 : ℝ≥0) ≤ 8).trans htNN
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le ht1
  have huLarge : 49152 ≤ u := hTmin.trans hu
  have hu1Nat : 1 ≤ u := by omega
  have hu1 : (1 : ℝ≥0) ≤ u := by exact_mod_cast hu1Nat
  have hu4 : (4 : ℝ≥0) ≤ u := by exact_mod_cast (show 4 ≤ u by omega)
  have hutNN : (u : ℝ≥0) ≤ t := by exact_mod_cast hut
  have hpowerNN : (t : ℝ≥0)^d ≤ (u : ℝ≥0)^c := by exact_mod_cast hpower
  have htuc : (t : ℝ≥0) ≤ (u : ℝ≥0)^c := by
    apply le_trans _ hpowerNN
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (show 1 ≤ d by omega)
  have hconstant : 24+2*Caux ≤ eta*(t : ℝ≥0) := by
    have hceil : (24+2*Caux)/eta0 ≤ (t : ℝ≥0) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈(24+2*Caux)/eta0⌉₊ ≤ t by dsimp only [Tp] at ht; omega))
    have hbase : 24+2*Caux ≤ eta0*t := by
      simpa only [mul_comm] using (div_le_iff₀ heta0).mp hceil
    exact hbase.trans (mul_le_mul_of_nonneg_right heta zero_le)
  have h24 : 24 ≤ eta*(t : ℝ≥0) := (le_add_of_nonneg_right zero_le).trans hconstant
  have hC : 2*Caux ≤ eta*(t : ℝ≥0) := (le_add_of_nonneg_left zero_le).trans hconstant
  have hdensity := source_stage_density_scalars t u p eta n Caux physical c d htNN hu1 hutNN hb hd
    hpowerNN hpLo hpHi h24 hC
  have haux : Caux ≤ (u : ℝ≥0) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show ⌈Caux⌉₊ ≤ u by dsimp only [coefficientLower] at hTc; omega)
  have hnum := hbudgets u hu t ht0 htuc
  have herror : 1/(t : ℝ≥0)^2 < 1 := by
    have h2 : (2 : ℝ≥0) ≤ t := (by norm_num : (2 : ℝ≥0) ≤ 8).trans htNN
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ≥0) < 2^2) (pow_le_pow_left' h2 2)
    exact hh.trans_lt (by norm_num)
  have hn : 1 ≤ n := (Nat.one_le_pow _ _ hu1Nat).trans hscale
  have hp : 0 < p := (by positivity : (0 : ℝ≥0) < 1/(t : ℝ≥0)^physical).trans_le hpLo
  have hp1 : p ≤ 1 := hdensity.2.1.trans ((div_le_one (zero_lt_one.trans_le hu1)).mpr hu1)
  have hcoeff : KSSSPowerCoefficientBounds q (fun a ↦ 9*24^a) Bexp u :=
    hcoefficient.mono (by exact_mod_cast hTa.trans hu)
  refine ⟨?_, hnum.2.2.2.2.2.1, hnum.2.2.1, hdensity.1, hdensity.2.1, haux⟩
  refine {
    p_pos := hp
    p_le_one := hp1
    eta_pos := heta0.trans_le heta
    eta_le_one := heta1
    current_pos := hn
    large := huLarge
    binomial := by dsimp only [coefficientLower] at hTc; omega
    order := by dsimp only [coefficientLower] at hTc; omega
    scale := hscale
    edge_floor := hdensity.2.2.2.1
    ratio_floor := hdensity.2.2.1
    auxiliary_pos := hCaux
    auxiliary_small := hdensity.2.2.2.2.1
    coefficient := hcoeff
    envelope := henvelope
    pair := hpair
    configuration := hconfiguration
    density_exponent := le_rfl
    prior_pos := hCprior
    augmented_z := ?_
    crude_constant := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈sourceCrudeUniformCoefficient stage q (Icc 4 q).card 1 1⌉₊ ≤ u by
        dsimp only [coefficientLower] at hTc; omega))
    cutoff := source_stage_scaled_crude_cutoff q 5 (26*q+12) c hc (by omega)
    ambient := hN
    incoming_error := hbeta
    delta_pos := hnum.1
    delta_lt_one := hnum.2.1
    geometric := hnum.2.2.2.1
    band := hnum.2.2.2.2.1 n (hnN.trans hN)
    prior_budget := hnum.2.2.2.2.2.2
    error_lt_one := herror }
  intro j hj
  exact source_augmented_coefficient_power t u (z j) c v d ht1 hu4 hc hvd hpowerNN (hz j hj)

end

end Erdos207
