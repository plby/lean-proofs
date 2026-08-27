/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceReserveSizeBudgets
import ErdosProblems.Erdos207.SourceReservePreparation
import ErdosProblems.Erdos207.SourceRegularizedPrecision

/-! # Simultaneous eventual reserve-preparation scalars on the physical and analytic scales -/

namespace Erdos207

open Finset
open scoped Classical NNReal

theorem eventually_source_reserve_preparation_budget
    (q ell b reserveExp D L step R bAn B k Rmin analyticAmbient : ℕ) (eta0 : ℝ≥0)
    (heta0 : 0 < eta0) (hreserve : 1 ≤ reserveExp)
    (hstep : 4*b+2 ≤ step) (hcurrentGap : 4*b+reserveExp+1 ≤ D)
    (hinnerGap : 2*reserveExp+2*b+1 ≤ L) (hlinkGap : reserveExp+3*b+1 ≤ L) :
    ∃ Tphysical Tanalytic : ℕ, 1 ≤ Tphysical ∧ 1 ≤ Tanalytic ∧
      ∀ t analytic N n u : ℕ, Tphysical ≤ t → Tanalytic ≤ analytic →
      N ≤ t^R → n ≤ t^R → t^D ≤ n → t^L ≤ u → t^step*u ≤ 2*n →
      analytic^ksssPowerDenominatorExponent q bAn B k Rmin ≤ n → n ≤ analytic^analyticAmbient →
      ∀ p eta xi : ℝ≥0, 1/(t : ℝ≥0)^b ≤ p → eta0 ≤ eta →
      24/(analytic : ℝ≥0)^bAn ≤ p^2*eta → xi ≤ (17+ell : ℕ)/(t : ℝ≥0) →
      let r := 1/(t : ℝ≥0)^reserveExp
      let epsilon : ℝ≥0 := 1/1048576
      let theta : ℝ := 1/(24*(analytic : ℝ)^ksssPowerErrorExponent bAn B)
      r ≤ 1 ∧ r ≤ 1/24576 ∧ xi ≤ epsilon/4 ∧ xi ≤ 1/1536 ∧
      1 ≤ (epsilon/4)*(p^2*eta*u) ∧ 6144 ≤ p^4*eta^6*n ∧
      (u : ℝ≥0) ≤ p^4*eta^6*n/1536 ∧ 0 < theta ∧ theta ≤ 1/2 ∧
      2*(n : ℝ)^2*Real.exp (-theta^2*((p : ℝ)^2*eta*n)/16) < 1 ∧
      sourceReserveFailureBound N u p eta r epsilon + reserveRegularizationFailureBound n p eta r ≤
        1/(t : ℝ≥0)^2 ∧ 1/(t : ℝ≥0)^2 < 1 := by
  let epsilon : ℝ≥0 := 1/1048576
  let Z : ℝ≥0 := (17+ell : ℕ)
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; norm_num
  obtain ⟨Tref, hTref, href⟩ := eventually_sourceReserveFailureBound_le_power reserveExp b 0 L R 2
    eta0 epsilon (1/2) heta0 hepsilon (by norm_num) hinnerGap (by simpa only [mul_zero, add_zero] using hlinkGap)
  obtain ⟨Treg, hTreg, hreg⟩ := eventually_reserveRegularizationFailureBound_le_power reserveExp b D R 2
    eta0 (1/2) heta0 (by norm_num) hcurrentGap
  obtain ⟨Tanalytic, hTanalytic, hanalytic⟩ := eventually_source_regularized_sampling_success q bAn B k Rmin analyticAmbient
  let constraints : Finset ℝ≥0 := {24576, 4*Z/epsilon, 1536*Z, 6144/eta0^6, 4/(epsilon*eta0)}
  let Tscalar := ⌈∑ x ∈ constraints, x⌉₊
  let Tphysical := Tref+Treg+Tscalar+2
  refine ⟨Tphysical, Tanalytic, by dsimp only [Tphysical]; omega, hTanalytic, ?_⟩
  intro t analytic N n u ht ha hN hn hnLower huLower hratio hscale hnAnalytic p eta xi hp heta hdensity hxi
  dsimp only
  have ht2 : 2 ≤ t := by dsimp only [Tphysical] at ht; omega
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have ha1 : 1 ≤ analytic := hTanalytic.trans ha
  have hconstraints : ∀ x ∈ constraints, x ≤ (t : ℝ≥0) := by
    intro x hx
    exact (single_le_sum (fun _ _ ↦ zero_le) hx).trans ((Nat.le_ceil (∑ x ∈ constraints, x)).trans
      (by exact_mod_cast (show Tscalar ≤ t by dsimp only [Tphysical] at ht; omega)))
  have htLarge : (24576 : ℝ≥0) ≤ t := hconstraints _
    (by simp only [constraints, mem_insert, mem_singleton, eq_self, true_or])
  have hreferenceT : 4*Z/epsilon ≤ (t : ℝ≥0) := hconstraints _
    (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hregularityT : 1536*Z ≤ (t : ℝ≥0) := hconstraints _
    (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hmassT : 6144/eta0^6 ≤ (t : ℝ≥0) := hconstraints _
    (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hendpointT : 4/(epsilon*eta0) ≤ (t : ℝ≥0) := hconstraints _
    (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true])
  let r : ℝ≥0 := 1/(t : ℝ≥0)^reserveExp
  have hr1 : r ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ htNN)
  have hrSmall : r ≤ 1/24576 := (inversePower_parameter_le_one_div t reserveExp htNN hreserve).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ≥0) < 24576) htLarge)
  have hXi := source_reserve_reference_tolerance t Z xi epsilon ht0 hepsilon hxi hreferenceT hregularityT
  have hmassCoef : (6144 : ℝ≥0) ≤ eta0^6*t := by
    have hh := (div_le_iff₀ (pow_pos heta0 6)).mp hmassT
    simpa only [mul_comm (t : ℝ≥0) (eta0^6)] using hh
  have hendpointCoef : (4 : ℝ≥0) ≤ epsilon*eta0*t := by
    have hh := (div_le_iff₀ (mul_pos hepsilon heta0)).mp hendpointT
    simpa only [mul_comm (t : ℝ≥0) (epsilon*eta0)] using hh
  have hendpoint := source_reserve_reference_endpoint_from_power t u p eta eta0 epsilon b L htNN hp heta
    (by exact_mod_cast huLower) (by omega) hendpointCoef
  have hmass := inversePower_fourth_density_scale t p eta eta0 n b D htNN (by omega)
    (by exact_mod_cast hnLower) hp heta
  have hinner := power_vortex_inner_density_margin t n u p eta eta0 b step (by exact_mod_cast ht2) hstep hp heta
    ((by norm_num : (1536 : ℝ≥0) ≤ 6144).trans hmassCoef) (by exact_mod_cast hratio)
  have htheta := source_regularized_precision (analytic : ℝ) bAn B (by exact_mod_cast ha1)
  have hsample := hanalytic analytic ha n p eta (by exact_mod_cast hscale) (by exact_mod_cast hnAnalytic)
    (by exact_mod_cast hdensity)
  have hRef := href t (by dsimp only [Tphysical] at ht; omega) N u p eta r epsilon hN huLower hp le_rfl heta
    (by simp only [pow_zero, div_one, le_refl])
  have hReg := hreg t (by dsimp only [Tphysical] at ht; omega) n p eta r hn hnLower hp le_rfl heta
  refine ⟨hr1, hrSmall, hXi.1, hXi.2, hendpoint, hmassCoef.trans hmass, hinner,
    htheta.1, htheta.2.1, hsample, ?_, ?_⟩
  · calc
      _ ≤ (1/2)/(t : ℝ≥0)^2+(1/2)/(t : ℝ≥0)^2 := add_le_add hRef hReg
      _ = _ := by ring
  · have ht2NN : (2 : ℝ≥0) ≤ t := by exact_mod_cast ht2
    have hpow : (4 : ℝ≥0) ≤ (t : ℝ≥0)^2 := by simpa only [show (2 : ℝ≥0)^2 = 4 by norm_num] using pow_le_pow_left' ht2NN 2
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ≥0) < 4) hpow).trans_lt (by norm_num)

end Erdos207
