/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveOverlapPowerBudgets
import ErdosProblems.Erdos207.InitialMasterErrorPowers
import ErdosProblems.Erdos207.SourceLinkScalarChoices
import ErdosProblems.Erdos207.EventualSourceMomentBudgets

/-! # Uniform overlap and geometric tails meet the final link probability budgets -/

namespace Erdos207

open scoped NNReal

theorem eventually_source_reserve_overlap_budget
    (R reserveExp D decay : ℕ) (C B0 : ℝ≥0) (hgap : 2*reserveExp ≤ D) :
    ∃ s B T : ℕ, 1 ≤ s ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ N n : ℕ, N ≤ t^R → n ≤ t^R → t^D ≤ n →
      ∀ beta : ℝ≥0, beta ≤ B0/(t : ℝ≥0)^B →
      let r := 1/(t : ℝ≥0)^reserveExp
      let overlap := ⌈(t : ℝ≥0)*r^2*n⌉₊
      2*s ≤ overlap+1 ∧ (overlap : ℝ≥0) ≤ 2*t*r^2*n ∧
        (overlap+1 : ℝ≥0) ≤ 3*t*r^2*n ∧
        (N : ℝ≥0)^2*((2*(n : ℝ≥0)*C^2*r^2/(overlap+1))^s+
          (2*(n : ℝ≥0)*C^2/(overlap+1))^s*beta) ≤ 1/(t : ℝ≥0)^decay := by
  let s := 2*R+decay+1
  let B := R*s+2*R+decay+1
  let coefficient := (1+B0)*(2*C^2)^s
  let T := max 1 (max (2*s) ⌈coefficient⌉₊)
  refine ⟨s, B, T, by dsimp only [s]; omega, le_max_left _ _, ?_⟩
  intro t ht N n hN hn hnLower beta hbeta
  dsimp only
  have ht1 : 1 ≤ t := (le_max_left 1 _).trans ht
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have hmomentT : 2*s ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hcoef : coefficient ≤ (t : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans ht))
  let r : ℝ≥0 := 1/(t : ℝ≥0)^reserveExp
  have hreserve : 1 ≤ r^2*(n : ℝ≥0) := by
    simpa only [pow_zero] using inversePower_density_ge_power (t : ℝ≥0) r n reserveExp 2 0 D
      htNN le_rfl (by omega) (by exact_mod_cast hnLower)
  have hscale : (t : ℝ≥0) ≤ (t : ℝ≥0)*r^2*n := by
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hreserve (zero_le (a := (t : ℝ≥0)))
  have hmoment : 2*s ≤ ⌈(t : ℝ≥0)*r^2*n⌉₊+1 := by
    have hh : (2*s : ℝ≥0) ≤ (⌈(t : ℝ≥0)*r^2*n⌉₊+1 : ℝ≥0) :=
      (show (2*s : ℝ≥0) ≤ t by exact_mod_cast hmomentT).trans
        (hscale.trans ((Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le)))
    exact_mod_cast hh
  have hround := rounded_reserve_overlap_bounds (t : ℝ≥0) r n (htNN.trans hscale)
  have hn0 : 0 < n := (pow_pos (by omega : 0 < t) D).trans_le hnLower
  have hbound := reserveOverlap_failure_power_bound N n R s B (decay+1) (t : ℝ≥0) r C beta B0
    htNN (by dsimp only [r]; positivity) hn0 (by exact_mod_cast hN) (by exact_mod_cast hn) hbeta
    (by dsimp only [s]; omega) (by dsimp only [B]; omega)
  exact ⟨hmoment, hround.1, hround.2,
    hbound.trans (inverse_power_absorb_coefficient t coefficient decay ht0 hcoef)⟩

theorem eventually_source_link_geometric_budget (R decay : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ N centers degree overlap : ℕ, N ≤ t^R → centers ≤ N →
      ∀ sigma : ℝ≥0, 4*(degree : ℝ≥0)*overlap*sigma^2 ≤ 2*t+1 →
        2*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t ≤ 1/2 ∧
        rawLinkGeometricFailure centers N degree overlap (2*t) t t sigma ≤ 1/(t : ℝ≥0)^decay := by
  obtain ⟨Tgeom, hTgeom, hgeom⟩ := eventually_polynomial_geometric_le_power R 3 decay 10 1 (by norm_num)
  obtain ⟨Thall, hThall, hhall⟩ := eventually_polynomial_geometric_le_power R 2 0 2 (1/2) (by norm_num)
  refine ⟨max Tgeom Thall, hTgeom.trans (le_max_left _ _), ?_⟩
  intro t ht N centers degree overlap hN hcenters sigma hcollision
  have hhal := hhall t ((le_max_right _ _).trans ht) N hN
  refine ⟨by simpa only [pow_zero, div_one] using hhal, ?_⟩
  have hcol : 4*(degree : ℝ≥0)*overlap*sigma^2 ≤ ((2*t : ℕ)+1 : ℝ≥0) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcollision
  apply (rawLinkGeometricFailure_le_single_dyadic centers N degree overlap (2*t) t t sigma le_rfl hcol).trans
  calc
    10*(centers : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t ≤
        10*(N+1 : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t := by
      gcongr
      exact (show (centers : ℝ≥0) ≤ N by exact_mod_cast hcenters).trans (le_add_of_nonneg_right zero_le)
    _ = 10*(N+1 : ℝ≥0)^3*(1/2 : ℝ≥0)^t := by ring
    _ ≤ _ := hgeom t ((le_max_left _ _).trans ht) N hN

theorem source_link_final_probability_budgets
    (t prior geometric forbidden degree quasi xi' : ℝ≥0) (ht : 3 ≤ t)
    (hprior : prior ≤ 1/t^2) (hgeometric : geometric ≤ 1/t^2) (hforbidden : forbidden ≤ 1/t^2)
    (hdegree : degree ≤ 1/t^2) (hquasi : quasi ≤ 1/t^2) (hxi : 6/t ≤ xi') :
    prior+geometric+forbidden ≤ 1/2 ∧ prior+degree+quasi ≤ xi'/2 := by
  have ht1 : 1 ≤ t := (by norm_num : (1 : ℝ≥0) ≤ 3).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hsum : ∀ a b c : ℝ≥0, a ≤ 1/t^2 → b ≤ 1/t^2 → c ≤ 1/t^2 → a+b+c ≤ 3/t^2 := by
    intro a b c ha hb hc
    calc
      _ ≤ 1/t^2+1/t^2+1/t^2 := add_le_add (add_le_add ha hb) hc
      _ = _ := by ring
  constructor
  · apply (hsum prior geometric forbidden hprior hgeometric hforbidden).trans
    apply (div_le_div_iff₀ (pow_pos ht0 2) (by norm_num : (0 : ℝ≥0) < 2)).mpr
    have hh := pow_le_pow_left' ht 2
    norm_num at hh ⊢
    exact (by norm_num : (6 : ℝ≥0) ≤ 9).trans hh
  · apply (hsum prior degree quasi hprior hdegree hquasi).trans
    calc
      3/t^2 ≤ 3/t := div_le_div_of_nonneg_left zero_le ht0
        (by simpa only [pow_one] using pow_le_pow_right₀ ht1 (by norm_num : 1 ≤ 2))
      _ = (6/t)/2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hxi zero_le

end Erdos207
