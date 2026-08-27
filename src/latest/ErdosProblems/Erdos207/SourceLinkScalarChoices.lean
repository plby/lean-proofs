/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredLinkSamplingScalars
import ErdosProblems.Erdos207.SourceLinkRoundedCaps

/-! # Fixed explicit integer choices for the source matching and deletion budgets -/

namespace Erdos207

open Finset
open scoped NNReal

theorem exists_source_link_rounding (x : ℝ≥0) (hx : 80 ≤ x) :
    ∃ c degree : ℕ, (c : ℝ≥0) ≤ x/40 ∧ x/80 ≤ c ∧
      2*x ≤ degree ∧ (degree : ℝ≥0) ≤ 3*x := by
  have hxR : (80 : ℝ) ≤ x := by exact_mod_cast hx
  have hfloor := floor_reference_hall_coefficient (x : ℝ) 1 (by simpa only [one_mul] using hxR)
  dsimp only at hfloor
  simp only [one_mul] at hfloor
  obtain ⟨degree, hdegree, hupper⟩ := exists_rounded_link_degree (x : ℝ) (by linarith only [hxR])
  refine ⟨⌊(x : ℝ)/40⌋₊, degree, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hfloor.1
  · exact_mod_cast hfloor.2
  · exact_mod_cast hdegree
  · exact_mod_cast hupper

theorem source_link_fixed_caps_budget (orders : Finset ℕ) (t : ℕ) :
    let cap := ⌊3*(t : ℝ≥0)/(orders.card+1 : ℝ≥0)⌋₊
    (∑ _j ∈ orders, (cap : ℝ≥0)) ≤ 3*t ∧
      (3/(orders.card+1 : ℝ≥0))*(t : ℝ≥0) ≤ cap+1 ∧
      ((2*t+∑ _j ∈ orders, cap)+t : ℕ) ≤ (6*(t : ℝ≥0)) := by
  dsimp only
  have hbudget := source_link_uniform_cap_budget orders 3 (t : ℝ≥0)
  refine ⟨hbudget.1, ?_, ?_⟩
  · have heq : (3/(orders.card+1 : ℝ≥0))*(t : ℝ≥0) = 3*(t : ℝ≥0)/(orders.card+1 : ℝ≥0) := by ring
    rw [heq]
    exact hbudget.2
  · push_cast
    have hh := hbudget.1
    calc
      _ ≤ (2:ℝ≥0)*t+3*t+t := add_le_add (add_le_add le_rfl hh) le_rfl
      _ = _ := by ring

theorem source_link_fixed_hall_budget
    (orders : Finset ℕ) (t : ℕ) (r p eta eta0 u : ℝ≥0) (c : ℕ)
    (hr : 0 < r) (hp : 0 < p) (hu : 0 < u) (heta0 : 0 < eta0) (heta : eta0 ≤ eta)
    (hc : r*p^2*eta*u/80 ≤ c) :
    let a := (1920/eta0)*(t : ℝ≥0)
    let cap := ⌊3*(t : ℝ≥0)/(orders.card+1 : ℝ≥0)⌋₊
    let Delta := 2*t+∑ _j ∈ orders, cap
    (Delta+t : ℝ≥0) ≤ (a/(r*p^2*u))*c/2 := by
  dsimp only
  apply link_reference_sampled_hall_budget ((1920/eta0)*(t : ℝ≥0)) r p eta u c
    (2*t+∑ _j ∈ orders, ⌊3*(t : ℝ≥0)/(orders.card+1 : ℝ≥0)⌋₊) t hr hp hu hc
  calc
    _ ≤ 6*(t : ℝ≥0) := by
      simpa only [Nat.cast_add] using (source_link_fixed_caps_budget orders t).2.2
    _ ≤ 12*(t : ℝ≥0) := mul_le_mul_of_nonneg_right (by norm_num : (6:ℝ≥0) ≤ 12) zero_le
    _ = ((1920/eta0)*(t : ℝ≥0))*eta0/160 := by field_simp; ring
    _ ≤ _ := by gcongr

theorem source_link_collision_power_budget
    (t n u A a r p degree overlap sigma : ℝ≥0) (reserveExp b v : ℕ)
    (ht : 1 ≤ t) (hr0 : 0 < r) (hu : 0 < u)
    (ha : a ≤ A*t) (hr : r ≤ 1/t^reserveExp) (hp : 1/t^b ≤ p)
    (hsize : n ≤ t^v*u) (hgap : v+2*b+4 ≤ reserveExp)
    (hdegree : degree ≤ 3*r*p^2*u) (hoverlap : overlap ≤ (2*t)*r^2*n)
    (hsigma : sigma ≤ a/(r*p^2*u)) (hthreshold : 24*A^2 ≤ t) :
    4*degree*overlap*sigma^2 ≤ 2*t+1 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < p := (by positivity : 0 < 1/t^b).trans_le hp
  have hmean := link_collision_mean_cancellation degree overlap sigma 3 (2*t) a r p n u
    hr0 hp0 hu hdegree hoverlap hsigma
  have hpower := link_collision_mean_power_decay t n u 1 A a r p 1 reserveExp b v 2
    ht hu (by simpa only [pow_one] using ha) hr hp (by simpa only [one_mul] using hsize) (by omega)
  calc
    _ = 4*(degree*overlap*sigma^2) := by ring
    _ ≤ 4*(3*(2*t)*(a^2*r*n/(p^2*u))) := mul_le_mul_of_nonneg_left hmean zero_le
    _ ≤ 4*(3*(2*t)*((A^2*1)/t^2)) := by gcongr
    _ = 24*A^2/t := by field_simp; ring
    _ ≤ 1 := (div_le_one ht0).mpr hthreshold
    _ ≤ _ := le_add_of_nonneg_left zero_le

theorem source_link_future_degree_ratio_power
    (t n u A a r p eta eta0 epsilon epsilon0 overlap sigma : ℝ≥0)
    (reserveExp b v h : ℕ) (ht : 1 ≤ t) (hr0 : 0 < r) (hu : 0 < u)
    (heta0 : 0 < eta0) (hepsilon0 : 0 < epsilon0)
    (ha : a ≤ A*t) (hr : r ≤ 1/t^reserveExp) (hp : 1/t^b ≤ p)
    (heta : eta0 ≤ eta) (hepsilon : epsilon0/t ≤ epsilon)
    (hsize : n ≤ t^v*u) (hgap : v+b*(h+2)+4 ≤ reserveExp)
    (hoverlap : overlap+1 ≤ (3*t)*r^2*n) (hsigma : sigma ≤ a/(r*p^2*u)) :
    2*(overlap+1)*sigma/(epsilon*p^h*eta^(h^2)) ≤ (6*A/(epsilon0*eta0^(h^2)))/t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < p := (by positivity : 0 < 1/t^b).trans_le hp
  have hetaPos : 0 < eta := heta0.trans_le heta
  have hepsilonPos : 0 < epsilon := (by positivity : 0 < epsilon0/t).trans_le hepsilon
  have hmean := link_inner_edge_mean_cancellation (overlap+1) sigma (3*t) a r p n u
    hr0 hp0 hu hoverlap hsigma
  have hpower := link_inner_edge_density_power_decay t n u 1 A a r p
    1 reserveExp b v h 3 ht hu (by simpa only [pow_one] using ha) hr hp
    (by simpa only [one_mul] using hsize) (by omega)
  calc
    _ = 2*((overlap+1)*sigma)/(epsilon*p^h*eta^(h^2)) := by ring
    _ ≤ 2*((3*t)*(a*r*n/(p^2*u)))/(epsilon*p^h*eta^(h^2)) := by gcongr
    _ = (6*t/(epsilon*eta^(h^2)))*(a*r*n/(p^(h+2)*u)) := by
      rw [pow_add]
      field_simp
      ring
    _ ≤ (6*t/((epsilon0/t)*eta0^(h^2)))*((A*1)/t^3) := by gcongr
    _ = _ := by field_simp

end Erdos207
