/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoverDownDensityScalars

/-! # A fixed explicit amplification factor for the actual correlated internal law -/

namespace Erdos207

open scoped NNReal

theorem source_correlated_internal_numeric_budget
    (t analytic n inner p eta eta0 constant : ℝ≥0) (c d reserveExp b v L : ℕ)
    (ht : 1 ≤ t) (hinner : 0 < inner) (heta0 : 0 < eta0) (heta01 : eta0 ≤ 1)
    (heta : eta0 ≤ eta) (hconstant : 1 ≤ constant)
    (hpower : t^d ≤ analytic^c) (hp : 1/t^b ≤ p) (hn : t^L ≤ n)
    (hsize : n ≤ t^v*inner) (hgap : 2*reserveExp+v ≤ d) (hreserveGap : reserveExp+1 ≤ d)
    (hpointGap : 2*b+1 ≤ L) (hconstantT : 2*constant ≤ t) (hfactorT : 152*constant/eta0 ≤ t) :
    let r := 1/t^reserveExp
    let mu := r^2*p^2*eta*inner
    let factor := 152*constant/eta0
    let alpha := factor/(p^2*n)
    let survivalBound := (2*constant)/t^d
    1 ≤ factor ∧ 1 ≤ 2*constant ∧ alpha ≤ 1 ∧ survivalBound ≤ 1 ∧ survivalBound ≤ r ∧
      constant*(2/analytic^c) ≤ survivalBound ∧
      constant*(24/(p^2*eta*n))+(constant*(2/analytic^c))*(64/mu) ≤ alpha ∧
      alpha*p^3 ≤ factor*(p/n) := by
  dsimp only
  let r := 1/t^reserveExp
  let mu := r^2*p^2*eta*inner
  let factor := 152*constant/eta0
  let alpha := factor/(p^2*n)
  let survivalBound := (2*constant)/t^d
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp0 : 0 < p := (by positivity : 0 < 1/t^b).trans_le hp
  have hn0 : 0 < n := (pow_pos ht0 L).trans_le hn
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hetaPos : 0 < eta := heta0.trans_le heta
  have hfactor : 1 ≤ factor := by
    apply (le_div_iff₀ heta0).mpr
    calc
      _ ≤ 1 := by simpa only [one_mul] using heta01
      _ ≤ 152*constant := by
        have hm := mul_le_mul_of_nonneg_left hconstant (show (0 : ℝ≥0) ≤ 152 from zero_le)
        exact (by norm_num : (1 : ℝ≥0) ≤ 152).trans (by simpa only [mul_one] using hm)
  have hJ : 1 ≤ 2*constant := by
    have hm := mul_le_mul_of_nonneg_left hconstant (show (0 : ℝ≥0) ≤ 2 from zero_le)
    exact (by norm_num : (1 : ℝ≥0) ≤ 2).trans (by simpa only [mul_one] using hm)
  have halpha : alpha ≤ 1 := inversePower_triangle_point_le_one t p n factor b L ht hp hn hfactorT hpointGap
  have hsurvival : survivalBound ≤ r := preliminary_survival_le_reserve t (2*constant)
    survivalBound reserveExp d ht hconstantT le_rfl hreserveGap
  have hr1 : r ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ ht)
  have hrate : constant*(2/analytic^c) ≤ survivalBound := by
    calc
      _ = (2*constant)/analytic^c := by ring
      _ ≤ _ := div_le_div_of_nonneg_left zero_le (pow_pos ht0 d) hpower
  have hbudget : survivalBound*n ≤ (2*constant)*r^2*inner := by
    simpa only [mul_one, one_mul] using preliminary_survival_reserve_budget t n inner 1 (2*constant)
      survivalBound reserveExp d v ht (by simpa only [one_mul] using hsize) le_rfl hgap
  have hpoint : constant*(24/(p^2*eta*n)) ≤ (24*constant/eta0)/(p^2*n) := by
    calc
      _ = (24*constant/eta)/(p^2*n) := by field_simp
      _ ≤ _ := by gcongr
  have hinternal : 64/mu ≤ (64/eta0)/(r^2*p^2*inner) := by
    dsimp only [mu]
    calc
      _ = (64/eta)/(r^2*p^2*inner) := by field_simp
      _ ≤ _ := by gcongr
  have hcombined := correlated_cover_point_le p r n inner (24*constant/eta0) (64/eta0)
    survivalBound (2*constant) hp0 hr0 hn0 hinner hbudget
  refine ⟨hfactor, hJ, halpha, hsurvival.trans hr1, hsurvival, hrate, ?_, ?_⟩
  · calc
      _ ≤ (24*constant/eta0)/(p^2*n)+survivalBound*((64/eta0)/(r^2*p^2*inner)) :=
        add_le_add hpoint (mul_le_mul hrate hinternal zero_le zero_le)
      _ ≤ ((24*constant/eta0)+(64/eta0)*(2*constant))/(p^2*n) := hcombined
      _ = _ := by ring
  · exact triangle_point_density_cancellation alpha p n factor hp0 hn0 le_rfl

end Erdos207
