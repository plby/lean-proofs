import ErdosProblems.Erdos1141.DivisorLValueComparison
import ErdosProblems.Erdos1141.DivisorErrorScales

/-!
# The divisor-sum asymptotic above the quarter-power scale
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem divisor_comparison_error_le_scales {m X Y : ℕ} (hm : 1 ≤ m) (hX : 0 < X)
    {c a σ : ℝ} (hc : 0 < c) (hXu : (X : ℝ) ≤ (m : ℝ) ^ c)
    (hYu : (Y : ℝ) ≤ 2 * (m : ℝ) ^ a) :
    (Y : ℝ) + (X : ℝ) * (m : ℝ) ^ (-σ) *
        (5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ)) +
      4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) ≤
    2 * (m : ℝ) ^ a + (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) +
      4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hXm : 0 < (X : ℝ) := by exact_mod_cast hX
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hlogXu : Real.log (X : ℝ) ≤ c * Real.log (m : ℝ) := by
    have h := Real.log_le_log hXm hXu
    simpa only [Real.log_rpow hmR] using h
  have hlogR : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log (m : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hfactor : 5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ) ≤
      (7 + 2 * c) * (1 + Real.log (m : ℝ)) := by
    rw [hlogR]
    nlinarith only [hlogXu, hlogm, hc]
  have hfirst : (X : ℝ) * (m : ℝ) ^ (-σ) *
        (5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ)) ≤
      (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) := by
    have hxpow : (X : ℝ) * (m : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (c - σ) := by
      rw [sub_eq_add_neg, Real.rpow_add hmR]
      exact mul_le_mul_of_nonneg_right hXu (Real.rpow_nonneg hmR.le _)
    have hfac0 : 0 ≤ 5 + 2 * Real.log (X : ℝ) + Real.log ((m ^ 2 : ℕ) : ℝ) := by
      rw [hlogR]
      positivity
    calc
      _ ≤ (m : ℝ) ^ (c - σ) * ((7 + 2 * c) * (1 + Real.log (m : ℝ))) :=
        mul_le_mul hxpow hfactor hfac0 (Real.rpow_nonneg hmR.le _)
      _ = _ := by ring
  have hratio : (m : ℝ) ^ c * Real.sqrt (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) =
      (m : ℝ) ^ (c - 3 / 2) := by
    rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_add hmR,
      ← Real.rpow_natCast, ← Real.rpow_sub hmR]
    congr 1
    ring
  have hsecond : 4 * (X : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) ≤
      4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) := by
    calc
      _ ≤ 4 * (m : ℝ) ^ c * Real.sqrt (m : ℝ) * Real.log (m : ℝ) / ((m ^ 2 : ℕ) : ℝ) := by
        gcongr
      _ = 4 * (m : ℝ) ^ (c - 3 / 2) * Real.log (m : ℝ) := by
        rw [← hratio]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact add_le_add (add_le_add hYu hfirst) hsecond

theorem eventually_divisor_sum_asymptotic {c : ℝ} (hc : 1 / 4 < c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ [NeZero m] (χ : DirichletCharacter ℂ m), χ.IsQuadratic → χ ≠ 1 →
        |(∑ n ∈ Finset.Icc 1 ⌊(m : ℝ) ^ c⌋₊, divisorCoefficient χ n) -
          (⌊(m : ℝ) ^ c⌋₊ : ℝ) * (DirichletCharacter.LFunction χ 1).re| ≤ (m : ℝ) ^ (c - τ) := by
  let a : ℝ := min ((c + 1 / 4) / 2) (1 / 2)
  have ha : 1 / 4 < a := by dsimp [a]; exact lt_min (by linarith) (by norm_num)
  have hac : a < c := (min_le_left _ _).trans_lt (by linarith)
  have ha2 : a < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨σ, hσ, hprefix⟩ := eventually_quadratic_prefix_bound ha
  obtain ⟨τ, hτ, herror⟩ := eventually_divisor_error_le hc0 hac hσ
  have hYX := Burgess.eventually_const_mul_rpow_le (C := 2) (d := 1 / 2) (by norm_num) hac
  have hYR := Burgess.eventually_const_mul_rpow_le (C := 2) (d := 1) (by norm_num) ha2
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hprefix, herror, hYX, hYR, Burgess.eventually_floor_rpow_bounds hc0,
    eventually_ge_atTop 2] with m hpref herr hYX hYR hfloor hm
  intro _ χ hχ hχ1
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  let X := ⌊(m : ℝ) ^ c⌋₊
  let Y := ⌈(m : ℝ) ^ a⌉₊
  have hceil := Burgess.ceil_rpow_bounds ha0.le (show 1 ≤ m by omega)
  have hXpos : 0 < X := by
    have h : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hfloor.1
    exact_mod_cast h
  have hYpos : 0 < Y := by
    have h : (0 : ℝ) < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hmR a) hceil.1
    exact_mod_cast h
  have hYX' : Y ≤ X := by
    have hmid : 2 * (m : ℝ) ^ a ≤ (m : ℝ) ^ c / 2 := by
      nlinarith only [hYX]
    have h : (Y : ℝ) ≤ X := hceil.2.trans (hmid.trans hfloor.1)
    exact_mod_cast h
  have hYR' : Y ≤ m ^ 2 := by
    have h : (Y : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by
      have h := hceil.2.trans hYR
      simpa only [one_mul, Real.rpow_two, Nat.cast_pow] using h
    exact_mod_cast h
  have hb : 0 ≤ (m : ℝ) ^ (-σ) := Real.rpow_nonneg hmR.le _
  have hbound (n : ℕ) (hn : Y ≤ n) :
      |∑ d ∈ Finset.Icc 1 n, (χ (d : ℕ)).re| ≤ (n : ℝ) * (m : ℝ) ^ (-σ) :=
    hpref χ hχ hχ1 n (hceil.1.trans (by exact_mod_cast hn))
  have hcomp := abs_divisor_sum_sub_LFunction_main_le
    (by omega) χ hχ hχ1 hYpos hYX' hYR' hb hbound
  exact (hcomp.trans (divisor_comparison_error_le_scales
    (by omega) hXpos hc0 hfloor.2 hceil.2)).trans herr

end Pollack17
