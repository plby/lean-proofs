import ErdosProblems.Erdos4.OuterLogBounds

/-!
# Uniform comparison with Erdős's original threshold

The third iterated logarithm is not replaced by a fixed lower bound at
large indices. Splitting at `log n = t²⁵` keeps its full squared saving,
and gives a fixed multiple of `X V r` uniformly over the CRT range.
-/

open Filter
open scoped Topology

namespace Erdos4.OuterThreshold

open SmoothParameters OuterRay OuterAccuracy OuterLogBounds

noncomputable def coefficient (C : ℝ) (a : ℕ) : ℝ :=
  800 * C + 2400 * C * (2 : ℝ) ^ a / Real.log 2 ^ 2

theorem coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (a : ℕ) : 0 ≤ coefficient C a := by
  unfold coefficient
  positivity

theorem threshold_le {C : ℝ} (hC : 0 ≤ C) {a r n : ℕ} (hra : a ≤ r) (hr : 4 ≤ r)
    (h₁ : 1 ≤ Real.log (n : ℝ)) (h₂ : 1 ≤ Real.log (Real.log (n : ℝ)))
    (h₃ : 1 ≤ Real.log (Real.log (Real.log (n : ℝ))))
    (hupper : Real.log (n : ℝ) ≤ 3 * frontier a r) :
    Erdos4.threshold C n ≤ coefficient C a * ((frontier a r : ℝ) * core r * r) := by
  have hlogs := upper_logs hra hr h₁ h₂ h₃ hupper
  have h₄ : 0 ≤ Real.log (Real.log (Real.log (Real.log (n : ℝ)))) := Real.log_nonneg h₃
  have hl₁ : 0 ≤ Real.log (n : ℝ) := by linarith
  have hl₂ : 0 ≤ Real.log (Real.log (n : ℝ)) := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnum : C * Real.log (Real.log (n : ℝ)) *
      Real.log (Real.log (Real.log (Real.log (n : ℝ)))) ≤
      C * (100 * primaryExponent a r) * (8 * r) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlogs.1 hC) hlogs.2 h₄ (by positivity)
  have hscale : 0 ≤ (frontier a r : ℝ) * core r * r := by positivity
  by_cases hsmall : Real.log (n : ℝ) ≤ (primaryFrontier a r : ℝ) ^ 25
  · have hquot : C * Real.log (Real.log (n : ℝ)) *
        Real.log (Real.log (Real.log (Real.log (n : ℝ)))) /
          Real.log (Real.log (Real.log (n : ℝ))) ^ 2 ≤
        C * (100 * primaryExponent a r) * (8 * r) :=
      (div_le_self (by positivity) (one_le_pow₀ h₃)).trans hnum
    have hraw := mul_le_mul hquot hsmall hl₁ (by positivity)
    have hnat : primaryFrontier a r ^ 25 * primaryExponent a r ≤ frontier a r * core r := by
      calc
        _ ≤ primaryFrontier a r ^ 25 * primaryFrontier a r :=
          Nat.mul_le_mul_left _ (primaryExponent_le_primary a r)
        _ = primaryFrontier a r ^ 26 := (pow_succ (primaryFrontier a r) 25).symm
        _ ≤ base a r := Nat.pow_le_pow_right (primaryFrontier_pos a r) (by norm_num)
        _ ≤ frontier a r := base_le_frontier a r
        _ ≤ frontier a r * core r := by
          simpa using Nat.mul_le_mul_left (frontier a r) (show 1 ≤ core r from core_pos r)
    have hsmallE : (primaryFrontier a r : ℝ) ^ 25 * primaryExponent a r ≤
        (frontier a r : ℝ) * core r := by exact_mod_cast hnat
    have hh := mul_le_mul_of_nonneg_left hsmallE (by positivity : 0 ≤ 800 * C * (r : ℝ))
    have hbound : Erdos4.threshold C n ≤ (800 * C) * ((frontier a r : ℝ) * core r * r) := by
      unfold Erdos4.threshold
      nlinarith only [hraw, hh]
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right _ hscale
    unfold coefficient
    exact le_add_of_nonneg_right (by positivity)
  · have hlo := lower_third_log (le_of_not_ge hsmall)
    have hden : ((2 : ℝ) ^ r * Real.log 2) ^ 2 ≤
        Real.log (Real.log (Real.log (n : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlo 2
    have hquot : C * Real.log (Real.log (n : ℝ)) *
        Real.log (Real.log (Real.log (Real.log (n : ℝ)))) /
          Real.log (Real.log (Real.log (n : ℝ))) ^ 2 ≤
        C * (100 * primaryExponent a r) * (8 * r) / ((2 : ℝ) ^ r * Real.log 2) ^ 2 := by
      exact (div_le_div_of_nonneg_right hnum (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
    have hraw := mul_le_mul hquot hupper hl₁ (by positivity)
    have heq : C * (100 * primaryExponent a r) * (8 * r) /
        ((2 : ℝ) ^ r * Real.log 2) ^ 2 * (3 * frontier a r) =
        (2400 * C * (2 : ℝ) ^ a / Real.log 2 ^ 2) * ((frontier a r : ℝ) * core r * r) := by
      rw [exponent_ratio]
      field_simp
      ring
    have hbound : Erdos4.threshold C n ≤
        (2400 * C * (2 : ℝ) ^ a / Real.log 2 ^ 2) * ((frontier a r : ℝ) * core r * r) :=
      hraw.trans_eq heq
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right _ hscale
    unfold coefficient
    have hh : 0 ≤ 800 * C := by positivity
    linarith

theorem exists_log_start :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 0 < n ∧
      1 ≤ Real.log (n : ℝ) ∧ 1 ≤ Real.log (Real.log (n : ℝ)) ∧
      1 ≤ Real.log (Real.log (Real.log (n : ℝ))) := by
  have h₁ := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₂ := Real.tendsto_log_atTop.comp h₁
  have h₃ := Real.tendsto_log_atTop.comp h₂
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop 1, h₁.eventually (eventually_ge_atTop 1),
    h₂.eventually (eventually_ge_atTop 1), h₃.eventually (eventually_ge_atTop 1)] with n hn hl₁ hl₂ hl₃
  exact ⟨hn, hl₁, hl₂, hl₃⟩

theorem log_primorial_le_two (X : ℕ) : Real.log (primorial X : ℝ) ≤ 2 * X := by
  have hh := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right log_two_bounds.2 (Nat.cast_nonneg X : (0 : ℝ) ≤ X)])

theorem eventually_log_endpoint (a L : ℕ) (hL : 0 < L) :
    ∀ᶠ r : ℕ in atTop, ∀ n : ℕ, 0 < n → n ≤ L * primorial (frontier a r) →
      Real.log (n : ℝ) ≤ 3 * frontier a r := by
  have hXtop : Tendsto (fun r : ℕ => (frontier a r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_frontier a)
  filter_upwards [hXtop.eventually (eventually_ge_atTop (Real.log L))] with r hr
  intro n hn hnupper
  have hh := Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n)
    (by exact_mod_cast hnupper : (n : ℝ) ≤ (L * primorial (frontier a r) : ℕ))
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hL.ne')
    (by exact_mod_cast (primorial_pos (frontier a r)).ne')] at hh
  have hprim := log_primorial_le_two (frontier a r)
  linarith

end Erdos4.OuterThreshold
