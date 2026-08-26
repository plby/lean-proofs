import ErdosProblems.Erdos796.MeisselMertensProof
import ErdosProblems.Erdos796.MertensCutoffCertificate

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An explicit upper bound for the Meissel--Mertens constant

This file proves a deliberately modest, fully kernel-checked estimate
`Mertens.M < 933 / 1000`.  The proof cuts the defining integral at `100`.
The finite part is certified by kernel-checked rational inequalities, while
the tail uses only Mathlib's elementary Chebyshev estimate for `psi`.
-/

namespace Erdos796

open Filter Topology Asymptotics
open Real Finset Interval MeasureTheory
open ArithmeticFunction hiding log
open scoped BigOperators

private theorem E₁Λ_le_psi_div {x : ℝ} (hx : 1 ≤ x) :
    Mertens.E₁Λ x ≤ Chebyshev.psi x / x := by
  unfold Mertens.E₁Λ
  have hxpos : 0 < x := by linarith
  suffices
      x * ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d / d ≤
        x * (log x + Chebyshev.psi x / x) by
    linarith [le_of_mul_le_mul_left this hxpos]
  calc
    x * ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d / d =
        ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d * (x / d) := by
          rw [Finset.mul_sum]
          ring_nf
    _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊,
        vonMangoldt d * (⌊x / d⌋₊ + 1) := by
          gcongr
          exact Nat.lt_floor_add_one _ |>.le
    _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) +
        ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d := by
          simp_rw [mul_add, mul_one]
          rw [Finset.sum_add_distrib, Mertens.sum_log_eq_sum_mangoldt]
    _ ≤ x * log x + Chebyshev.psi x := by
          rw [Chebyshev.psi]
          gcongr
          exact Mertens.sum_log_le hx
    _ = x * (log x + Chebyshev.psi x / x) := by field_simp

private theorem E₁p_le_chebyshev {x : ℝ} (hx : 1 ≤ x) :
    Mertens.E₁p x ≤ log 4 + 2 * log x / sqrt x := by
  have hxpos : 0 < x := by linarith
  calc
    Mertens.E₁p x ≤ Mertens.E₁Λ x := Mertens.E₁p.le_E₁Λ x
    _ ≤ Chebyshev.psi x / x := E₁Λ_le_psi_div hx
    _ ≤ (log 4 * x + 2 * sqrt x * log x) / x := by
      gcongr
      exact Chebyshev.psi_le hx
    _ = log 4 + 2 * log x / sqrt x := by
      have hsqrt : 0 < sqrt x := sqrt_pos.2 hxpos
      field_simp [hsqrt.ne']
      ring_nf
      rw [sq_sqrt hxpos.le]

private theorem integral_rpow_neg_three_halves :
    ∫ t : ℝ in Set.Ioi 100, t ^ (-(3 : ℝ) / 2) = 1 / 5 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 100),
    ← Real.sqrt_eq_rpow]

private theorem integrable_tail_majorant :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => log 4 / (t * log t ^ 2) +
        (2 / log 100) * t ^ (-(3 : ℝ) / 2))
      (Set.Ioi 100) MeasureTheory.volume := by
  exact (integrable_const_div_mul_log_sq_clean (log 4) (by norm_num)).add
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul
      (2 / log 100))

private theorem integral_tail_majorant :
    ∫ t : ℝ in Set.Ioi 100,
        (log 4 / (t * log t ^ 2) +
          (2 / log 100) * t ^ (-(3 : ℝ) / 2)) =
      (log 4 + (2 : ℝ) / 5) / log 100 := by
  rw [MeasureTheory.integral_add
    (integrable_const_div_mul_log_sq_clean (log 4) (by norm_num))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul
      (2 / log 100))]
  rw [integ_div_mul_log_sq_clean (log 4) (by norm_num),
    MeasureTheory.integral_const_mul, integral_rpow_neg_three_halves]
  ring

private theorem E₁p_tail_integral_le :
    ∫ t : ℝ in Set.Ioi 100,
        Mertens.E₁p t / (t * log t ^ 2) ≤
      (log 4 + (2 : ℝ) / 5) / log 100 := by
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi 100,
        (log 4 / (t * log t ^ 2) +
          (2 / log 100) * t ^ (-(3 : ℝ) / 2)) := by
      apply MeasureTheory.setIntegral_mono_on
        (integrable_E₁p_div_mul_log_sq_clean (by norm_num))
        integrable_tail_majorant (by measurability)
      intro t ht
      simp only [Set.mem_Ioi] at ht
      have ht0 : 0 < t := by linarith
      have ht1 : 1 ≤ t := by linarith
      have hlog : 0 < log t := log_pos (by linarith)
      have hlog100 : 0 < log 100 := log_pos (by norm_num)
      have hsqrt : 0 < sqrt t := sqrt_pos.2 ht0
      have hden : 0 < t * log t ^ 2 := mul_pos ht0 (sq_pos_of_pos hlog)
      have hE := E₁p_le_chebyshev ht1
      have hfirst :
          Mertens.E₁p t / (t * log t ^ 2) ≤
            (log 4 + 2 * log t / sqrt t) / (t * log t ^ 2) :=
        div_le_div_of_nonneg_right hE hden.le
      have hlogmono : log 100 ≤ log t :=
        log_le_log (by norm_num) ht.le
      have hcoeff : 2 / log t ≤ (2 : ℝ) / log 100 := by
        rw [div_le_div_iff₀ hlog hlog100]
        linarith
      have hrpow : t ^ (-(3 : ℝ) / 2) = 1 / (t * sqrt t) := by
        rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
          Real.rpow_neg ht0.le]
        have hthree : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
        rw [hthree, Real.rpow_add ht0, Real.rpow_one,
          ← Real.sqrt_eq_rpow]
        field
      calc
        Mertens.E₁p t / (t * log t ^ 2) ≤
            (log 4 + 2 * log t / sqrt t) /
              (t * log t ^ 2) := hfirst
        _ = log 4 / (t * log t ^ 2) +
            (2 / log t) * t ^ (-(3 : ℝ) / 2) := by
              rw [hrpow]
              field_simp
        _ ≤ log 4 / (t * log t ^ 2) +
            (2 / log 100) * t ^ (-(3 : ℝ) / 2) := by
              gcongr
    _ = _ := integral_tail_majorant

/-- A fully explicit bound sufficient for the manuscript's rounded
second-order constant. -/
theorem mertensM_lt_933_div_1000 :
    Mertens.M < (933 : ℝ) / 1000 := by
  have hid := E₂p_eq_clean (x := (100 : ℝ)) (by norm_num)
  unfold Mertens.E₂p at hid
  norm_num only [Nat.floor_ofNat] at hid
  have hsum :
      (∑ p ∈ Ioc (0 : ℕ) 100 with p.Prime, (1 : ℝ) / p) =
        primeHarmonic 100 := by
    rw [← primesLE_eq_filter_Ioc]
    simp [primeHarmonic, one_div]
  rw [hsum] at hid
  have hformula :
      Mertens.M =
        primeHarmonic 100 - log (log 100) -
          Mertens.E₁p 100 / log 100 +
          ∫ t : ℝ in Set.Ioi 100,
            Mertens.E₁p t / (t * log t ^ 2) := by
    linarith
  rw [hformula]
  linarith [E₁p_tail_integral_le, finite_cutoff_100_combined_lt]

end Erdos796
