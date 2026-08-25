import Util.Bernays.SmoothedFunctional
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Splitting the logarithmic kernel at the square root of the endpoint
-/

open Set Filter Topology MeasureTheory
open scoped Classical

namespace Bernays

noncomputable def normUpperPart (a : ℕ → ℂ) (u : ℝ) (n : ℕ) : ℂ :=
  if u ≤ (n : ℝ) then a n else 0

noncomputable def normLowerPart (a : ℕ → ℂ) (u : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ) < u then a n else 0

theorem cheby_of_norm_le {a b : ℕ → ℂ} (hb : cheby b) (h : ∀ n : ℕ, ‖a n‖ ≤ ‖b n‖) :
    cheby a := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, fun N => (Finset.sum_le_sum (fun n _ => h n)).trans (hC N)⟩

theorem normUpperPart_norm_le (a : ℕ → ℂ) (u : ℝ) (n : ℕ) :
    ‖normUpperPart a u n‖ ≤ ‖a n‖ := by
  unfold normUpperPart
  split_ifs <;> simp

theorem normLowerPart_norm_le (a : ℕ → ℂ) (u : ℝ) (n : ℕ) :
    ‖normLowerPart a u n‖ ≤ ‖a n‖ := by
  unfold normLowerPart
  split_ifs <;> simp

theorem logarithmicKernelMass_split {a : ℕ → ℂ} (ha : cheby a) (u : ℝ) {x : ℝ} (hx : 0 < x) :
    logarithmicKernelMass a x = logarithmicKernelMass (normLowerPart a u) x +
      logarithmicKernelMass (normUpperPart a u) x := by
  have h₀ := cheby_of_norm_le ha (normLowerPart_norm_le a u)
  have h₁ := cheby_of_norm_le ha (normUpperPart_norm_le a u)
  rw [logarithmicKernelMass, logarithmicKernelMass, logarithmicKernelMass,
    ← (logarithmicKernelMass_summable h₀ hx).tsum_add (logarithmicKernelMass_summable h₁ hx)]
  apply tsum_congr
  intro n
  by_cases h : (n : ℝ) < u
  · simp only [normLowerPart, normUpperPart, h, not_le.mpr h, ↓reduceIte, norm_zero,
      zero_div, zero_mul, add_zero]
  · simp only [normLowerPart, normUpperPart, h, le_of_not_gt h, ↓reduceIte, norm_zero,
      zero_div, zero_mul, zero_add]

theorem sqrt_log_le_twice_sqrt_log {x y : ℝ} (hx : 1 ≤ x) (hy : Real.sqrt x ≤ y) :
    Real.sqrt (Real.log x) ≤ 2 * Real.sqrt (Real.log y) := by
  have hx₀ := zero_lt_one.trans_le hx
  have hy₀ := (Real.sqrt_pos.mpr hx₀).trans_le hy
  have hl := Real.log_le_log (Real.sqrt_pos.mpr hx₀) hy
  rw [Real.log_sqrt hx₀.le] at hl
  have hxL := Real.log_nonneg hx
  have hyL : 0 ≤ Real.log y := by linarith
  have hsx := Real.sq_sqrt hxL
  have hsy := Real.sq_sqrt hyL
  nlinarith [Real.sqrt_nonneg (Real.log x), Real.sqrt_nonneg (Real.log y)]

theorem normUpperPart_cheby_logBound {a : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {x : ℝ} (hx : 1 < x) :
    chebyWith (2 * C / Real.sqrt (Real.log x)) (normUpperPart a (Real.sqrt x)) := by
  intro N
  by_cases hN : (N : ℝ) ≤ Real.sqrt x
  · have hzero : cumsum (fun n => ‖normUpperPart a (Real.sqrt x) n‖) N = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnR : (n : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hn
      simp only [normUpperPart, if_neg (not_le.mpr (hnR.trans_le hN)), norm_zero]
    rw [hzero]
    positivity
  · have hsx := Real.sqrt_pos.mpr (Real.log_pos hx)
    have hden : 0 < 1 + Real.sqrt (Real.log (N : ℝ)) := by positivity
    have hlog := sqrt_log_le_twice_sqrt_log hx.le (le_of_not_ge hN)
    apply (Finset.sum_le_sum (fun n _ => normUpperPart_norm_le a (Real.sqrt x) n)).trans
    apply (hcount N).trans
    have hscalar : C / (1 + Real.sqrt (Real.log (N : ℝ))) ≤ 2 * C / Real.sqrt (Real.log x) := by
      apply (div_le_div_iff₀ hden hsx).mpr
      have hmul := mul_le_mul_of_nonneg_left hlog hC
      nlinarith
    calc
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))) =
          (C / (1 + Real.sqrt (Real.log (N : ℝ)))) * N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg N)

end Bernays
