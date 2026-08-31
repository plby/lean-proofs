import ErdosProblems.Erdos1141.QuadraticCoefficients
import ErdosProblems.Erdos1141.BurgessEnergyArithmetic
import BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# A truncated hyperbola estimate for quadratic divisor coefficients
-/

namespace Pollack17

open scoped BigOperators
open BoundedGaps.Maynard

theorem divisor_sum_hyperbola (f : ℕ → ℝ) {X Y : ℕ} (hYX : Y ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d) =
      (∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) +
        ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (positiveFactorPairs X)
    (fun p : ℕ × ℕ => p.1 ≤ Y) (fun p => f p.1)
  have hsmall : (∑ p ∈ (positiveFactorPairs X).filter (fun p => p.1 ≤ Y), f p.1) =
      ∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d := by
    rw [sum_positiveFactorPairs_filter_fst_eq_sum_multipliers (fun d => d ≤ Y) (fun d _ => f d)]
    have hset : (Finset.Ioc 0 X).filter (fun d => d ≤ Y) = Finset.Icc 1 Y := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
    simp
  have hlarge : (∑ p ∈ (positiveFactorPairs X).filter (fun p => ¬p.1 ≤ Y), f p.1) =
      ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d := by
    rw [Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩)
    · intro p hp
      obtain ⟨hp, hY⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp, hprod⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      have ha := Finset.mem_Ioc.mp ha
      have hb := Finset.mem_Ioc.mp hb
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr hb,
        Finset.mem_Ioc.mpr ⟨by change Y < p.1; omega, (Nat.le_div_iff_mul_le hb.1).mpr hprod⟩⟩
    · intro p _ p' _ h
      exact Prod.ext (congrArg Sigma.snd h) (congrArg Sigma.fst h)
    · rintro ⟨a, d⟩ h
      obtain ⟨ha, hd⟩ := Finset.mem_sigma.mp h
      have ha := Finset.mem_Icc.mp ha
      have hd := Finset.mem_Ioc.mp hd
      dsimp only [Sigma.fst, Sigma.snd] at ha hd
      refine ⟨(d, a), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, by simpa using not_le.mpr hd.1⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,
        hd.2.trans (Nat.div_le_self _ _)⟩, Finset.mem_Ioc.mpr ha⟩,
        (Nat.le_div_iff_mul_le ha.1).mp hd.2⟩
    · intro p _
      rfl
  calc
    _ = ∑ n ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors, f d := by
      rw [show Finset.Icc 1 X = Finset.Ioc 0 X by ext n; simp; omega]
    _ = ∑ p ∈ positiveFactorPairs X, f p.1 := sum_divisors_up_to_eq_sum_positiveFactorPairs _
    _ = _ := by rw [← hsplit, hsmall, hlarge]

theorem abs_truncated_floor_error_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (X Y : ℕ) :
    |(∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) -
      (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)| ≤ Y := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 Y,
        |((X / d : ℕ) : ℝ) * f d - (X : ℝ) * (f d / (d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 Y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have heq : ((X / d : ℕ) : ℝ) * f d - (X : ℝ) * (f d / (d : ℝ)) =
          (((X / d : ℕ) : ℝ) - (X : ℝ) / d) * f d := by ring
      rw [heq, abs_mul]
      have hfloor : |((X / d : ℕ) : ℝ) - (X : ℝ) / d| ≤ 1 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
        have h := Nat.lt_floor_add_one ((X : ℝ) / d)
        rw [Nat.floor_div_eq_div] at h
        linarith
      exact (mul_le_mul hfloor (hf d) (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    _ = _ := by simp

theorem abs_hyperbola_tail_le (f : ℕ → ℝ) {X Y : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n →
      |∑ d ∈ Finset.Icc 1 n, f d| ≤ (n : ℝ) * b) :
    |∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d| ≤
      2 * (X : ℝ) * b * (1 + Real.log (X : ℝ)) := by
  have hterm (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      |∑ d ∈ Finset.Ioc Y (X / a), f d| ≤ 2 * (X : ℝ) * b * (a : ℝ)⁻¹ := by
    by_cases hN : Y ≤ X / a
    · have heq : (∑ d ∈ Finset.Ioc Y (X / a), f d) =
          (∑ d ∈ Finset.Icc 1 (X / a), f d) - ∑ d ∈ Finset.Icc 1 Y, f d := by
        rw [show Finset.Icc 1 (X / a) = Finset.Ioc 0 (X / a) by ext n; simp; omega,
          show Finset.Icc 1 Y = Finset.Ioc 0 Y by ext n; simp; omega,
          ← Finset.sum_Ioc_consecutive f (Nat.zero_le Y) hN]
        ring
      rw [heq]
      calc
        _ ≤ |∑ d ∈ Finset.Icc 1 (X / a), f d| + |∑ d ∈ Finset.Icc 1 Y, f d| := by
          simpa only [Real.norm_eq_abs] using norm_sub_le
            (∑ d ∈ Finset.Icc 1 (X / a), f d) (∑ d ∈ Finset.Icc 1 Y, f d)
        _ ≤ ((X / a : ℕ) : ℝ) * b + (Y : ℝ) * b :=
          add_le_add (hprefix _ hN) (hprefix _ le_rfl)
        _ ≤ 2 * (((X / a : ℕ) : ℝ) * b) := by
          have h := mul_le_mul_of_nonneg_right (show (Y : ℝ) ≤ (X / a : ℕ) by exact_mod_cast hN) hb
          linarith
        _ ≤ 2 * ((X : ℝ) / a * b) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right Nat.cast_div_le hb) (by norm_num)
        _ = _ := by ring
    · rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.sum_empty, abs_zero]
      positivity
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 X, |∑ d ∈ Finset.Ioc Y (X / a), f d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X, 2 * (X : ℝ) * b * (a : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (2 * (X : ℝ) * b) * ∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Burgess.sum_Icc_inv_natCast_le_one_add_log X) (by positivity)

theorem abs_divisor_sum_sub_truncated_main_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {X Y : ℕ} (hYX : Y ≤ X) {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, Y ≤ n → |∑ d ∈ Finset.Icc 1 n, f d| ≤ (n : ℝ) * b) :
    |(∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)| ≤
      (Y : ℝ) + 2 * (X : ℝ) * b * (1 + Real.log (X : ℝ)) := by
  rw [divisor_sum_hyperbola f hYX]
  have heq : (∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) +
      (∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ) =
      ((∑ d ∈ Finset.Icc 1 Y, ((X / d : ℕ) : ℝ) * f d) -
        (X : ℝ) * ∑ d ∈ Finset.Icc 1 Y, f d / (d : ℝ)) +
        (∑ a ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Ioc Y (X / a), f d) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (abs_truncated_floor_error_le f hf X Y)
    (abs_hyperbola_tail_le f hb hprefix))

end Pollack17
