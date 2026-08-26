import ErdosProblems.Erdos67.StationaryEntropy
import Mathlib.Analysis.PSeries

/-!
# Harmonic averages and translation

The total-variation estimate for translating a harmonic average follows from a
finite summation-by-parts identity. Its error tends to zero by divergence of the
harmonic series.
-/

open scoped BigOperators Topology
open Finset Filter

namespace Erdos67.StationaryHarmonicAverage

noncomputable def mass (t : ℕ) : ℝ := ∑ n ∈ range t, ((n + 1 : ℕ) : ℝ)⁻¹

noncomputable def average (t : ℕ) (F : ℕ → ℝ) : ℝ :=
  (∑ n ∈ range t, ((n + 1 : ℕ) : ℝ)⁻¹ * F (n + 1)) / mass t

theorem mass_pos {t : ℕ} (ht : 0 < t) : 0 < mass t := by
  apply Finset.sum_pos'
  · intro n _
    positivity
  · exact ⟨0, Finset.mem_range.mpr ht, by norm_num⟩

theorem tendsto_mass_atTop : Tendsto mass atTop atTop := by
  unfold mass
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem tendsto_inv_mass : Tendsto (fun t ↦ (mass t)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_mass_atTop

/-- Discrete integration by parts, with both boundary terms displayed. -/
theorem weighted_difference_identity (w F : ℕ → ℝ) (t : ℕ) :
    (∑ n ∈ range (t + 1), w n * (F (n + 1) - F n)) =
      w t * F (t + 1) - w 0 * F 0 +
        ∑ n ∈ range t, (w n - w (n + 1)) * F (n + 1) := by
  induction t with
  | zero => simp [mul_sub]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem sum_weight_differences (w : ℕ → ℝ) (t : ℕ) :
    (∑ n ∈ range t, (w n - w (n + 1))) = w 0 - w t := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_range_succ, ih]; ring

theorem abs_weighted_difference_le (w F : ℕ → ℝ) (B : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hdec : ∀ n, w (n + 1) ≤ w n)
    (hF : ∀ n, |F n| ≤ B) (t : ℕ) :
    |∑ n ∈ range (t + 1), w n * (F (n + 1) - F n)| ≤ 2 * B * w 0 := by
  rw [weighted_difference_identity]
  have hterm (n : ℕ) : |(w n - w (n + 1)) * F (n + 1)| ≤
      (w n - w (n + 1)) * B := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hdec n))]
    exact mul_le_mul_of_nonneg_left (hF _) (sub_nonneg.mpr (hdec n))
  have hsum : |∑ n ∈ range t, (w n - w (n + 1)) * F (n + 1)| ≤
      (w 0 - w t) * B := by
    calc
      |∑ n ∈ range t, (w n - w (n + 1)) * F (n + 1)| ≤
          ∑ n ∈ range t, |(w n - w (n + 1)) * F (n + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range t, (w n - w (n + 1)) * B :=
        Finset.sum_le_sum fun n _ ↦ hterm n
      _ = (w 0 - w t) * B := by rw [← Finset.sum_mul, sum_weight_differences]
  have hend (n : ℕ) (m : ℕ) : |w n * F m| ≤ w n * B := by
    rw [abs_mul, abs_of_nonneg (hw n)]
    exact mul_le_mul_of_nonneg_left (hF m) (hw n)
  have hfirst := abs_add_le (w t * F (t + 1) - w 0 * F 0)
    (∑ n ∈ range t, (w n - w (n + 1)) * F (n + 1))
  have hsecond := abs_sub (w t * F (t + 1)) (w 0 * F 0)
  nlinarith [hend t (t + 1), hend 0 0]

/-- Translation changes a harmonic average by at most `2B/H_t`. -/
theorem abs_average_shift_sub_le {t : ℕ} (ht : 0 < t) (F : ℕ → ℝ) (B : ℝ)
    (hF : ∀ n, |F n| ≤ B) :
    |average t (fun n ↦ F (n + 1)) - average t F| ≤ 2 * B / mass t := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have h := abs_weighted_difference_le (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹)
    (fun n ↦ F (n + 1)) B (fun _ ↦ by positivity)
    (fun n ↦ by
      apply inv_anti₀ (by positivity)
      exact_mod_cast (by omega : n + 1 ≤ n + 1 + 1))
    (fun n ↦ hF (n + 1)) s
  simp only [Nat.zero_add, Nat.cast_one, inv_one, mul_one] at h
  unfold average
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [abs_div, abs_of_pos (mass_pos (Nat.succ_pos s))]
  exact div_le_div_of_nonneg_right h (mass_pos (Nat.succ_pos s)).le

theorem tendsto_translation_error_bound (B : ℝ) :
    Tendsto (fun t ↦ 2 * B / mass t) atTop (nhds 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul
    tendsto_inv_mass (a := 2 * B)

end Erdos67.StationaryHarmonicAverage
