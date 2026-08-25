import Mathlib

/-!
# Reciprocal sums from a linear prefix bound
-/

open scoped BigOperators

namespace Erdos1141

lemma sum_range_succ_eq_Icc_of_zero (f : ℕ → ℂ) (hf0 : f 0 = 0) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) = ∑ i ∈ Finset.Icc 1 n, f i := by
  rw [Nat.range_succ_eq_Icc_zero, Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
  simpa [hf0] using congrArg (fun s : Finset ℕ ↦ ∑ i ∈ s, f i)
    (Finset.Icc_add_one_left_eq_Ioc 0 n).symm

lemma norm_inv_succ_sub_inv (n : ℕ) (hn : 0 < n) :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ - (n : ℂ)⁻¹‖ =
      (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : ((n + 1 : ℕ) : ℂ)⁻¹ - (n : ℂ)⁻¹ =
      (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ : ℝ) := by push_cast; rfl
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
  · ring
  · exact sub_nonpos.mpr (inv_anti₀ hnr (by norm_num))

theorem norm_reciprocal_interval_le_of_linear_prefix
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (K : ℝ) (hK : 0 ≤ K)
    (D M : ℕ) (hD : 0 < D) (hDM : D ≤ M)
    (hprefix : ∀ N : ℕ, D ≤ N → ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ (N : ℝ) * K) :
    ‖∑ n ∈ Finset.Ioc D M, f n / n‖ ≤ K * (3 + Real.log (M : ℝ)) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hMr : (0 : ℝ) < M := by exact_mod_cast hD.trans_le hDM
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hD.trans_le hDM)
  rcases hDM.eq_or_lt with rfl | hDM
  · simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    positivity
  let S := fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, f n
  have hab := Finset.sum_Ioc_by_parts (fun n : ℕ ↦ (n : ℂ)⁻¹) f hDM
  simp only [smul_eq_mul, sum_range_succ_eq_Icc_of_zero f hf0] at hab
  have hfirst : ‖(M : ℂ)⁻¹ * S M‖ ≤ K := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (M : ℝ)⁻¹ * ((M : ℝ) * K) :=
        mul_le_mul_of_nonneg_left (hprefix M hDM.le) (by positivity)
      _ = K := by field_simp
  have hsecond : ‖((D + 1 : ℕ) : ℂ)⁻¹ * S D‖ ≤ K := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ ((D + 1 : ℕ) : ℝ)⁻¹ * ((D : ℝ) * K) :=
        mul_le_mul_of_nonneg_left (hprefix D le_rfl) (by positivity)
      _ ≤ ((D + 1 : ℕ) : ℝ)⁻¹ * (((D + 1 : ℕ) : ℝ) * K) := by gcongr; omega
      _ = K := by field_simp
  have hterm : ∀ n ∈ Finset.Ioc D (M - 1),
      ‖(((n + 1 : ℕ) : ℂ)⁻¹ - (n : ℂ)⁻¹) * S n‖ ≤ K * (n : ℝ)⁻¹ := by
    intro n hn
    have hnD := (Finset.mem_Ioc.mp hn).1.le
    have hn0 : 0 < n := hD.trans_le hnD
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have hgap : (0 : ℝ) ≤ (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ :=
      sub_nonneg.mpr (inv_anti₀ hnr (by norm_num))
    rw [norm_mul, norm_inv_succ_sub_inv n hn0]
    calc
      _ ≤ ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) * ((n : ℝ) * K) :=
        mul_le_mul_of_nonneg_left (hprefix n hnD) hgap
      _ = K / (n + 1 : ℕ) := by push_cast; field_simp; ring
      _ ≤ K * (n : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hnr (by norm_num)) hK
  have hsum : ‖∑ n ∈ Finset.Ioc D (M - 1),
      (((n + 1 : ℕ) : ℂ)⁻¹ - (n : ℂ)⁻¹) * S n‖ ≤ K * (1 + Real.log (M : ℝ)) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc D (M - 1),
          ‖(((n + 1 : ℕ) : ℂ)⁻¹ - (n : ℂ)⁻¹) * S n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ioc D (M - 1), K * (n : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ Finset.Icc 1 M, K * (n : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
          omega
        · intro n _ _; positivity
      _ = K * ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
          harmonic_le_one_add_log M) hK
  have hid : (∑ n ∈ Finset.Ioc D M, f n / n) =
      (M : ℂ)⁻¹ * S M - ((D + 1 : ℕ) : ℂ)⁻¹ * S D -
        ∑ n ∈ Finset.Ioc D (M - 1), (((n + 1 : ℕ) : ℂ)⁻¹ - (n : ℂ)⁻¹) * S n := by
    simpa only [S, div_eq_mul_inv, mul_comm] using hab
  rw [hid]
  calc
    _ ≤ (‖(M : ℂ)⁻¹ * S M‖ + ‖((D + 1 : ℕ) : ℂ)⁻¹ * S D‖) +
        ‖∑ n ∈ Finset.Ioc D (M - 1), (((n + 1 : ℕ) : ℂ)⁻¹ - (n : ℂ)⁻¹) * S n‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by linarith [hfirst, hsecond, hsum]

end Erdos1141
