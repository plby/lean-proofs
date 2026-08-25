import ErdosProblems.Erdos1141.GeneralBurgess
import Mathlib.Algebra.BigOperators.Module

/-!
# Discrete partial summation for reciprocal character sums
-/

namespace Pollack17

open scoped BigOperators

theorem abs_reciprocal_interval_le (f : ℕ → ℝ) {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y)
    {b : ℝ} (hb : 0 ≤ b)
    (hprefix : ∀ n : ℕ, x ≤ n → n ≤ y →
      |∑ i ∈ Finset.range (n + 1), f i| ≤ (n : ℝ) * b) :
    |∑ i ∈ Finset.Ioc x y, f i / (i : ℝ)| ≤ b * (3 + Real.log (y : ℝ)) := by
  by_cases heq : x = y
  · subst y
    have hy1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    simp only [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact mul_nonneg hb (by linarith [Real.log_nonneg hy1])
  have hlt : x < y := lt_of_le_of_ne hxy heq
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyR : 0 < (y : ℝ) := by exact_mod_cast (hx.trans_le hxy)
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), f i
  have hid : (∑ i ∈ Finset.Ioc x y, f i / (i : ℝ)) =
      (y : ℝ)⁻¹ * S y - ((x + 1 : ℕ) : ℝ)⁻¹ * S x -
        ∑ i ∈ Finset.Ioc x (y - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i := by
    simpa only [S, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      Finset.sum_Ioc_by_parts (fun i : ℕ => (i : ℝ)⁻¹) f hlt
  have hend : |(y : ℝ)⁻¹ * S y| ≤ b := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hyR)]
    calc
      _ ≤ (y : ℝ)⁻¹ * ((y : ℝ) * b) := mul_le_mul_of_nonneg_left
        (hprefix y hxy le_rfl) (inv_nonneg.mpr hyR.le)
      _ = _ := by field_simp
  have hstart : |((x + 1 : ℕ) : ℝ)⁻¹ * S x| ≤ b := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < ((x + 1 : ℕ) : ℝ)⁻¹)]
    calc
      _ ≤ ((x + 1 : ℕ) : ℝ)⁻¹ * ((x : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (hprefix x le_rfl hxy) (by positivity)
      _ ≤ ((x + 1 : ℕ) : ℝ)⁻¹ * (((x + 1 : ℕ) : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by push_cast; linarith) hb) (by positivity)
      _ = b := by field_simp
  have hterm (i : ℕ) (hi : i ∈ Finset.Ioc x (y - 1)) :
      |(((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| ≤ b * (i : ℝ)⁻¹ := by
    have hix := (Finset.mem_Ioc.mp hi).1
    have hiy := (Finset.mem_Ioc.mp hi).2
    have hiR : 0 < (i : ℝ) := by exact_mod_cast (hx.trans hix)
    have hi1R : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    have hinv : ((i + 1 : ℕ) : ℝ)⁻¹ ≤ (i : ℝ)⁻¹ :=
      inv_anti₀ hiR (by push_cast; linarith)
    have hdiff : 0 ≤ (i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹ := sub_nonneg.mpr hinv
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hinv)]
    calc
      _ = ((i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹) * |S i| := by ring
      _ ≤ ((i : ℝ)⁻¹ - ((i + 1 : ℕ) : ℝ)⁻¹) * ((i : ℝ) * b) :=
        mul_le_mul_of_nonneg_left (hprefix i hix.le (by omega)) hdiff
      _ = b * ((i + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      _ ≤ b * (i : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hinv hb
  have hsum : |∑ i ∈ Finset.Ioc x (y - 1),
      (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| ≤ b * (1 + Real.log (y : ℝ)) := by
    calc
      _ ≤ ∑ i ∈ Finset.Ioc x (y - 1),
          |(((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ioc x (y - 1), b * (i : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ = b * ∑ i ∈ Finset.Ioc x (y - 1), (i : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ b * ∑ i ∈ Finset.Icc 1 y, (i : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hb
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          have hi := Finset.mem_Ioc.mp hi
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · intro i _ _
          positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left (Burgess.sum_Icc_inv_natCast_le_one_add_log y) hb
  rw [hid]
  calc
    _ ≤ |(y : ℝ)⁻¹ * S y| + |((x + 1 : ℕ) : ℝ)⁻¹ * S x| +
        |∑ i ∈ Finset.Ioc x (y - 1), (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i| :=
      (by
        have h₁ := norm_sub_le ((y : ℝ)⁻¹ * S y - ((x + 1 : ℕ) : ℝ)⁻¹ * S x)
          (∑ i ∈ Finset.Ioc x (y - 1), (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) * S i)
        have h₂ := norm_sub_le ((y : ℝ)⁻¹ * S y) (((x + 1 : ℕ) : ℝ)⁻¹ * S x)
        simp only [Real.norm_eq_abs] at h₁ h₂
        linarith only [h₁, h₂])
    _ ≤ b + b + b * (1 + Real.log (y : ℝ)) := add_le_add (add_le_add hend hstart) hsum
    _ = _ := by ring

end Pollack17
