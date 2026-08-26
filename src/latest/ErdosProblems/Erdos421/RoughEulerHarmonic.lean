import ErdosProblems.Erdos421.RoughEulerProduct
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # An elementary upper bound for the rough-number density -/

namespace Erdos421

theorem reciprocal_smooth_hasSum (z : ℕ) :
    HasSum (fun n : Nat.smoothNumbers z ↦ ((n : ℕ) : ℝ)⁻¹) (roughEulerProduct z)⁻¹ := by
  let f : ℕ →* ℝ :=
    { toFun := fun n ↦ (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := by intro m n; simp only [Nat.cast_mul, mul_inv] }
  have hprime : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := by
    intro p hp
    have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpp)]
    exact (inv_lt_one₀ hpp).mpr (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hprime z).2
  change HasSum (fun n : Nat.smoothNumbers z ↦ ((n : ℕ) : ℝ)⁻¹)
    (∏ p ∈ z.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) at h
  simpa only [roughEulerProduct, sievePrimes, Nat.Ico_zero_eq_range, Nat.primesBelow,
    Finset.prod_inv_distrib] using h

theorem harmonic_le_inv_roughEulerProduct {z : ℕ} (hz : 1 ≤ z) :
    (harmonic (z - 1) : ℝ) ≤ (roughEulerProduct z)⁻¹ := by
  classical
  have hmem : ∀ n ∈ Finset.Icc 1 (z - 1), n ∈ Nat.smoothNumbers z := by
    intro n hn
    obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
    exact Nat.mem_smoothNumbers_of_lt hn1 (by omega)
  have hb := sum_le_hasSum ((Finset.Icc 1 (z - 1)).subtype (fun n ↦ n ∈ Nat.smoothNumbers z))
    (fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg (n : ℕ))) (reciprocal_smooth_hasSum z)
  rw [Finset.sum_subtype_of_mem (fun n : ℕ ↦ (n : ℝ)⁻¹) hmem] at hb
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using hb

theorem roughEulerProduct_le_inv_log {z : ℕ} (hz : 2 ≤ z) :
    roughEulerProduct z ≤ (Real.log (z : ℝ))⁻¹ := by
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hb : Real.log (z : ℝ) ≤ (roughEulerProduct z)⁻¹ := by
    apply le_trans _ (harmonic_le_inv_roughEulerProduct (by omega))
    have h := log_add_one_le_harmonic (z - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ z)] at h
  rw [inv_eq_one_div, le_div_iff₀ hlog]
  have h := mul_le_mul_of_nonneg_right hb (roughEulerProduct_pos z).le
  simpa only [inv_mul_cancel₀ (roughEulerProduct_pos z).ne', mul_comm] using h

end Erdos421
