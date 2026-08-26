import ErdosProblems.Erdos4.EulerDensity

/-!
# Two-sided Euler density estimates

The already proved weak Mertens bounds give an absolute upper bound for
the normalization factor `V ρ log R`, and two-sided estimates for the
preliminary-sieve density between two prime cutoffs. No asymptotic Euler
constant is needed.
-/

open scoped BigOperators

namespace Erdos4.EulerDensityBounds

open ArithmeticFibers EulerDensity

theorem exists_uniform_density_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ K R : ℕ, K ≤ R → 2 ≤ R →
      UnitFourier.unitDensity (fun p : primeWindow K R => (p : ℕ)) *
        BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Real.log R ≤ C := by
  obtain ⟨c, hc, hlower⟩ := weak_mertens_third_lower_all
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro K R hKR hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hprod : 0 < partial_euler_product R := zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hh : c * Real.log R ≤ partial_euler_product R := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_pos hprod, abs_of_pos hlog]
      using hlower (R : ℝ) (by exact_mod_cast (show 1 ≤ R by omega))
  have hinv := one_div_le_one_div_of_le (mul_pos hc hlog) hh
  rw [window_density_mul_small hKR, full_density_eq_inverse]
  have hmul := mul_le_mul_of_nonneg_right hinv hlog.le
  have heq : (1 / (c * Real.log (R : ℝ))) * Real.log R = c⁻¹ := by field_simp
  rw [heq] at hmul
  simpa only [one_div] using hmul

theorem window_density_eq_ratio {w z : ℕ} (hwz : w ≤ z) :
    UnitFourier.unitDensity (fun p : primeWindow w z => (p : ℕ)) =
      partial_euler_product w / partial_euler_product z := by
  have hh := window_density_mul_small hwz
  rw [density_primorial_eq, full_density_eq_inverse, full_density_eq_inverse] at hh
  have hw : 0 < partial_euler_product w := zero_lt_one.trans_le partial_euler_trivial_lower_bound
  calc
    _ = (UnitFourier.unitDensity (fun p : primeWindow w z => (p : ℕ)) *
        (partial_euler_product w)⁻¹) * partial_euler_product w := by field_simp
    _ = (partial_euler_product z)⁻¹ * partial_euler_product w := by rw [hh]
    _ = _ := by ring

theorem exists_window_density_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w z : ℕ, 2 ≤ w → w ≤ z →
      c * Real.log w / Real.log z ≤ UnitFourier.unitDensity (fun p : primeWindow w z => (p : ℕ)) ∧
      UnitFourier.unitDensity (fun p : primeWindow w z => (p : ℕ)) ≤ C * Real.log w / Real.log z := by
  obtain ⟨c₀, hc₀, hlower⟩ := weak_mertens_third_lower_all
  obtain ⟨C₀, hC₀, hupper⟩ := weak_mertens_third_upper_all
  refine ⟨c₀ / C₀, C₀ / c₀, div_pos hc₀ hC₀, div_pos hC₀ hc₀, ?_⟩
  intro w z hw hwz
  have hz : 2 ≤ z := hw.trans hwz
  have hlw : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast hw)
  have hlz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hpw : 0 < partial_euler_product w := zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hpz : 0 < partial_euler_product z := zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hwlow : c₀ * Real.log w ≤ partial_euler_product w := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_pos hpw, abs_of_pos hlw]
      using hlower (w : ℝ) (by exact_mod_cast (show 1 ≤ w by omega))
  have hwup : partial_euler_product w ≤ C₀ * Real.log w := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_pos hpw, abs_of_pos hlw]
      using hupper (w : ℝ) (by exact_mod_cast hw)
  have hzlow : c₀ * Real.log z ≤ partial_euler_product z := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_pos hpz, abs_of_pos hlz]
      using hlower (z : ℝ) (by exact_mod_cast (show 1 ≤ z by omega))
  have hzup : partial_euler_product z ≤ C₀ * Real.log z := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_pos hpz, abs_of_pos hlz]
      using hupper (z : ℝ) (by exact_mod_cast hz)
  rw [window_density_eq_ratio hwz]
  constructor
  · calc
      _ = (c₀ * Real.log w) / (C₀ * Real.log z) := by ring
      _ ≤ partial_euler_product w / (C₀ * Real.log z) :=
        div_le_div_of_nonneg_right hwlow (mul_pos hC₀ hlz).le
      _ ≤ _ := div_le_div_of_nonneg_left hpw.le hpz hzup
  · calc
      _ ≤ (C₀ * Real.log w) / partial_euler_product z := div_le_div_of_nonneg_right hwup hpz.le
      _ ≤ (C₀ * Real.log w) / (c₀ * Real.log z) :=
        div_le_div_of_nonneg_left (mul_pos hC₀ hlw).le (mul_pos hc₀ hlz) hzlow
      _ = _ := by ring

end Erdos4.EulerDensityBounds
