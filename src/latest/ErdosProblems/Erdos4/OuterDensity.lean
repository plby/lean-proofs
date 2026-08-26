import ErdosProblems.Erdos4.OuterRay

/-!
# Preliminary survival density on the integer ray

The logarithmic ratio of the two sieve cutoffs lies between `4/(r V)`
and `8/(r V)` once the fixed loss parameter is in its stable range.
Weak Mertens bounds therefore give the same two-sided order for the
actual preliminary survival density.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.OuterDensity

open SmoothParameters ChebyshevIntervals OuterRay

theorem core_le_primaryExponent (a r : ℕ) : core r ≤ primaryExponent a r := by
  have hh := Nat.mul_le_mul_right (core r) (show 1 ≤ 2 ^ (a + 2 * r) from Nat.one_le_two_pow)
  simpa only [one_mul, primaryExponent] using hh

theorem smallCutoff_two_le (a r : ℕ) : 2 ≤ smallCutoff a r := by
  have hV : 2 ≤ core r := Nat.le_pow (pow_pos (by norm_num) r)
  exact (hV.trans (core_le_primaryExponent a r)).trans (Nat.le_pow (by norm_num))

theorem primeInterval_eq_primeWindow (w z : ℕ) :
    primeInterval w z = ArithmeticFibers.primeWindow w z := by
  ext p
  rw [mem_primeInterval, ArithmeticFibers.mem_primeWindow]

theorem cutoff_log_ratio_bounds {a r : ℕ} (hra : a ≤ r) (hr : 8 ≤ r) :
    4 / ((r : ℝ) * core r) ≤ Real.log (smallCutoff a r : ℝ) / Real.log (smoothFrontier r : ℝ) ∧
      Real.log (smallCutoff a r : ℝ) / Real.log (smoothFrontier r : ℝ) ≤ 8 / ((r : ℝ) * core r) := by
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hE : primaryExponent a r ≤ core r ^ 2 :=
    primaryExponent_le_core_sq_of (stable_exponent_comparison hra (by omega))
  have hlo : Real.log (core r : ℝ) ≤ Real.log (primaryExponent a r : ℝ) :=
    Real.log_le_log hV (by exact_mod_cast core_le_primaryExponent a r)
  have hup : Real.log (primaryExponent a r : ℝ) ≤ 2 * Real.log (core r : ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast primaryExponent_pos a r)
      (by exact_mod_cast hE : (primaryExponent a r : ℝ) ≤ (core r : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  rw [log_core] at hlo hup
  have hwlog : Real.log (smallCutoff a r : ℝ) = 4 * Real.log (primaryExponent a r : ℝ) := by
    rw [smallCutoff, Nat.cast_pow, Real.log_pow]
    norm_num
  have hzlog : Real.log (smoothFrontier r : ℝ) =
      ((r : ℝ) * core r) * ((2 : ℝ) ^ r * Real.log 2) := by
    rw [smoothFrontier, Nat.cast_pow, Real.log_pow]
    simp only [smoothExponent, rankinDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hg : 0 < (2 : ℝ) ^ r * Real.log 2 := mul_pos (by positivity) hlog2
  have hden : 0 < Real.log (smoothFrontier r : ℝ) := by rw [hzlog]; positivity
  constructor
  · calc
      _ = (4 * ((2 : ℝ) ^ r * Real.log 2)) / Real.log (smoothFrontier r : ℝ) := by
        rw [hzlog]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by rw [hwlog]; linarith) hden.le
  · calc
      _ ≤ (8 * ((2 : ℝ) ^ r * Real.log 2)) / Real.log (smoothFrontier r : ℝ) :=
        div_le_div_of_nonneg_right (by rw [hwlog]; linarith) hden.le
      _ = _ := by rw [hzlog]; field_simp

/-- The two constants are independent of the fixed loss parameter. -/
theorem exists_survival_density_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : ℕ, ∀ᶠ r : ℕ in atTop,
      c / ((r : ℝ) * core r) ≤ UnitFourier.unitDensity (fun p : randomPrimes a r => (p : ℕ)) ∧
      UnitFourier.unitDensity (fun p : randomPrimes a r => (p : ℕ)) ≤ C / ((r : ℝ) * core r) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hbounds⟩ := EulerDensityBounds.exists_window_density_bounds
  refine ⟨4 * c₀, 8 * C₀, by positivity, by positivity, ?_⟩
  intro a
  filter_upwards [eventually_ge_atTop (max a 8), eventually_small_le_smooth a] with r hr hwz
  have hra : a ≤ r := (le_max_left a 8).trans hr
  have hr8 : 8 ≤ r := (le_max_right a 8).trans hr
  have hh := hbounds (smallCutoff a r) (smoothFrontier r) (smallCutoff_two_le a r) hwz
  have hratio := cutoff_log_ratio_bounds hra hr8
  have heq : UnitFourier.unitDensity (fun p : randomPrimes a r => (p : ℕ)) =
      UnitFourier.unitDensity (fun p : ArithmeticFibers.primeWindow (smallCutoff a r) (smoothFrontier r) => (p : ℕ)) := by
    unfold UnitFourier.unitDensity
    rw [Finset.prod_coe_sort (randomPrimes a r) (fun p : ℕ => ((p : ℝ) - 1) / p),
      Finset.prod_coe_sort (ArithmeticFibers.primeWindow (smallCutoff a r) (smoothFrontier r))
        (fun p : ℕ => ((p : ℝ) - 1) / p), randomPrimes, primeInterval_eq_primeWindow]
  rw [heq]
  constructor
  · calc
      _ = c₀ * (4 / ((r : ℝ) * core r)) := by ring
      _ ≤ c₀ * (Real.log (smallCutoff a r : ℝ) / Real.log (smoothFrontier r : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio.1 hc₀.le
      _ ≤ _ := by simpa only [mul_div_assoc] using hh.1
  · calc
      _ ≤ C₀ * (Real.log (smallCutoff a r : ℝ) / Real.log (smoothFrontier r : ℝ)) := by
        simpa only [mul_div_assoc] using hh.2
      _ ≤ C₀ * (8 / ((r : ℝ) * core r)) := mul_le_mul_of_nonneg_left hratio.2 hC₀.le
      _ = _ := by ring

end Erdos4.OuterDensity
