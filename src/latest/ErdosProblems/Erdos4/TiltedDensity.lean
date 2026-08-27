import ErdosProblems.Erdos4.TiltedPrimeSums
import ErdosProblems.Erdos4.EulerDensityBounds

/-!
# The density of surviving primes

Truncate the product at `Z` with `τ log Z ≤ 1`. Its ratio to the ordinary
Mertens product is bounded by an absolute constant, using the elementary
estimate `sum log p / p ≤ 2 log Z`.
-/

open scoped BigOperators

namespace Erdos4.Tilted

theorem baseline_le_one {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) : baseline s u ≤ 1 := by
  rw [baseline_eq_one_sub_atom hs hu]
  linarith [atom_nonneg hs hu]

theorem baseline_le_uniform_exp {s : ℕ} (hs : 2 ≤ s) (τ : ℝ) (hτ : 0 ≤ τ) :
    baseline s ((s : ℝ) ^ (-τ)) ≤ (1 - 1 / (s : ℝ)) *
      Real.exp (2 * τ * Real.log s / s) := by
  let u := (s : ℝ) ^ (-τ)
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hu0 : 0 ≤ u := (rpow_tilt_pos hs τ).le
  have hu1 : u ≤ 1 := rpow_tilt_le_one hs hτ
  have hden : 0 < (s : ℝ) - 1 + u := denominator_pos hs hu0
  have hU : 0 < 1 - 1 / (s : ℝ) := by
    have hh : 1 / (s : ℝ) < 1 := (div_lt_one hspos).mpr (by linarith)
    linarith
  have hfrac : (1 - u) / ((s : ℝ) - 1 + u) ≤ 2 * (1 - u) / s := by
    apply (div_le_div_iff₀ hden hspos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (show 0 ≤ (s : ℝ) - 2 + 2 * u by linarith)]
  have hexp : u = Real.exp (-(τ * Real.log (s : ℝ))) := by
    dsimp only [u]
    rw [Real.rpow_def_of_pos hspos]
    congr 1
    ring
  have hdiff : 1 - u ≤ τ * Real.log s := by
    have hh := Real.one_sub_le_exp_neg (τ * Real.log (s : ℝ))
    rw [← hexp] at hh
    linarith
  have hratio : baseline s u / (1 - 1 / (s : ℝ)) ≤ Real.exp (2 * τ * Real.log s / s) := by
    calc
      _ = 1 + (1 - u) / ((s : ℝ) - 1 + u) := by
        unfold baseline
        field_simp [hden.ne', hspos.ne', show (s : ℝ) - 1 ≠ 0 by linarith]
        ring
      _ ≤ 1 + 2 * (1 - u) / s := add_le_add le_rfl hfrac
      _ ≤ Real.exp (2 * (1 - u) / s) := by
        simpa only [add_comm] using Real.add_one_le_exp (2 * (1 - u) / s)
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ hspos.le
        nlinarith
  have hh := (div_le_iff₀ hU).mp hratio
  simpa only [mul_comm] using hh

theorem primeSurvival_coordinate_eq (w B : ℕ) (τ : ℝ) :
    primeSurvival (coordinateValue w B) τ =
      ∏ p ∈ coordinatePrimes w B, baseline p ((p : ℝ) ^ (-τ)) := by
  unfold primeSurvival coordinateValue
  exact Finset.prod_coe_sort (coordinatePrimes w B) (fun p : ℕ => baseline p ((p : ℝ) ^ (-τ)))

theorem primeSurvival_mono_upper {w Z B : ℕ} (hZB : Z ≤ B) (τ : ℝ) :
    primeSurvival (coordinateValue w B) τ ≤ primeSurvival (coordinateValue w Z) τ := by
  rw [primeSurvival_coordinate_eq, primeSurvival_coordinate_eq]
  have hsub : coordinatePrimes w Z ⊆ coordinatePrimes w B := by
    intro p hp
    obtain ⟨hpp, hwp, hpZ⟩ := mem_coordinatePrimes.mp hp
    exact mem_coordinatePrimes.mpr ⟨hpp, hwp, hpZ.trans hZB⟩
  apply Finset.prod_le_prod_of_subset_of_le_one hsub
  · intro p hp
    exact (baseline_pos (mem_coordinatePrimes.mp hp).1.two_le
      (rpow_tilt_pos (mem_coordinatePrimes.mp hp).1.two_le τ).le).le
  · intro p hp _
    exact baseline_le_one (mem_coordinatePrimes.mp hp).1.two_le
      (rpow_tilt_pos (mem_coordinatePrimes.mp hp).1.two_le τ).le

theorem primeSurvival_truncated_bound {w Z B : ℕ} (hZ : 1 ≤ Z) (hZB : Z ≤ B)
    (τ : ℝ) (hτ : 0 ≤ τ) (hcut : τ * Real.log (Z : ℝ) ≤ 1) :
    primeSurvival (coordinateValue w B) τ ≤
      (∏ p ∈ coordinatePrimes w Z, ((p : ℝ) - 1) / p) * Real.exp 4 := by
  have hprod : primeSurvival (coordinateValue w Z) τ ≤
      (∏ p ∈ coordinatePrimes w Z, (1 - 1 / (p : ℝ))) *
        Real.exp (2 * τ * ∑ p ∈ coordinatePrimes w Z, Real.log (p : ℝ) / p) := by
    rw [primeSurvival_coordinate_eq]
    have hh := Finset.prod_le_prod
      (s := coordinatePrimes w Z)
      (fun p hp => (baseline_pos (mem_coordinatePrimes.mp hp).1.two_le
        (rpow_tilt_pos (mem_coordinatePrimes.mp hp).1.two_le τ).le).le)
      (fun p hp => baseline_le_uniform_exp (mem_coordinatePrimes.mp hp).1.two_le τ hτ)
    rw [Finset.prod_mul_distrib, ← Real.exp_sum] at hh
    have heq : (∑ p ∈ coordinatePrimes w Z, 2 * τ * Real.log (p : ℝ) / p) =
        2 * τ * ∑ p ∈ coordinatePrimes w Z, Real.log (p : ℝ) / p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [heq] at hh
    exact hh
  have hsum : (∑ p ∈ coordinatePrimes w Z, Real.log (p : ℝ) / p) ≤ 2 * Real.log Z :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))).trans (sum_prime_log_div_le Z hZ)
  have hbudget : 2 * τ * (∑ p ∈ coordinatePrimes w Z, Real.log (p : ℝ) / p) ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * τ by positivity)
    nlinarith
  have hpoint : ∀ p ∈ coordinatePrimes w Z, 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_coordinatePrimes.mp hp).1.ne_zero
    field_simp
  have hprod0 : 0 ≤ ∏ p ∈ coordinatePrimes w Z, ((p : ℝ) - 1) / p := by
    apply Finset.prod_nonneg
    intro p hp
    have hh : (1 : ℝ) ≤ p := by exact_mod_cast (mem_coordinatePrimes.mp hp).1.one_le
    exact div_nonneg (sub_nonneg.mpr hh) (Nat.cast_nonneg _)
  have heq := Finset.prod_congr rfl hpoint
  rw [heq] at hprod
  exact (primeSurvival_mono_upper hZB τ).trans
    (hprod.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbudget) hprod0))

theorem coordinate_uniform_product (w B : ℕ) :
    (∏ p ∈ coordinatePrimes w B, ((p : ℝ) - 1) / p) =
      UnitFourier.unitDensity (fun p : ArithmeticFibers.primeWindow w B => (p : ℕ)) := by
  symm
  exact Finset.prod_coe_sort (coordinatePrimes w B) (fun p : ℕ => ((p : ℝ) - 1) / p)

theorem primeSurvival_ge_uniform (w B : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    UnitFourier.unitDensity (fun p : ArithmeticFibers.primeWindow w B => (p : ℕ)) ≤
      primeSurvival (coordinateValue w B) τ := by
  rw [← coordinate_uniform_product, primeSurvival_coordinate_eq]
  apply Finset.prod_le_prod
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_coordinatePrimes.mp hp).1.one_le
    exact div_nonneg (sub_nonneg.mpr hp1) (Nat.cast_nonneg p)
  · intro p hp
    have hp2 := (mem_coordinatePrimes.mp hp).1.two_le
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hu0 := (rpow_tilt_pos hp2 τ).le
    have hu1 := rpow_tilt_le_one hp2 hτ
    exact div_le_div_of_nonneg_left (show 0 ≤ (p : ℝ) - 1 by linarith)
      (denominator_pos hp2 hu0) (by linarith)

/-- Two-sided bounds with absolute constants; the precise Euler constant is not needed. -/
theorem exists_tilted_density_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w Z B : ℕ, 2 ≤ w → w ≤ Z → Z ≤ B →
      ∀ (τ : ℝ), 0 ≤ τ → τ * Real.log (Z : ℝ) ≤ 1 →
        c * Real.log w / Real.log B ≤ primeSurvival (coordinateValue w B) τ ∧
        primeSurvival (coordinateValue w B) τ ≤ C * Real.log w / Real.log Z := by
  obtain ⟨c, C, hc, hC, hbound⟩ := EulerDensityBounds.exists_window_density_bounds
  refine ⟨c, C * Real.exp 4, hc, mul_pos hC (Real.exp_pos _), ?_⟩
  intro w Z B hw hwZ hZB τ hτ hcut
  constructor
  · exact (hbound w B hw (hwZ.trans hZB)).1.trans (primeSurvival_ge_uniform w B τ hτ)
  · have hh := primeSurvival_truncated_bound (w := w) (show 1 ≤ Z by omega) hZB τ hτ hcut
    rw [coordinate_uniform_product] at hh
    calc
      _ ≤ UnitFourier.unitDensity (fun p : ArithmeticFibers.primeWindow w Z => (p : ℕ)) * Real.exp 4 := hh
      _ ≤ (C * Real.log w / Real.log Z) * Real.exp 4 :=
        mul_le_mul_of_nonneg_right (hbound w Z hw hwZ).2 (Real.exp_pos _).le
      _ = _ := by ring

end Erdos4.Tilted
