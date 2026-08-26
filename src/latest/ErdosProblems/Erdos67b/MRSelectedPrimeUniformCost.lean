import ErdosProblems.Erdos67b.MRSelectedPrimeIntervalMass

/-!
# Uniform selected-prime costs at a fixed endpoint ratio

The Euler multiplier depends only on the ratio of logarithmic endpoints.
It is independent of the ambient scale and of the upper power exponent.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrSelectedPrimeRatioCost (r : ℝ) : ℝ :=
  Real.exp (2 * Real.exp 1 * (Real.log (4 / r) + 2 * PrimeEstimates.mertensBound))

theorem mrSelectedPrimeRatioCost_pos (r : ℝ) : 0 < mrSelectedPrimeRatioCost r :=
  Real.exp_pos _

theorem mrSelected_eulerProduct_one_le_exp_reciprocalMass
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    (∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹) ≤ Real.exp (2 * ∑ p ∈ A, 1 / (p : ℝ)) := by
  have hh : ∀ p ∈ A, (p : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    intro p hp
    rw [Real.rpow_neg_one]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ p by exact_mod_cast (hA p hp).two_le)
  simpa only [Real.rpow_neg_one, one_div] using mrSelected_eulerProduct_le_exp_mass A 1 hh

theorem mrSelected_eulerProducts_le_ratio
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {r b : ℝ} (hr : 0 < r) (hrOne : r ≤ 1) (hb : 0 < b) (ha : 4 ≤ r * b)
    (hlower : ∀ p ∈ A, r * b ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b) :
    (∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹) ≤ mrSelectedPrimeRatioCost r ∧
    (∏ p ∈ A, (1 - (p : ℝ) ^ (-(1 - b⁻¹)))⁻¹) ≤ mrSelectedPrimeRatioCost r := by
  have hab : r * b ≤ b := by nlinarith
  have hbTwo : 2 ≤ b := by linarith
  have hratio : 4 * b / (r * b) = 4 / r := by field_simp
  have hmass := mrSelected_reciprocalMass_le_log_ratio A hA ha hab hlower hupper
  rw [hratio] at hmass
  have hmassNonneg : 0 ≤ ∑ p ∈ A, 1 / (p : ℝ) :=
    Finset.sum_nonneg (fun p hp ↦ by positivity)
  have hR : 0 ≤ Real.log (4 / r) + 2 * PrimeEstimates.mertensBound :=
    hmassNonneg.trans hmass
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨?_, ?_⟩
  · apply (mrSelected_eulerProduct_one_le_exp_reciprocalMass A hA).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply (mrSelected_eulerProduct_shifted_le_reciprocalMass A hbTwo
      (fun p hp ↦ mrSelected_log_lower_four_implies_four (hA p hp) ha (hlower p hp))
      hupper).trans
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hmass (by positivity))

theorem mrSelected_euler_rankin_le_ratio
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {r b tau epsilon : ℝ} {K : ℕ}
    (hr : 0 < r) (hrOne : r ≤ 1) (hb : 0 < b) (ha : 4 ≤ r * b)
    (hlower : ∀ p ∈ A, r * b ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b)
    (hepsilon : 0 ≤ epsilon) (hK : Real.exp (tau * b) ≤ K) :
    epsilon * (∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹) +
        (K : ℝ) ^ ((1 - b⁻¹) - 1) * ∏ p ∈ A, (1 - (p : ℝ) ^ (-(1 - b⁻¹)))⁻¹ ≤
      mrSelectedPrimeRatioCost r * (epsilon + Real.exp (-tau)) := by
  obtain ⟨hone, hshift⟩ := mrSelected_eulerProducts_le_ratio A hA hr hrOne hb ha hlower hupper
  have hpower : (K : ℝ) ^ ((1 - b⁻¹) - 1) ≤ Real.exp (-tau) := by
    calc
      _ ≤ (Real.exp (tau * b)) ^ ((1 - b⁻¹) - 1) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hK (by
          have := inv_pos.mpr hb
          linarith)
      _ = _ := mrSelected_rankin_exp_cutoff hb
  calc
    _ ≤ epsilon * mrSelectedPrimeRatioCost r +
        (K : ℝ) ^ ((1 - b⁻¹) - 1) * mrSelectedPrimeRatioCost r :=
      add_le_add (mul_le_mul_of_nonneg_left hone hepsilon)
        (mul_le_mul_of_nonneg_left hshift (Real.rpow_nonneg (Nat.cast_nonneg K) _))
    _ ≤ epsilon * mrSelectedPrimeRatioCost r +
        Real.exp (-tau) * mrSelectedPrimeRatioCost r :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hpower (mrSelectedPrimeRatioCost_pos r).le)
    _ = _ := by ring

end

end Erdos67b
