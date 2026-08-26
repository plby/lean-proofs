import ErdosProblems.Erdos67b.MRSelectedPrimeUniformCost

/-!
# Selected-prime tails with an arbitrary fixed positive-line shift

The line `1 - shift / b` strengthens the Rankin tail to `exp (-shift * tau)`.
Its Euler multiplier remains independent of the ambient scale. This lets
subsequent parameter choices track more than a polynomial cutoff cost.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrSelectedPrimeShiftedRatioCost (r shift : ℝ) : ℝ :=
  Real.exp (2 * Real.exp shift * (Real.log (4 / r) + 2 * PrimeEstimates.mertensBound))

theorem mrSelectedPrimeShiftedRatioCost_pos (r shift : ℝ) :
    0 < mrSelectedPrimeShiftedRatioCost r shift := Real.exp_pos _

theorem mrSelected_shiftedPower_le_exp_shift_div {p : ℕ} (hp : 0 < p)
    {b shift : ℝ} (hb : 0 < b) (hshift : 0 ≤ shift)
    (hlog : Real.log (p : ℝ) ≤ b) :
    (p : ℝ) ^ (-(1 - shift / b)) ≤ Real.exp shift / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hratio : Real.log (p : ℝ) * (shift / b) ≤ shift := by
    have hh := mul_le_mul_of_nonneg_left hlog hshift
    have hdiv : shift * Real.log (p : ℝ) / b ≤ shift := (div_le_iff₀ hb).2 hh
    convert hdiv using 1; ring
  rw [show -(1 - shift / b) = -1 + shift / b by ring, Real.rpow_add hpR,
    Real.rpow_neg_one, Real.rpow_def_of_pos hpR, div_eq_mul_inv (Real.exp shift) (p : ℝ),
    mul_comm (Real.exp shift)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hratio) (inv_nonneg.mpr hpR.le)

theorem mrSelected_eulerProduct_shift_le_reciprocalMass
    (A : Finset ℕ) {b shift : ℝ} (hb : 0 < b) (hshift : 0 ≤ shift)
    (hbs : 2 * shift ≤ b) (hfour : ∀ p ∈ A, 4 ≤ p)
    (hlog : ∀ p ∈ A, Real.log (p : ℝ) ≤ b) :
    (∏ p ∈ A, (1 - (p : ℝ) ^ (-(1 - shift / b)))⁻¹) ≤
      Real.exp (2 * Real.exp shift * ∑ p ∈ A, 1 / (p : ℝ)) := by
  have hratio : shift / b ≤ 1 / 2 := (div_le_iff₀ hb).2 (by linarith)
  have hhalf : ∀ p ∈ A, (p : ℝ) ^ (-(1 - shift / b)) ≤ 1 / 2 := by
    intro p hp
    have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hfour p hp
    calc
      _ ≤ (4 : ℝ) ^ (-(1 - shift / b)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
      _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]; norm_num
  apply (mrSelected_eulerProduct_le_exp_mass A (1 - shift / b) hhalf).trans
  apply Real.exp_le_exp.mpr
  have hsum : (∑ p ∈ A, (p : ℝ) ^ (-(1 - shift / b))) ≤
      Real.exp shift * ∑ p ∈ A, 1 / (p : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_one_div] using mrSelected_shiftedPower_le_exp_shift_div
      (by have := hfour p hp; omega) hb hshift (hlog p hp)
  linarith

theorem mrSelected_eulerProducts_shift_le_ratio
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {r b shift : ℝ} (hr : 0 < r) (hrOne : r ≤ 1) (hb : 0 < b)
    (hshift : 0 ≤ shift) (hbs : 2 * shift ≤ b) (ha : 4 ≤ r * b)
    (hlower : ∀ p ∈ A, r * b ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b) :
    (∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹) ≤ mrSelectedPrimeShiftedRatioCost r shift ∧
    (∏ p ∈ A, (1 - (p : ℝ) ^ (-(1 - shift / b)))⁻¹) ≤
      mrSelectedPrimeShiftedRatioCost r shift := by
  have hab : r * b ≤ b := by nlinarith
  have hratio : 4 * b / (r * b) = 4 / r := by field_simp
  have hmass := mrSelected_reciprocalMass_le_log_ratio A hA ha hab hlower hupper
  rw [hratio] at hmass
  have hmassNonneg : 0 ≤ ∑ p ∈ A, 1 / (p : ℝ) :=
    Finset.sum_nonneg (fun p hp ↦ by positivity)
  have hR : 0 ≤ Real.log (4 / r) + 2 * PrimeEstimates.mertensBound :=
    hmassNonneg.trans hmass
  have he : 1 ≤ Real.exp shift := Real.one_le_exp hshift
  refine ⟨?_, ?_⟩
  · apply (mrSelected_eulerProduct_one_le_exp_reciprocalMass A hA).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply (mrSelected_eulerProduct_shift_le_reciprocalMass A hb hshift hbs
      (fun p hp ↦ mrSelected_log_lower_four_implies_four (hA p hp) ha (hlower p hp))
      hupper).trans
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hmass (by positivity))

theorem mrSelected_rankin_exp_cutoff_shift {b shift tau : ℝ} (hb : 0 < b) :
    (Real.exp (tau * b)) ^ ((1 - shift / b) - 1) = Real.exp (-shift * tau) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp
  ring

theorem mrSelected_shifted_euler_rankin_le_ratio
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {r b shift tau epsilon : ℝ} {K : ℕ}
    (hr : 0 < r) (hrOne : r ≤ 1) (hb : 0 < b)
    (hshift : 0 ≤ shift) (hbs : 2 * shift ≤ b) (ha : 4 ≤ r * b)
    (hlower : ∀ p ∈ A, r * b ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b)
    (hepsilon : 0 ≤ epsilon) (hK : Real.exp (tau * b) ≤ K) :
    epsilon * (∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹) +
        (K : ℝ) ^ ((1 - shift / b) - 1) *
          ∏ p ∈ A, (1 - (p : ℝ) ^ (-(1 - shift / b)))⁻¹ ≤
      mrSelectedPrimeShiftedRatioCost r shift * (epsilon + Real.exp (-shift * tau)) := by
  obtain ⟨hone, hshiftProd⟩ :=
    mrSelected_eulerProducts_shift_le_ratio A hA hr hrOne hb hshift hbs ha hlower hupper
  have hpower : (K : ℝ) ^ ((1 - shift / b) - 1) ≤ Real.exp (-shift * tau) := by
    calc
      _ ≤ (Real.exp (tau * b)) ^ ((1 - shift / b) - 1) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hK (by
          have := div_nonneg hshift hb.le
          linarith)
      _ = _ := mrSelected_rankin_exp_cutoff_shift hb
  calc
    _ ≤ epsilon * mrSelectedPrimeShiftedRatioCost r shift +
        (K : ℝ) ^ ((1 - shift / b) - 1) * mrSelectedPrimeShiftedRatioCost r shift :=
      add_le_add (mul_le_mul_of_nonneg_left hone hepsilon)
        (mul_le_mul_of_nonneg_left hshiftProd (Real.rpow_nonneg (Nat.cast_nonneg K) _))
    _ ≤ epsilon * mrSelectedPrimeShiftedRatioCost r shift +
        Real.exp (-shift * tau) * mrSelectedPrimeShiftedRatioCost r shift :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hpower
        (mrSelectedPrimeShiftedRatioCost_pos r shift).le)
    _ = _ := by ring

end

end Erdos67b
