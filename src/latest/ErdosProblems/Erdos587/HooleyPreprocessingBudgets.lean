import ErdosProblems.Erdos587.HooleyPreprocessing
import ErdosProblems.Erdos587.HooleySeedDyadicBounds

/-! # Dyadic costs and retained cardinalities for preprocessing -/

open Filter

namespace Erdos587.CFP

lemma delta_preprocessing_cost_le (h L I : ℕ) (hh : 2 ≤ h) (hI : I ≤ h)
    (hlinear : 8 * (L + 1) + 1 ≤ h) :
    4 * h ^ 4 * (2 * L + 2) + (I + 1) * h ^ 2 ≤ h ^ 5 := by
  have hindexCost : (I + 1) * h ^ 2 ≤ h ^ 4 := by
    calc
      _ ≤ h ^ 2 * h ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
      _ = h ^ 4 := by ring
  calc
    _ ≤ 4 * h ^ 4 * (2 * L + 2) + h ^ 4 := Nat.add_le_add_left hindexCost _
    _ = (8 * (L + 1) + 1) * h ^ 4 := by ring
    _ ≤ h * h ^ 4 := Nat.mul_le_mul_right _ hlinear
    _ = h ^ 5 := by ring

lemma delta_preprocessing_reserve_budget (h I : ℕ) (hh : 2 ≤ h) (hI : I ≤ h) :
    I * h ^ 2 + h ^ 2 ≤ h ^ 4 := by
  calc
    _ = (I + 1) * h ^ 2 := by ring
    _ ≤ h ^ 2 * h ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = h ^ 4 := by ring

lemma delta_preprocessing_retained_budgets (a m T r R : ℕ) (hcost : a ≤ m + T)
    (hsmall : T + r ≤ R) (hlarge : 6 * R + 6 ≤ a) :
    2 * ((a + 2) / 3) + r + 1 ≤ m ∧ a ≤ 2 * (m - r) ∧
      a ≤ 3 * ((a + 2) / 3) := by omega

theorem delta_eventually_preprocessing_linear_budget (B b : ℕ) (hb : 0 < b) :
    ∀ᶠ t : ℕ in atTop, 2 ≤ 2 ^ (b * t) ∧ 8 * (B * t + 1) + 1 ≤ 2 ^ (b * t) := by
  filter_upwards [delta_eventually_shifted_polynomial_le_two_pow (8 * B + 9) 1,
    eventually_ge_atTop 1] with t ht htpos
  have hscale : 2 ^ t ≤ 2 ^ (b * t) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  constructor
  · exact (show 2 ^ 1 ≤ 2 ^ t from Nat.pow_le_pow_right (by omega) htpos).trans hscale
  · have hfirst : 8 * (B * t + 1) + 1 ≤ (8 * B + 9) * (t + 1) ^ 1 := by
      simp only [pow_one]
      nlinarith
    exact hfirst.trans (ht.trans hscale)

theorem delta_eventually_dyadic_index_bound (d₀ a b : ℕ) (ha : 0 < a) (hb : d₀ + 1 ≤ b) :
    ∀ᶠ t : ℕ in atTop, ∀ d ≤ d₀, (a * 2 ^ t) ^ d ≤ 2 ^ (b * t) := by
  filter_upwards [delta_eventually_dyadic_polynomial_power 1 a 0 d₀] with t ht
  simp only [pow_zero, mul_one, one_mul] at ht
  intro d hd
  calc
    _ ≤ (a * 2 ^ t) ^ d₀ := Nat.pow_le_pow_right (by positivity) hd
    _ ≤ 2 ^ ((d₀ + 1) * t) := ht
    _ ≤ 2 ^ (b * t) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ hb)

end Erdos587.CFP
