import ErdosProblems.Erdos1141.SparseEulerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorbing a sparse Euler product into a small power

When the number of exceptional primes is bounded by a fixed power of
`log m`, the exponential cost in the finite Euler product is smaller than
every positive power of `m`, after choosing the Rankin exponent small enough.
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem eventually_const_mul_rpow_le {C d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ d * x ^ b := by
  have hlarge := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually
    (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hratio : C ≤ d * x ^ (b - a) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hx
  calc
    C * x ^ a ≤ (d * x ^ (b - a)) * x ^ a :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hx0.le _)
    _ = d * x ^ b := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring

theorem sparse_cost_le_double_rpow (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := by
  by_cases hK : K = 0
  · subst K
    simp [Real.zero_rpow hδ.ne', Real.zero_rpow (by positivity : 2 * δ ≠ 0)]
  have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hK
  have hK0 : 0 < (K : ℝ) := zero_lt_one.trans_le hK1
  have hpow : 1 ≤ (K : ℝ) ^ δ := Real.one_le_rpow hK1 hδ.le
  have hlog : Real.log (K : ℝ) ≤ (K : ℝ) ^ δ * δ⁻¹ := by
    simpa only [div_eq_mul_inv] using Real.log_natCast_le_rpow_div K hδ
  calc
    (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
        (K : ℝ) ^ δ * ((2 + δ⁻¹) * (K : ℝ) ^ δ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hK0.le _)
      nlinarith
    _ = (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := by
      rw [mul_left_comm, ← Real.rpow_add hK0]
      congr 2
      ring

theorem eventually_sparse_exponential_le_rpow {B δ η C : ℝ}
    (_hB : 0 < B) (hδ : 0 < δ) (hsmall : 2 * B * δ < 1)
    (hη : 0 < η) (hC : 0 ≤ C) :
    ∀ᶠ m : ℕ in atTop, ∀ K : ℕ,
      (K : ℝ) ≤ (Real.log (m : ℝ)) ^ B →
        Real.exp (C * (K : ℝ) ^ δ * (2 + Real.log (K : ℝ))) ≤ (m : ℝ) ^ η := by
  have hlogtop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := C * (2 + δ⁻¹)) hη hsmall)
  filter_upwards [hbound, eventually_ge_atTop 2] with m hm hm2
  intro K hK
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hL0 : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hmass : (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      (2 + δ⁻¹) * (Real.log (m : ℝ)) ^ (2 * B * δ) := by
    calc
      (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
          (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := sparse_cost_le_double_rpow K hδ
      _ ≤ (2 + δ⁻¹) * ((Real.log (m : ℝ)) ^ B) ^ (2 * δ) := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg K) hK (by positivity))
        positivity
      _ = (2 + δ⁻¹) * (Real.log (m : ℝ)) ^ (2 * B * δ) := by
        rw [← Real.rpow_mul hL0.le]
        congr 2
        ring
  have hexponent : C * (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      Real.log (m : ℝ) * η := by
    have hmassC := mul_le_mul_of_nonneg_left hmass hC
    simp only [Real.rpow_one] at hm
    nlinarith
  rw [Real.rpow_def_of_pos hm0]
  exact Real.exp_le_exp.mpr hexponent

/-- A polylogarithmic number of exceptional primes forces a fixed power
saving in the divisor-coefficient sum, uniformly over the character. -/
theorem eventually_sparse_divisor_sum {c B : ℝ} (hc : 0 < c) (hB : 0 < B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ → ∀ X : ℕ,
        (X : ℝ) ≤ (m : ℝ) ^ c →
        ((exceptionalPrimes χ X).card : ℝ) ≤ (Real.log (m : ℝ)) ^ B →
        (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤ (m : ℝ) ^ (c - ρ) := by
  let δ : ℝ := 1 / (4 * (B + 1))
  let s : ℝ := 1 - δ
  let η : ℝ := c * δ / 4
  let ρ : ℝ := c * δ / 2
  let Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(2 * s))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 / 4 := by
    exact one_div_lt_one_div_of_lt (by norm_num) (by nlinarith : 4 < 4 * (B + 1))
  have hδid : 4 * (B + 1) * δ = 1 := by
    exact mul_one_div_cancel (by positivity : (4 : ℝ) * (B + 1) ≠ 0)
  have hsmall : 2 * B * δ < 1 := by nlinarith
  have hs0 : 1 / 2 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hspos : 0 < s := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hexp := eventually_sparse_exponential_le_rpow (C := 2 * eulerLogConstant)
    hB hδ0 hsmall hη
    (mul_nonneg (by norm_num) eulerLogConstant_pos.le)
  have hZ : ∀ᶠ m : ℕ in atTop, Z ≤ (m : ℝ) ^ η := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_const_mul_rpow_le (C := Z) (d := 1) (a := 0) (by norm_num) hη)
    simpa only [Real.rpow_zero, mul_one, one_mul] using h
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hexp, hZ, eventually_ge_atTop 1] with m hmExp hmZ hm1
  intro χ hχ X hX hK
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hXpow : (X : ℝ) ^ s ≤ (m : ℝ) ^ (c * s) := by
    calc
      (X : ℝ) ^ s ≤ ((m : ℝ) ^ c) ^ s :=
        Real.rpow_le_rpow (Nat.cast_nonneg X) hX hspos.le
      _ = (m : ℝ) ^ (c * s) := (Real.rpow_mul hm0.le c s).symm
  have hExp := hmExp (exceptionalPrimes χ X).card hK
  have hExp' :
      Real.exp (2 * eulerLogConstant * (exceptionalPrimes χ X).card ^ (1 - s) *
        (2 + Real.log (exceptionalPrimes χ X).card)) ≤ (m : ℝ) ^ η := by
    simpa only [s, sub_sub_cancel] using hExp
  calc
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
        (X : ℝ) ^ s * Z *
          Real.exp (2 * eulerLogConstant * (exceptionalPrimes χ X).card ^ (1 - s) *
            (2 + Real.log (exceptionalPrimes χ X).card)) :=
      sum_divisorCoefficient_le_sparse_bound χ hχ X hs0 hs1
    _ ≤ (m : ℝ) ^ (c * s) * (m : ℝ) ^ η * (m : ℝ) ^ η :=
      mul_le_mul
        (mul_le_mul hXpow hmZ hZ0 (Real.rpow_nonneg hm0.le _)) hExp'
        (Real.exp_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hm0.le _))
    _ = (m : ℝ) ^ (c - ρ) := by
      rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
      congr 1
      dsimp [s, η, ρ]
      ring

end Pollack17
