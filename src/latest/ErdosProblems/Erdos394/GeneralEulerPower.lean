import ErdosProblems.Erdos394.EulerHarmonic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sharp powered Euler comparisons for general root weights
-/

open Nat Finset

namespace Erdos394

/-- Local numerator comparison with the exact exponent `1-1/K`, expressed
without real powers. -/
theorem combinedEulerFactor_pow_le
    {K : ℕ} (hK : 0 < K) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((1 - x) * (1 + x / (K : ℝ))) ^ K ≤ (1 - x) ^ (K - 1) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hbase0 : 0 ≤ 1 + x / (K : ℝ) := by positivity
  have hexpBase : 1 + x / (K : ℝ) ≤ Real.exp (x / (K : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (x / (K : ℝ))
  have hpow : (1 + x / (K : ℝ)) ^ K ≤ Real.exp x := by
    calc
      (1 + x / (K : ℝ)) ^ K ≤ (Real.exp (x / (K : ℝ))) ^ K :=
        pow_le_pow_left₀ hbase0 hexpBase K
      _ = Real.exp ((K : ℝ) * (x / (K : ℝ))) :=
        (Real.exp_nat_mul (x / (K : ℝ)) K).symm
      _ = Real.exp x := by field_simp
  have hneg : 1 - x ≤ Real.exp (-x) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-x)
  have hcore : (1 - x) * (1 + x / (K : ℝ)) ^ K ≤ 1 := by
    calc
      (1 - x) * (1 + x / (K : ℝ)) ^ K ≤
          Real.exp (-x) * (1 + x / (K : ℝ)) ^ K :=
        mul_le_mul_of_nonneg_right hneg (pow_nonneg hbase0 K)
      _ ≤ Real.exp (-x) * Real.exp x :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hsub0 : 0 ≤ (1 - x) ^ (K - 1) := by positivity
  calc
    ((1 - x) * (1 + x / (K : ℝ))) ^ K =
        (1 - x) ^ (K - 1) *
          ((1 - x) * (1 + x / (K : ℝ)) ^ K) := by
      have hKs : K - 1 + 1 = K := by omega
      have hpowSub : (1 - x) ^ K = (1 - x) ^ (K - 1) * (1 - x) := by
        nth_rewrite 1 [← hKs]
        rw [pow_succ]
      rw [mul_pow, hpowSub]
      ring
    _ ≤ (1 - x) ^ (K - 1) * 1 :=
      mul_le_mul_of_nonneg_left hcore hsub0
    _ = (1 - x) ^ (K - 1) := by ring

/-- Product numerator comparison:
`(V·∏(1+1/(Kp)))^K ≤ V^(K-1)`. -/
theorem combinedEulerProduct_pow_le
    (K : ℕ) (hK : 0 < K) (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    (localEulerProduct P x *
      ∏ i ∈ P, (1 + x i / (K : ℝ))) ^ K ≤
        (localEulerProduct P x) ^ (K - 1) := by
  unfold localEulerProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  calc
    (∏ i ∈ P, ((1 - x i) * (1 + x i / (K : ℝ))) ^ K) ≤
        ∏ i ∈ P, (1 - x i) ^ (K - 1) := by
      apply Finset.prod_le_prod
      · intro i hi
        apply pow_nonneg
        exact mul_nonneg (sub_nonneg.mpr (hx1 i hi))
          (add_nonneg zero_le_one (div_nonneg (hx0 i hi)
            (by exact_mod_cast hK.le)))
      · intro i hi
        exact combinedEulerFactor_pow_le hK (hx0 i hi) (hx1 i hi)
    _ = (∏ i ∈ P, (1 - x i)) ^ (K - 1) :=
      Finset.prod_pow P (K - 1) (fun i ↦ 1 - x i)

/-- Local denominator comparison. For primes large enough that
`x≤1/(2(2K+1))`, the root factor has exponent strictly larger than
`1/(K+1)`: `(1-x)^2(1+x/K)^(2K+1)≥1`. -/
theorem one_le_denominatorEulerFactor
    {K : ℕ} (hK : 0 < K) {x : ℝ} (hx0 : 0 ≤ x)
    (hxsmall : 2 * (2 * K + 1 : ℕ) * x ≤ 1) :
    1 ≤ (1 - x) ^ 2 * (1 + x / (K : ℝ)) ^ (2 * K + 1) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  let b : ℕ := 2 * K + 1
  have hbpos : 0 < b := by dsimp [b]; omega
  have hxhalf : 2 * x ≤ 1 := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    change 2 * (b : ℝ) * x ≤ 1 at hxsmall
    nlinarith
  have hminus0 : 0 ≤ 1 - 2 * x := by linarith
  have hminus : 1 - 2 * x ≤ (1 - x) ^ 2 := by nlinarith [sq_nonneg x]
  have hbern : 1 + (b : ℝ) * (x / (K : ℝ)) ≤
      (1 + x / (K : ℝ)) ^ b := by
    have hneg : (-2 : ℝ) ≤ x / (K : ℝ) := by
      have := div_nonneg hx0 hKR.le
      linarith
    simpa using one_add_mul_le_pow hneg b
  have hlin0 : 0 ≤ 1 + (b : ℝ) * (x / (K : ℝ)) := by positivity
  have hproduct :
      (1 - 2 * x) * (1 + (b : ℝ) * (x / (K : ℝ))) ≤
        (1 - x) ^ 2 * (1 + x / (K : ℝ)) ^ b :=
    mul_le_mul hminus hbern hlin0 (sq_nonneg (1 - x))
  have hleft : 1 ≤
      (1 - 2 * x) * (1 + (b : ℝ) * (x / (K : ℝ))) := by
    have hbEq : (b : ℝ) = 2 * (K : ℝ) + 1 := by dsimp [b]; push_cast; ring
    have hsmallR : 2 * (b : ℝ) * x ≤ 1 := by
      change 2 * (b : ℝ) * x ≤ 1 at hxsmall
      exact hxsmall
    rw [hbEq]
    field_simp
    nlinarith
  exact hleft.trans hproduct

/-- Product denominator comparison:
`1 ≤ V²·(∏(1+1/(Kp)))^(2K+1)`. -/
theorem one_le_denominatorEulerProduct
    (K : ℕ) (hK : 0 < K) (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i)
    (hxsmall : ∀ i ∈ P, 2 * (2 * K + 1 : ℕ) * x i ≤ 1) :
    1 ≤ (localEulerProduct P x) ^ 2 *
      (∏ i ∈ P, (1 + x i / (K : ℝ))) ^ (2 * K + 1) := by
  unfold localEulerProduct
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  calc
    1 = ∏ _i ∈ P, (1 : ℝ) := by simp
    _ ≤ ∏ i ∈ P, (1 - x i) ^ 2 *
        (1 + x i / (K : ℝ)) ^ (2 * K + 1) := by
      apply Finset.prod_le_prod
      · intro i hi
        norm_num
      · intro i hi
        exact one_le_denominatorEulerFactor hK (hx0 i hi) (hxsmall i hi)

end Erdos394
