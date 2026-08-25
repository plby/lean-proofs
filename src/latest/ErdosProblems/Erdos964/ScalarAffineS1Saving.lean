import ErdosProblems.Erdos964.ScalarAffineS1Error
import ErdosProblems.Erdos964.SemiprimeSavingParameters

/-!
# Arbitrary logarithmic saving for the scalar first-sum counting error

The explicit coefficient and divisor bounds lose a large but fixed power
of a logarithm. Any radius exponent below `1/2` absorbs that loss.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem exists_radius_square_log_saving (a b : ℕ) (C α : ℝ)
    (hC : 0 < C) (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ R : ℕ,
      1 ≤ R → (R : ℝ) ≤ Real.rpow (N : ℝ) α →
      C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ b ≤
        (N : ℝ) / (Real.log N) ^ a := by
  let K : ℝ := C * 2 ^ b
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨N₀, hN₀, hsave⟩ := exists_log_pow_le_mul_rpow_nat (b + a)
    (1 - 2 * α) (1 / K) (by linarith) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN R hRone hR
  have hNfour : 4 ≤ N := hN₀.trans hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hlogone := one_le_log_natCast hNfour
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hRN : (R : ℝ) ≤ N := hR.trans
    (Real.rpow_le_self_of_one_le hNone (by linarith))
  have hlogs : 1 + Real.log (R : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have := Real.log_le_log hRpos hRN
    linarith
  have hlogR : 0 ≤ 1 + Real.log (R : ℝ) := by
    linarith [Real.log_natCast_nonneg R]
  have hproduct : (Real.rpow (N : ℝ) α) ^ 2 * Real.rpow (N : ℝ) (1 - 2 * α) = N := by
    calc
      _ = Real.rpow (N : ℝ) (α + α) * Real.rpow (N : ℝ) (1 - 2 * α) := by
        have hadd : Real.rpow (N : ℝ) (α + α) =
            Real.rpow (N : ℝ) α * Real.rpow (N : ℝ) α := Real.rpow_add hNpos α α
        rw [hadd]
        ring
      _ = Real.rpow (N : ℝ) ((α + α) + (1 - 2 * α)) :=
        (Real.rpow_add hNpos _ _).symm
      _ = _ := by
        rw [show (α + α) + (1 - 2 * α) = 1 by ring]
        exact Real.rpow_one _
  calc
    _ ≤ C * (Real.rpow (N : ℝ) α) ^ 2 * (2 * Real.log (N : ℝ)) ^ b := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg R) hR 2) hC.le)
        (pow_le_pow_left₀ hlogR hlogs b) (by positivity) (by positivity)
    _ = (K * (Real.rpow (N : ℝ) α) ^ 2 * (Real.log (N : ℝ)) ^ (b + a)) /
        (Real.log (N : ℝ)) ^ a := by
      dsimp [K]
      rw [mul_pow, pow_add]
      field_simp
    _ ≤ (K * (Real.rpow (N : ℝ) α) ^ 2 *
        ((1 / K) * Real.rpow (N : ℝ) (1 - 2 * α))) / (Real.log (N : ℝ)) ^ a := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsave N hN) (by positivity)) (by positivity)
    _ = _ := by
      have hid : K * (Real.rpow (N : ℝ) α) ^ 2 *
          ((1 / K) * Real.rpow (N : ℝ) (1 - 2 * α)) = N := by
        calc
          _ = (Real.rpow (N : ℝ) α) ^ 2 * Real.rpow (N : ℝ) (1 - 2 * α) := by field_simp
          _ = _ := hproduct
      rw [hid]

theorem exists_scalarAffineS1_logSaving (a : ℕ) (α : ℝ)
    (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (A B : Fin 3 → ℕ) (v R : ℕ) (s : BoundingSieve),
      s.prodPrimes.Coprime (affineNormalizationModulus A B) →
      (∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) →
      1 ≤ R → (R : ℝ) ≤ Real.rpow (N : ℝ) α →
      ∀ y : ℕ → ℝ, (∀ u, |y u| ≤ 7) → (∀ u, R ≤ u → y u = 0) →
      |(∑ n ∈ Finset.Ico N (2 * N),
          scalarAffineWeight (fun i => A i * affineNormalizationModulus A B)
            (fun i => A i * v + B i) s.prodPrimes (scalarSelbergCoefficient s y) n) -
          (N : ℝ) * ∑ r ∈ s.prodPrimes.divisors, dimensionSelbergWeight 3 r * (y r) ^ 2| ≤
        (N : ℝ) / (Real.log N) ^ a := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_radius_square_log_saving a 684 49 α
    (by norm_num) hα hαhalf
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN A B v R s hsM hs hRone hR y hy hcut
  have h := normalized_scalarAffineS1_error_le_log A B v N R s hsM hs y 7 (by norm_num) hy hcut
  norm_num only [show (7 : ℝ) ^ 2 = 49 by norm_num] at h
  exact h.trans (hbound N hN R hRone hR)

end Erdos964
