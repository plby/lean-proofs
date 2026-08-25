import ErdosProblems.Erdos964.AffineSieveCandidate
import ErdosProblems.Erdos964.SemiprimeSavingParameters

/-!
# Logarithmic saving for the first affine sieve counting error

For any radius below a fixed power `N^α`, `α < 1/2`, the exact finite
counting error is smaller than `N/(log N)^a` for every fixed `a`.
This does not yet evaluate the divisor-sum main term.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem exists_affineS1_radius_saving (a : ℕ) (α : ℝ)
    (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ R : ℕ,
      1 ≤ R → (R : ℝ) ≤ Real.rpow (N : ℝ) α →
      49 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ 42 ≤
        (N : ℝ) / (Real.log N) ^ a := by
  let C : ℝ := 49 * 2 ^ 42
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N₀, hN₀, hsave⟩ := exists_log_pow_le_mul_rpow_nat (42 + a)
    (1 - 2 * α) (1 / C) (by linarith) (by positivity)
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
    _ ≤ 49 * (Real.rpow (N : ℝ) α) ^ 2 * (2 * Real.log (N : ℝ)) ^ 42 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg R) hR 2)
          (by norm_num))
        (pow_le_pow_left₀ hlogR hlogs 42) (by positivity) (by positivity)
    _ = (C * (Real.rpow (N : ℝ) α) ^ 2 * (Real.log (N : ℝ)) ^ (42 + a)) /
        (Real.log (N : ℝ)) ^ a := by
      dsimp [C]
      rw [mul_pow, pow_add]
      field_simp
    _ ≤ (C * (Real.rpow (N : ℝ) α) ^ 2 *
        ((1 / C) * Real.rpow (N : ℝ) (1 - 2 * α))) / (Real.log (N : ℝ)) ^ a := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsave N hN) (by positivity)) (by positivity)
    _ = _ := by
      have hid : C * (Real.rpow (N : ℝ) α) ^ 2 *
          ((1 / C) * Real.rpow (N : ℝ) (1 - 2 * α)) = N := by
        calc
          _ = (Real.rpow (N : ℝ) α) ^ 2 * Real.rpow (N : ℝ) (1 - 2 * α) := by
            field_simp
          _ = _ := hproduct
      rw [hid]

theorem exists_affineMaynardS1_three_logSaving (a : ℕ) (α : ℝ)
    (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (H : Finset ℕ), H.card = 3 → ∀ (A B : H → ℕ) (R W v : ℕ),
        1 ≤ R → (R : ℝ) ≤ Real.rpow (N : ℝ) α → 0 < W →
        CoversAffineLeadingPrimes A W → CoversAffineDeterminantPrimes A B W →
      |(∑ n ∈ Finset.Ico N (2 * N), affineMaynardWeight A B R W v n) -
          affineMaynardS1Main H R W N| ≤ (N : ℝ) / (Real.log N) ^ a := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_affineS1_radius_saving a α hα hαhalf
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN H hH A B R W v hRone hR hW hlead hdet
  exact (affineMaynardS1_three_error_le hH A B R W v N hW hlead hdet).trans
    (hbound N hN R hRone hR)

end Erdos964
