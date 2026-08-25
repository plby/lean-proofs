import ErdosProblems.Erdos237b.S2DyadicLower
import ErdosProblems.Erdos237b.S2CrossLimit
import ErdosProblems.Erdos237b.SieveConstants

/-! A lower sequence for the complete S2 arithmetic coefficient, including its cross correction. -/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable def s2YArithmeticCoefficient (H : Finset ℕ) (R W : ℕ)
    (y : (H → ℕ) → ℝ) (m : H) : ℝ :=
  maynardS2RestrictedYDiagonalSum H R W (maynardCoefficientFromY H R W y) m -
    incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
      (maynardDivisorTupleSupport H R W) (maynardCoefficientFromY H R W y) m

theorem lower_sequence_for_s2Arithmetic {H : Finset ℕ} {alpha B J : ℝ}
    (halpha : 0 < alpha) (hB : 0 ≤ B) (y : ℕ → (H → ℕ) → ℝ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N)) (hbound : ∀ N r, |y N r| ≤ B)
    (m : H) (b : ℕ → ℝ) (hb : Tendsto b atTop (nhds J))
    (hble : ∀ᶠ N : ℕ in atTop, b N ≤ s2FiberSquareDiagonal H
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) (y N) m /
        sieveCoordinateScale alpha N ^ ((univ.erase m).card + 2)) :
    ∃ c : ℕ → ℝ, Tendsto c atTop (nhds J) ∧
      ∀ᶠ N : ℕ in atTop, c N ≤ s2YArithmeticCoefficient H
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) (y N) m /
          sieveCoordinateScale alpha N ^ ((univ.erase m).card + 2) := by
  have hdiff := tendsto_normalized_s2Diagonal_sub_fiberDiagonal halpha hB y hy hbound m
  have hcross := tendsto_normalized_s2_cross halpha hB y hy hbound m
  have hlim := (hb.add hdiff).sub hcross
  simp only [add_zero, sub_zero] at hlim
  refine ⟨_, hlim, ?_⟩
  filter_upwards [hble] with N hN
  unfold s2YArithmeticCoefficient
  rw [sub_div, sub_div]
  linarith

theorem exists_dyadic_s2Arithmetic_lower_sequence {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (m : H) (hL : 0 < L) (hk : 2 ^ L ≤ k)
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ J : ℝ, ∃ b : ℕ → ℝ, dyadicS2FiberConstant L k ≤ J ∧
      Tendsto b atTop (nhds J) ∧
      ∀ᶠ N : ℕ in atTop, b N ≤ s2YArithmeticCoefficient H
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
        (dyadicY (L := L) e alpha N) m / sieveCoordinateScale alpha N ^ (k + 1) := by
  have hc : Fintype.card H = k := (Fintype.card_congr e).trans (Fintype.card_fin k)
  have hkpos : 0 < k := (pow_pos (by decide) L).trans_le hk
  have he : (univ.erase m).card = k - 1 := by rw [card_erase_of_mem (mem_univ m), card_univ, hc]
  let K := range (k + 1)
  let q : K ≃ Option H := Fintype.equivOfCardEq (by simp [K, hc])
  obtain ⟨J, b, hJ, hb, hble⟩ := exists_dyadic_s2Fiber_lower_sequence q m e hL hk halpha
  obtain ⟨c, hclim, hcble⟩ := lower_sequence_for_s2Arithmetic halpha (dyadicWeightBound_nonneg L k)
    (dyadicY (L := L) e alpha) (dyadicY_supported e alpha) (abs_dyadicY_le e alpha) m b hb hble
  have hexp : (univ.erase m).card + 2 = k + 1 := by rw [he]; omega
  refine ⟨J, c, ?_, hclim, ?_⟩
  · rw [hexp, he] at hJ
    exact hJ
  · simpa only [hexp] using hcble

end Erdos237b
