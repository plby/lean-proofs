import ErdosProblems.Erdos237.SieveS2Decomposition

/-! Composition of the arithmetic lower bound, ordinary PNT, and unconditional prime errors. -/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem exists_dyadic_s2Main_lower_sequence {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (hL : 0 < L) (hk : 2 ^ L ≤ k) {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ J : ℝ, ∃ b : ℕ → ℝ, alpha * k * dyadicS2FiberConstant L k ≤ J ∧
      Tendsto b atTop (nhds J) ∧
      ∀ᶠ N : ℕ in atTop, b N ≤ s2YMain H alpha (dyadicY (L := L) e alpha) N /
        sieveScale H alpha N := by
  classical
  have hc : Fintype.card H = k := (Fintype.card_congr e).trans (Fintype.card_fin k)
  choose J b hJ hb hble using fun m : H =>
    exists_dyadic_s2Arithmetic_lower_sequence e m hL hk halpha
  refine ⟨∑ m : H, alpha * J m,
    fun N => ∑ m : H, (shiftedPrimeIntervalCount N m.val / N *
      Real.log (engelsmaMaynardRadius alpha N)) * b m N, ?_, ?_, ?_⟩
  · have hs := sum_le_sum fun m (_ : m ∈ (univ : Finset H)) =>
      mul_le_mul_of_nonneg_left (hJ m) halpha.le
    simpa only [sum_const, card_univ, hc, nsmul_eq_mul, mul_left_comm, mul_assoc] using hs
  · apply tendsto_finsetSum
    intro m _
    exact (tendsto_shiftedPrimeFactor halpha m.val).mul (hb m)
  · have hall : ∀ᶠ N : ℕ in atTop, ∀ m : H, b m N ≤
        s2YArithmeticCoefficient H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
          (dyadicY (L := L) e alpha N) m / sieveCoordinateScale alpha N ^ (k + 1) :=
      eventually_all.mpr hble
    filter_upwards [hall, eventually_sieveCoordinateScale_pos halpha,
      eventually_gt_atTop 0] with N hall hA hN
    rw [s2YMain_normalized _ hN hA, hc]
    apply sum_le_sum
    intro m _
    apply mul_le_mul_of_nonneg_left (hall m)
    exact mul_nonneg (div_nonneg (shiftedPrimeIntervalCount_nonneg N m.val) (by positivity))
      (Real.log_natCast_nonneg _)

theorem exists_dyadic_sieveS2_lower_sequence {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) (hH : H.Nonempty) (hadm : BoundedGaps.IsAdmissible H)
    (hL : 0 < L) (hk : 2 ^ L ≤ k) {theta delta : ℝ}
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2) :
    ∃ J : ℝ, ∃ b : ℕ → ℝ, (theta / 2 - delta) * k * dyadicS2FiberConstant L k ≤ J ∧
      Tendsto b atTop (nhds J) ∧
      ∀ᶠ N : ℕ in atTop, b N ≤ primeWeightedSieveSum H N
        (sieveYWeight H (theta / 2 - delta) (dyadicY (L := L) e (theta / 2 - delta))
          (admissibleResidue hadm) N) / sieveScale H (theta / 2 - delta) N := by
  let alpha := theta / 2 - delta
  let y := dyadicY (L := L) e alpha
  let v := admissibleResidue hadm
  obtain ⟨J, b, hJ, hb, hble⟩ := exists_dyadic_s2Main_lower_sequence e hL hk
    (show 0 < alpha by dsimp [alpha]; linarith)
  have herr := tendsto_normalized_s2YError hH htheta hthetaHalf hdelta hdeltaTheta
    (dyadicWeightBound_nonneg L k) y v (dyadicY_supported e alpha) (abs_dyadicY_le e alpha)
    (admissibleResidue_coprime hadm)
  refine ⟨J, fun N => b N + s2YError H alpha y v N / sieveScale H alpha N, hJ, ?_, ?_⟩
  · simpa using hb.add herr
  · filter_upwards [hble, eventually_sieveS2_eq_main_add_error hthetaHalf hdelta hdeltaTheta y v]
      with N hN heq
    rw [heq, add_div]
    exact add_le_add hN le_rfl

end Erdos237
