import ErdosProblems.Erdos237b.SieveS2Lower
import ErdosProblems.Erdos237b.MaynardBridge

/-!
# Unconditional qualitative prime tuples, sufficient for Erdős 237

The radius exponent is `1/8`, with prime level `3/8`. The coarse dyadic
construction only needs `L > 512*m` and `k ≥ 2^L`; no sharp threshold is used.
-/

namespace Erdos237b

open Finset Filter BoundedGaps BoundedGaps.Maynard

theorem dyadic_positive_sieve_excess {H : Finset ℕ} {L k m : ℕ}
    (e : H ≃ Fin k) (hadm : IsAdmissible H) (hL : 0 < L) (hk : 2 ^ L ≤ k)
    (hlarge : 512 * (m : ℝ) < L) : HasEventuallyPositiveSieveExcess H m := by
  have hkpos : 0 < k := (pow_pos (by decide) L).trans_le hk
  have hc : Fintype.card H = k := (Fintype.card_congr e).trans (Fintype.card_fin k)
  have hH : H.Nonempty := card_pos.mp (by simpa using (hc ▸ hkpos : 0 < Fintype.card H))
  obtain ⟨J, b, hJ, hb, hble⟩ := exists_dyadic_sieveS2_lower_sequence
    (theta := (3 / 8 : ℝ)) (delta := (1 / 16 : ℝ)) e hH hadm hL hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [show (3 / 8 : ℝ) / 2 - 1 / 16 = 1 / 8 by norm_num] at hJ hb hble
  apply hasEventuallyPositiveSieveExcess_of_lower_sequence
    (sieveYWeight H (1 / 8) (dyadicY (L := L) e (1 / 8)) (admissibleResidue hadm))
    (sieveScale H (1 / 8)) b
  · exact lt_of_lt_of_le (dyadic_sieve_margin hL hkpos hlarge) (sub_le_sub_right hJ _)
  · exact eventually_sieveScale_pos H (by norm_num)
  · exact sieveYWeight_nonneg H (1 / 8) _ _
  · exact tendsto_dyadic_sieveWeightSum hL hk e (by norm_num) (by norm_num) _
  · exact hb
  · exact hble

theorem qualitativePrimeTuples_unconditional : QualitativePrimeTuples := by
  apply qualitativePrimeTuples_of_positiveSieveExcess
  intro m
  let L := 512 * (m + 1)
  let k := 2 ^ L
  refine ⟨k, fun H hcard hadm => ?_⟩
  let e : H ≃ Fin k := Fintype.equivOfCardEq (by simpa using hcard)
  apply dyadic_positive_sieve_excess (L := L) e hadm (by dsimp [L]; omega) le_rfl
  dsimp [L]
  push_cast
  linarith

end Erdos237b
