import Util.MaynardTao.BFT.ProgressionWeights
import ErdosProblems.Erdos6.GenericS2Restricted

/-! # The second moment and its main term in a fixed progression -/

namespace MaynardBFT

open Filter Erdos6.Maynard BoundedGaps.Maynard
open scoped BigOperators

noncomputable section

def progressionS2Main (H : Finset ℕ) (q : ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  compatiblePairRestrictedMainOuter H (progressionSupport H q alpha N)
    (maynardRadius alpha N) (progressionModulus q N) (v N) N
    (progressionCoefficient H q alpha F N) (progressionSupport_valid H q alpha N)

def progressionS2Error (H : Finset ℕ) (q : ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  compatiblePairRestrictedErrorOuter H (progressionSupport H q alpha N)
    (maynardRadius alpha N) (progressionModulus q N) (v N) N
    (progressionCoefficient H q alpha F N) (progressionSupport_valid H q alpha N)

theorem eventually_progressionS2_eq_main_add_error
    (H : Finset ℕ) (q : ℕ) {theta delta : ℝ} (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      primeWeightedSieveSum H N (progressionWeight H q (theta / 2 - delta) v F N) =
        progressionS2Main H q (theta / 2 - delta) v F N +
          progressionS2Error H q (theta / 2 - delta) v F N := by
  filter_upwards [eventually_progression_coverage H q,
    eventually_engelsmaMaynardRadius_le hthetaHalf hdelta hdeltaTheta] with N hcoverage hRN
  unfold progressionWeight
  rw [primeWeightedSieveSum_preSieved_eq_compatiblePrimeWeightedPairSum
    (progressionSupport_valid H q (theta / 2 - delta) N) hcoverage]
  rw [compatiblePrimeWeightedPairSum_eq_restrictedOuterMain_addError
    (progressionSupport_valid H q (theta / 2 - delta) N) hRN]
  rfl

theorem restrictedMainCoefficient_eq_invTotient
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (lambda : (H → ℕ) → ℝ) (m : H) :
    restrictedMainArithmeticCoefficient H D W lambda m =
      (W.totient : ℝ)⁻¹ *
        compatibleDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m := by
  unfold restrictedMainArithmeticCoefficient
  rw [restrictedDivisorPairModulusTotientSum_eq_invTotient_mul]
  · congr 1
    exact compatibleDivisorPairRestrictedTotientKernel_eq_commonDivisorS2TupleSum m hD
  · exact hD

theorem eventually_progressionS2Main_eq {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) (alpha : ℝ) (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      progressionS2Main H q alpha v F N = tupleMaynardS2Main H alpha v F N / q := by
  filter_upwards [eventually_progression_support_eq hq H alpha,
    eventually_progression_coefficient_eq hq H alpha F,
    tendsto_shifted_tripleLogCutoff.eventually (eventually_ge_atTop q)]
    with N hsupport hcoeff hcut
  unfold progressionS2Main
  rw [compatiblePairRestrictedMainOuter_eq_shift_sum
    (progressionSupport_valid H q alpha N), tupleMaynardS2Main_eq_shift_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [restrictedMainCoefficient_eq_invTotient (progressionSupport_valid H q alpha N),
    hsupport, hcoeff, tupleRestrictedMainCoefficient_eq_invTotient_mul_GKernel]
  have hphi : (progressionModulus q N).totient = q * (maynardModulus N).totient :=
    totient_mul_primorial hq hcut
  rw [hphi, Nat.cast_mul]
  unfold tupleRestrictedGKernel tupleShiftedPrimeIntervalCount
  ring

end

end MaynardBFT
