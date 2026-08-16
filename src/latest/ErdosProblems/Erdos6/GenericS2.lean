import ErdosProblems.Erdos6.GenericS1
import BoundedGaps.Maynard.ImprovedGPY.S2ActualError

/-!
# The second Maynard sieve moment for a finite tuple

This file starts the candidate-generic version of the `S₂` argument.  In
particular, none of the definitions below is tied to the 105-element tuple
used by the bundled bounded-gaps theorem.
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

theorem tupleMaynardS2SupportProof
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) :
    ∀ d ∈ tupleMaynardSupport H alpha N,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H
        (maynardRadius alpha N) (maynardModulus N) d := by
  classical
  intro d hd
  unfold tupleMaynardSupport BoundedGaps.Maynard.maynardDivisorTupleSupport at hd
  exact (Finset.mem_filter.mp hd).2

def tupleMaynardS2Main (H : Finset ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.compatiblePairRestrictedMainOuter H
    (tupleMaynardSupport H alpha N)
    (maynardRadius alpha N) (maynardModulus N) (v N) N
    (tupleMaynardCoefficient H alpha F N)
    (tupleMaynardS2SupportProof H alpha N)

def tupleMaynardS2Error (H : Finset ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.compatiblePairRestrictedErrorOuter H
    (tupleMaynardSupport H alpha N)
    (maynardRadius alpha N) (maynardModulus N) (v N) N
    (tupleMaynardCoefficient H alpha F N)
    (tupleMaynardS2SupportProof H alpha N)

theorem eventually_tupleMaynardS2_eq_main_add_error
    (H : Finset ℕ) {theta delta : ℝ} (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.primeWeightedSieveSum H N
          (tupleMaynardWeight H (theta / 2 - delta) v F N) =
        tupleMaynardS2Main H (theta / 2 - delta) v F N +
          tupleMaynardS2Error H (theta / 2 - delta) v F N := by
  classical
  filter_upwards [eventually_tupleMaynard_coverage H,
    BoundedGaps.Maynard.eventually_engelsmaMaynardRadius_le
      hthetaHalf hdelta hdeltaTheta] with N hcoverage hRN
  let D := tupleMaynardSupport H (theta / 2 - delta) N
  let lambda := tupleMaynardCoefficient H (theta / 2 - delta) F N
  have hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H
        (maynardRadius (theta / 2 - delta) N) (maynardModulus N) d := by
    intro d hd
    exact tupleMaynardS2SupportProof H (theta / 2 - delta) N d
      (by simpa [D] using hd)
  change BoundedGaps.Maynard.primeWeightedSieveSum H N
      (BoundedGaps.Maynard.preSievedSquareDivisorWeight H D lambda
        (v N) (maynardModulus N)) = _
  rw [BoundedGaps.Maynard.primeWeightedSieveSum_preSieved_eq_compatiblePrimeWeightedPairSum
    hD hcoverage]
  rw [BoundedGaps.Maynard.compatiblePrimeWeightedPairSum_eq_restrictedOuterMain_addError
    hD hRN]
  rfl

end

end Erdos6.Maynard
