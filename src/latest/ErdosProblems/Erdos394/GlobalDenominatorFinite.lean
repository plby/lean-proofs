import ErdosProblems.Erdos394.SimplifiedFixedQDenominator
import ErdosProblems.Erdos394.PrimeWeightedBlockLower
import ErdosProblems.Erdos394.ParameterFloor
import ErdosProblems.Erdos394.WeightedSubsetTruncation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite global denominator lower bound
-/

open Nat Finset

namespace Erdos394

/-- Canonical shifted-root horizon for a selected subset. -/
def selectedHorizon (K C0 : ℕ) (T : Finset ℕ) : ℕ :=
  primeProduct T / (C0 * K ^ (T.card + 1))

/-- Canonical base of the large-prime block attached to a selected subset. -/
def selectedPrimeBase (X : ℕ) (T : Finset ℕ) : ℕ :=
  X / (32 * primeProduct T)

/-- F-085 specialized to the canonical horizon and prime block. -/
theorem canonical_fixedQ_shiftedGood_lower
    (P T : Finset ℕ) (K C0 X R : ℕ)
    (hK : 0 < K) (hC0 : 0 < C0)
    (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ T, K < p)
    (hPupper : ∀ p ∈ P, p ≤ selectedPrimeBase X T)
    (hheight : 2 * K ≤ selectedHorizon K C0 T * selectedPrimeBase X T)
    (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)))
    {L : ℝ}
    (htotal : L ≤ primeIntervalWeightedMass (selectedPrimeBase X T)
      (16 * selectedPrimeBase X T)) :
    ((selectedHorizon K C0 T : ℕ) : ℝ) / 2 *
      (L - (((16 * selectedPrimeBase X T : ℕ) : ℝ) ^ 2 /
          (C0 : ℝ)) * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) -
        ((primeProduct T : ℝ) / (C0 : ℝ)) *
          ((truncatedSubsets (P \ T) R).card : ℝ) *
            (2 * ((16 * selectedPrimeBase X T : ℕ) : ℝ))) ≤
      shiftedGoodPrimeTMass T K (selectedHorizon K C0 T)
        (selectedPrimeBase X T) (16 * selectedPrimeBase X T)
        (fun p hp ↦ hprime p (hTP hp)) := by
  have hY : C0 * K ^ (T.card + 1) * selectedHorizon K C0 T ≤
      primeProduct T := by
    unfold selectedHorizon
    exact Nat.mul_div_le (primeProduct T) (C0 * K ^ (T.card + 1))
  have h := fixedQ_shiftedGoodPrimeTMass_lower_simplified
    P T K (selectedHorizon K C0 T) (selectedPrimeBase X T)
      (16 * selectedPrimeBase X T) R C0 hK hC0 hTP hprime hlarge
      hPupper hheight hR htail hY htotal
  convert h using 1 <;> ring

/-- If the two bad terms consume at most half the Chebyshev main term, the
canonical fixed-q contribution retains `Y L/4`. -/
theorem quarter_horizon_primeMain_le_canonical_mass
    (P T : Finset ℕ) (K C0 X R : ℕ)
    (hK : 0 < K) (hC0 : 0 < C0)
    (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ T, K < p)
    (hPupper : ∀ p ∈ P, p ≤ selectedPrimeBase X T)
    (hheight : 2 * K ≤ selectedHorizon K C0 T * selectedPrimeBase X T)
    (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)))
    (hbasepos : 0 < selectedPrimeBase X T)
    (hrecip : Real.log 2 /
        (16 * Real.log (selectedPrimeBase X T)) ≤
      primeReciprocalSum (16 * selectedPrimeBase X T) -
        primeReciprocalSum (selectedPrimeBase X T))
    (hbad : 2 *
      ((((16 * selectedPrimeBase X T : ℕ) : ℝ) ^ 2 /
          (C0 : ℝ)) * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
        ((primeProduct T : ℝ) / (C0 : ℝ)) *
          ((truncatedSubsets (P \ T) R).card : ℝ) *
            (2 * ((16 * selectedPrimeBase X T : ℕ) : ℝ))) ≤
      Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
        (16 * Real.log (selectedPrimeBase X T))) :
    ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
        (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
          (16 * Real.log (selectedPrimeBase X T))) ≤
      shiftedGoodPrimeTMass T K (selectedHorizon K C0 T)
        (selectedPrimeBase X T) (16 * selectedPrimeBase X T)
        (fun p hp ↦ hprime p (hTP hp)) := by
  let L : ℝ := Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
    (16 * Real.log (selectedPrimeBase X T))
  let E : ℝ := (((16 * selectedPrimeBase X T : ℕ) : ℝ) ^ 2 /
      (C0 : ℝ)) * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
    ((primeProduct T : ℝ) / (C0 : ℝ)) *
      ((truncatedSubsets (P \ T) R).card : ℝ) *
        (2 * ((16 * selectedPrimeBase X T : ℕ) : ℝ))
  have htotal : L ≤ primeIntervalWeightedMass (selectedPrimeBase X T)
      (16 * selectedPrimeBase X T) :=
    log_two_mul_sq_div_le_primeIntervalWeightedMass hbasepos hrecip
  have hfixed := canonical_fixedQ_shiftedGood_lower P T K C0 X R
    hK hC0 hTP hprime hlarge hPupper hheight hR htail htotal
  have hLE : L / 2 ≤ L - E := by
    dsimp [L, E] at hbad ⊢
    linarith
  have hY0 : 0 ≤ ((selectedHorizon K C0 T : ℕ) : ℝ) / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hLE hY0
  dsimp [E] at hscaled
  have hmid : ((selectedHorizon K C0 T : ℕ) : ℝ) / 2 * (L / 2) ≤
      shiftedGoodPrimeTMass T K (selectedHorizon K C0 T)
        (selectedPrimeBase X T) (16 * selectedPrimeBase X T)
        (fun p hp ↦ hprime p (hTP hp)) := by
    exact hscaled.trans (by
      simpa only [sub_add_eq_sub_sub] using hfixed)
  dsimp [L] at hmid
  convert hmid using 1 <;> ring

end Erdos394
