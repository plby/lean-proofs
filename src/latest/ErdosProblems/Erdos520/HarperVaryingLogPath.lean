import ErdosProblems.Erdos520.HarperFairEulerProduct
import ErdosProblems.Erdos520.HarperScheduledOffDiagonal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# True logarithmic paths at varying mesh heights

The global Harper event is expressed using actual Euler factors, whereas the
Gaussian comparison is expressed using centered linear block sums.  This
file gives the deterministic bridge for a different evaluation height in
each scheduled block.  The total Taylor error is bounded by one summable
prime tail, uniformly in the number of blocks.
-/

theorem harperCoordinateLogIncrement_eq_half_log_factor
    (p : Nat) (u : Real) (b : Bool) :
    harperCoordinateLogIncrement p u b =
      (1 / 2 : Real) * Real.log (harperCoordinateFactor p u b) := by
  simpa only [harperCoordinateLogIncrement, harperCoordinateFactor] using!
    harperLogPrimeIncrement_eq_half_log_factor (fun _ => b) p u

theorem log_harperCoordinateFactor_eq_two_mul_logIncrement
    (p : Nat) (u : Real) (b : Bool) :
    Real.log (harperCoordinateFactor p u b) =
      2 * harperCoordinateLogIncrement p u b := by
  rw [harperCoordinateLogIncrement_eq_half_log_factor]
  ring

/-- The logarithm of one squared block energy is twice the true amplitude
logarithm over that block. -/
theorem log_harperEulerBlockEnergy_eq_two_mul_logBlockSum
    (y : Nat) (S : Finset (HarperPrimeIndex y))
    (u : Real) (eta : HarperPrimeCube y) :
    Real.log
        (∏ p ∈ S, harperCoordinateFactor p.1 u (eta p)) =
      2 * harperLogBlockSum y S u eta := by
  rw [Real.log_prod]
  · unfold harperLogBlockSum
    calc
      (∑ p ∈ S, Real.log (harperCoordinateFactor p.1 u (eta p))) =
          ∑ p ∈ S, 2 * harperCoordinateLogIncrement p.1 u (eta p) := by
        apply Finset.sum_congr rfl
        intro p hpS
        exact log_harperCoordinateFactor_eq_two_mul_logIncrement
          p.1 u (eta p)
      _ = 2 * ∑ p ∈ S,
          harperCoordinateLogIncrement p.1 u (eta p) := by
        rw [Finset.mul_sum]
  · intro p hpS
    unfold harperCoordinateFactor
    exact (harperEulerFactor_pos (fun _ => eta p)
      (Nat.prime_of_mem_primesBelow p.property) u).ne'

/-- True logarithmic block increments along a varying-height path. -/
noncomputable def harperScheduledLogBlockVectorVarying
    (y start n : Nat) (u : Fin n -> Real) :
    HarperPrimeCube y -> (Fin n -> Real) :=
  fun eta i => harperLogBlockSum y
    (harperScheduledPrimeBlock y (start + (i : Nat))) (u i) eta

/-- Centered linear block increments under a fixed tilt and varying
evaluation heights. -/
noncomputable def harperScheduledCenteredBlockVectorVarying
    (y start n : Nat) (t : Real) (u : Fin n -> Real) :
    HarperPrimeCube y -> (Fin n -> Real) :=
  fun eta i => harperCenteredLinearPrimeBlockSum y
    (harperScheduledPrimeBlock y (start + (i : Nat))) t (u i) eta

/-- Quadratic tilted drift of each varying-height block. -/
noncomputable def harperScheduledMainMeanVectorVarying
    (y start n : Nat) (t : Real) (u : Fin n -> Real) : Fin n -> Real :=
  fun i => harperLogMainBlockMean y
    (harperScheduledPrimeBlock y (start + (i : Nat))) t (u i)

/-- Exact logarithm of the whole scheduled varying-height squared Euler
product. -/
theorem log_harperScheduledVaryingEulerEnergy_eq_two_mul_sum_logBlockVector
    (y start n : Nat) (u : Fin n -> Real) (eta : HarperPrimeCube y) :
    Real.log (harperScheduledVaryingEulerEnergy y start n u eta) =
      2 * ∑ i : Fin n,
        harperScheduledLogBlockVectorVarying y start n u eta i := by
  unfold harperScheduledVaryingEulerEnergy
  rw [Real.log_prod]
  · calc
      (∑ i : Fin n,
          Real.log
            (∏ p ∈ harperScheduledPrimeBlock y (start + (i : Nat)),
              harperCoordinateFactor p.1 (u i) (eta p))) =
          ∑ i : Fin n,
            2 * harperScheduledLogBlockVectorVarying
              y start n u eta i := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact log_harperEulerBlockEnergy_eq_two_mul_logBlockSum y
          (harperScheduledPrimeBlock y (start + (i : Nat))) (u i) eta
      _ = 2 * ∑ i : Fin n,
          harperScheduledLogBlockVectorVarying y start n u eta i := by
        rw [Finset.mul_sum]
  · intro i _hi
    exact (Finset.prod_pos fun p hp =>
      (show 0 < harperCoordinateFactor p.1 (u i) (eta p) by
        unfold harperCoordinateFactor
        exact harperEulerFactor_pos (fun _ => eta p)
          (Nat.prime_of_mem_primesBelow p.property) (u i))).ne'

theorem sum_harperScheduledBlockCubicRemainder_eq_rangeFrom
    (y start n : Nat) :
    (∑ i : Fin n,
        harperBlockCubicRemainder y
          (harperScheduledPrimeBlock y (start + (i : Nat)))) =
      harperBlockCubicRemainder y
        (harperScheduledPrimeRangeFrom y start n) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : Nat => harperBlockCubicRemainder y
      (harperScheduledPrimeBlock y (start + k))) n]
  have h := Finset.sum_biUnion
    (f := fun p : HarperPrimeIndex y =>
      (2 / 3 : Real) * (Real.sqrt (p.1 : Real))⁻¹ ^ 3)
    (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)
  simpa only [harperScheduledPrimeRangeFrom,
    harperBlockCubicRemainder] using! h.symm

/-- The entire varying-height logarithmic path differs from its centered
linear path plus deterministic drift by one start-scale tail. -/
theorem abs_sum_harperScheduledLogBlockVectorVarying_sub_centered_add_mean_le
    (y start n : Nat) (t : Real) (u : Fin n -> Real)
    (eta : HarperPrimeCube y) :
    |(∑ i : Fin n,
        harperScheduledLogBlockVectorVarying y start n u eta i) -
      ((∑ i : Fin n,
          harperScheduledCenteredBlockVectorVarying y start n t u eta i) +
        ∑ i : Fin n,
          harperScheduledMainMeanVectorVarying y start n t u i)| <=
      (4 / 3 : Real) *
        (Real.sqrt (harperBlockEndpoint start : Real))⁻¹ := by
  rw [<- Finset.sum_add_distrib, <- Finset.sum_sub_distrib]
  calc
    |∑ i : Fin n,
        (harperScheduledLogBlockVectorVarying y start n u eta i -
          (harperScheduledCenteredBlockVectorVarying
              y start n t u eta i +
            harperScheduledMainMeanVectorVarying y start n t u i))| <=
        ∑ i : Fin n,
          |harperScheduledLogBlockVectorVarying y start n u eta i -
            (harperScheduledCenteredBlockVectorVarying
                y start n t u eta i +
              harperScheduledMainMeanVectorVarying y start n t u i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i : Fin n,
        harperBlockCubicRemainder y
          (harperScheduledPrimeBlock y (start + (i : Nat))) := by
      exact Finset.sum_le_sum fun i _hi =>
        abs_harperLogBlockSum_sub_centered_add_mean_le y
          (harperScheduledPrimeBlock y (start + (i : Nat)))
          (fun p hp => by
            have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
            omega)
          t (u i) eta
    _ = harperBlockCubicRemainder y
        (harperScheduledPrimeRangeFrom y start n) :=
      sum_harperScheduledBlockCubicRemainder_eq_rangeFrom y start n
    _ <= (4 / 3 : Real) *
        (Real.sqrt (harperBlockEndpoint start : Real))⁻¹ :=
      harperBlockCubicRemainder_rangeFrom_le y start n

/-- Prefix version of the same error bound, phrased with the path partial
sum used by all barrier sets. -/
theorem abs_harperScheduledLogPathPartialSum_sub_centered_add_mean_le
    (y start n : Nat) (t : Real) (u : Fin n -> Real)
    (eta : HarperPrimeCube y) (k : Fin n) :
    |harperPathPartialSum
        (harperScheduledLogBlockVectorVarying y start n u eta) k -
      (harperPathPartialSum
          (harperScheduledCenteredBlockVectorVarying
            y start n t u eta) k +
        ∑ i ∈ Finset.Iic k,
          harperScheduledMainMeanVectorVarying y start n t u i)| <=
      (4 / 3 : Real) *
        (Real.sqrt (harperBlockEndpoint start : Real))⁻¹ := by
  unfold harperPathPartialSum
  rw [<- Finset.sum_add_distrib, <- Finset.sum_sub_distrib]
  calc
    |∑ i ∈ Finset.Iic k,
        (harperScheduledLogBlockVectorVarying y start n u eta i -
          (harperScheduledCenteredBlockVectorVarying
              y start n t u eta i +
            harperScheduledMainMeanVectorVarying y start n t u i))| <=
        ∑ i ∈ Finset.Iic k,
          |harperScheduledLogBlockVectorVarying y start n u eta i -
            (harperScheduledCenteredBlockVectorVarying
                y start n t u eta i +
              harperScheduledMainMeanVectorVarying y start n t u i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i ∈ Finset.Iic k,
        harperBlockCubicRemainder y
          (harperScheduledPrimeBlock y (start + (i : Nat))) := by
      exact Finset.sum_le_sum fun i hi =>
        abs_harperLogBlockSum_sub_centered_add_mean_le y
          (harperScheduledPrimeBlock y (start + (i : Nat)))
          (fun p hp => by
            have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
            omega)
          t (u i) eta
    _ <= ∑ i : Fin n,
        harperBlockCubicRemainder y
          (harperScheduledPrimeBlock y (start + (i : Nat))) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Iic k).subset_univ
        (fun i _hi _hnot => harperBlockCubicRemainder_nonneg y _)
    _ = harperBlockCubicRemainder y
        (harperScheduledPrimeRangeFrom y start n) :=
      sum_harperScheduledBlockCubicRemainder_eq_rangeFrom y start n
    _ <= (4 / 3 : Real) *
        (Real.sqrt (harperBlockEndpoint start : Real))⁻¹ :=
      harperBlockCubicRemainder_rangeFrom_le y start n

end Problem520
end Erdos
