import ErdosProblems.Erdos1038.PlatformAdjointAbelBoundary
import Mathlib.Analysis.Complex.AbelLimit

/-!
# Abel convergence of the full platform endpoint sequence

This file repackages the parity-split endpoint series as a single power
series and applies Abel's limit theorem to its boundary partial sums.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

/-- The full positive-frequency endpoint sequence.  Frequency zero is kept
separate as `f0`; positive frequencies acquire their value at angle `pi`.-/
def platformAbelEndpointSequence
    (coefficient : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * (-1 : ℝ) ^ n * coefficient n

@[simp] theorem platformAbelEndpointSequence_zero
    (coefficient : ℕ → ℝ) :
    platformAbelEndpointSequence coefficient 0 = 0 := by
  simp [platformAbelEndpointSequence]

@[simp] theorem platformAbelEndpointSequence_of_pos
    (coefficient : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    platformAbelEndpointSequence coefficient n =
      2 * (-1 : ℝ) ^ n * coefficient n := by
  simp [platformAbelEndpointSequence, Nat.ne_of_gt hn]

/-- The parity-split endpoint value is the power series of the full signed
positive-frequency endpoint sequence.-/
theorem platformAbelEndpointSeriesValue_eq_tsum_endpointSequence
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) :
    platformAbelEndpointSeriesValue f0 coefficient lambda =
      f0 + ∑' n : ℕ,
        platformAbelEndpointSequence coefficient n * lambda ^ n := by
  let term : ℕ → ℝ := fun n ↦
    platformAbelEndpointSequence coefficient n * lambda ^ n
  have hEvenBase : Summable (fun m : ℕ ↦
      2 * (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1)))) :=
    (summable_platformAbelEvenCoefficient hlambda hbound).mul_left 2
  have hEvenShift : Summable (fun m : ℕ ↦ term (2 * (m + 1))) := by
    exact hEvenBase.congr (fun m ↦ by
      dsimp only [term]
      rw [platformAbelEndpointSequence_of_pos coefficient (by omega)]
      simp only [pow_mul, neg_one_sq, one_pow]
      ring)
  have hEven : Summable (fun m : ℕ ↦ term (2 * m)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_eq, Nat.add_comm] using! hEvenShift
  have hOddBase : Summable (fun m : ℕ ↦
      -2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1))) :=
    (summable_platformAbelOddCoefficient hlambda hbound).mul_left (-2)
  have hOdd : Summable (fun m : ℕ ↦ term (2 * m + 1)) := by
    exact hOddBase.congr (fun m ↦ by
      dsimp only [term]
      rw [platformAbelEndpointSequence_of_pos coefficient (by omega)]
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
      ring)
  have hEvenTsum :
      (∑' m : ℕ, term (2 * m)) =
        ∑' m : ℕ,
          2 * (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) := by
    rw [hEven.tsum_eq_zero_add]
    dsimp only [term]
    rw [Nat.mul_zero, platformAbelEndpointSequence_zero, pow_zero,
      mul_one, zero_add]
    apply tsum_congr
    intro m
    rw [platformAbelEndpointSequence_of_pos coefficient (by omega)]
    simp only [pow_mul, neg_one_sq, one_pow]
    ring
  have hOddTsum :
      (∑' m : ℕ, term (2 * m + 1)) =
        -∑' m : ℕ,
          2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro m
    dsimp only [term]
    rw [platformAbelEndpointSequence_of_pos coefficient (by omega)]
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
    ring
  have hsplit :
      (∑' m : ℕ, term (2 * m)) + (∑' m : ℕ, term (2 * m + 1)) =
        ∑' n : ℕ, term n :=
    tsum_even_add_odd hEven hOdd
  rw [platformAbelEndpointSeriesValue, ← hsplit, hEvenTsum, hOddTsum]
  ring

/-- If the endpoint partial sums converge, then every interior Abel approach
converges to the same endpoint value.-/
theorem tendsto_platformAbelEndpointSeriesValue_of_partialSums
    {coefficient : ℕ → ℝ} {C f0 endpointLimit : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (hpartial : Tendsto
      (fun N ↦ ∑ n ∈ Finset.range N,
        platformAbelEndpointSequence coefficient n)
      atTop (nhds (endpointLimit - f0)))
    {lambda : ℕ → ℝ}
    (hlambda : InteriorAbelApproach lambda) :
    Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        f0 coefficient (lambda n))
      atTop (nhds endpointLimit) := by
  have hlambdaWithin : Tendsto lambda atTop (nhdsWithin 1 (Iio 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlambda.2, Eventually.of_forall (fun n ↦ by
      exact (abs_lt.mp (hlambda.1 n)).2)⟩
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hpartial
  have hseries := hAbel.comp hlambdaWithin
  have hsum := (tendsto_const_nhds :
    Tendsto (fun _n : ℕ ↦ f0) atTop (nhds f0)).add hseries
  have hsum' : Tendsto
      (fun n ↦ f0 + ∑' k : ℕ,
        platformAbelEndpointSequence coefficient k * lambda n ^ k)
      atTop (nhds endpointLimit) := by
    have hlimit : f0 + (endpointLimit - f0) = endpointLimit := by abel
    rw [hlimit] at hsum
    simpa only [Function.comp_apply] using! hsum
  apply hsum'.congr'
  filter_upwards with n
  exact (platformAbelEndpointSeriesValue_eq_tsum_endpointSequence
    (hlambda.1 n) hbound f0).symm

end

end Erdos1038
