import ErdosProblems.Erdos59.Core
import ErdosProblems.Erdos59.LowerConstruction
import ErdosProblems.Erdos59.BlowupFour
import ErdosProblems.Erdos59.NumericsFour
import ErdosProblems.Erdos59.WeakUpper

/-!
# The Morris--Saxton counterexample for Erdős problem 59

This file combines the two quantitative Füredi--Naor--Verstraëte estimates
with the four-fold matching blowup.  The constant is made completely
explicit: `c = 1 / 100`.
-/

namespace Erdos59

open SimpleGraph

private theorem matching_power_as_rpow (e : ℕ) :
    (209 ^ e : ℝ) = Real.rpow 2 (Real.logb 2 209 * (e : ℝ)) := by
  change (209 ^ e : ℝ) = (2 : ℝ) ^ (Real.logb 2 209 * (e : ℝ))
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) (by norm_num : (0 : ℝ) < 209)]
  rw [Real.rpow_natCast]

/-- The counting conclusion of Morris--Saxton, separated from the
graph-theoretic proof of the eventual FNV upper estimate. -/
private theorem morrisSaxtonArbitrarilyLarge_of_eventual_extremal_upper
    (hupper : ∀ᶠ n : ℕ in Filter.atTop,
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) <
        (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ)) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      Real.rpow 2
          ((1 + (1 / 100 : ℝ)) *
            (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ)) ≤
        (labelledFreeGraphCount (SimpleGraph.cycleGraph 6) n : ℝ) := by
  obtain ⟨Nupper, hNupper⟩ := Filter.eventually_atTop.mp hupper
  intro N
  obtain ⟨a, B, hm, htriangle, hC6, hedges⟩ :=
    LowerConstruction.infinitely_often (max (N + 1) Nupper)
  let : DecidableRel B.Adj := Classical.decRel _
  let m := fnvVertices a
  have hm_lower : max (N + 1) Nupper ≤ m := by simpa [m] using hm
  have hm_pos_nat : 0 < m := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos_nat
  have hmpow_pos : (0 : ℝ) < (m : ℝ) ^ (4 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hm_pos _
  have hn_upper : Nupper ≤ 4 * m := by omega
  have hex_upper := hNupper (4 * m) hn_upper
  have hfour_mul :
      ((4 * m : ℕ) : ℝ) ^ (4 / 3 : ℝ) =
        (4 : ℝ) ^ (4 / 3 : ℝ) * (m : ℝ) ^ (4 / 3 : ℝ) := by
    rw [Nat.cast_mul, Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    norm_num
  have hedges' :
      (2669 / 5000 : ℝ) * (m : ℝ) ^ (4 / 3 : ℝ) <
        (B.edgeFinset.card : ℝ) := by
    simpa [m] using hedges
  have hlog_pos : (0 : ℝ) < Real.logb 2 209 :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (1 : ℝ) < 209)
  have hconstant := numerical_four_certificate
  have hscaled := mul_lt_mul_of_pos_right hconstant hmpow_pos
  have hscaled' :
      ((1 + (1 / 100 : ℝ)) * (16 / 25 : ℝ) *
          (4 : ℝ) ^ (4 / 3 : ℝ)) *
        (m : ℝ) ^ (4 / 3 : ℝ) <
      ((2669 / 5000 : ℝ) * Real.logb 2 209) *
        (m : ℝ) ^ (4 / 3 : ℝ) := by
    simpa only [show (1 + (1 / 100 : ℝ)) = 101 / 100 by norm_num]
      using hscaled
  have hexponent :
      (1 + (1 / 100 : ℝ)) *
          (SimpleGraph.extremalNumber (4 * m)
            (SimpleGraph.cycleGraph 6) : ℝ) <
        Real.logb 2 209 * (B.edgeFinset.card : ℝ) := by
    rw [hfour_mul] at hex_upper
    have hupper_scaled := mul_lt_mul_of_pos_left hex_upper
      (by norm_num : (0 : ℝ) < 1 + 1 / 100)
    have hedge_scaled := mul_lt_mul_of_pos_left hedges' hlog_pos
    calc
      (1 + (1 / 100 : ℝ)) *
          (SimpleGraph.extremalNumber (4 * m)
            (SimpleGraph.cycleGraph 6) : ℝ) <
          (1 + (1 / 100 : ℝ)) *
            ((16 / 25 : ℝ) *
              ((4 : ℝ) ^ (4 / 3 : ℝ) *
                (m : ℝ) ^ (4 / 3 : ℝ))) := hupper_scaled
      _ = ((1 + (1 / 100 : ℝ)) * (16 / 25 : ℝ) *
            (4 : ℝ) ^ (4 / 3 : ℝ)) *
          (m : ℝ) ^ (4 / 3 : ℝ) := by ring
      _ < ((2669 / 5000 : ℝ) * Real.logb 2 209) *
          (m : ℝ) ^ (4 / 3 : ℝ) := hscaled'
      _ = Real.logb 2 209 *
          ((2669 / 5000 : ℝ) * (m : ℝ) ^ (4 / 3 : ℝ)) := by ring
      _ < Real.logb 2 209 * (B.edgeFinset.card : ℝ) := hedge_scaled
  have hcountNat := matchingBlowupFour_labelledFreeGraphCount_lower_bound B
    htriangle hC6
  have hcountReal :
      (209 ^ B.edgeFinset.card : ℝ) ≤
        (labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * m) : ℝ) := by
    exact_mod_cast hcountNat
  refine ⟨4 * m, by omega, ?_⟩
  calc
    Real.rpow 2
        ((1 + (1 / 100 : ℝ)) *
          (SimpleGraph.extremalNumber (4 * m)
            (SimpleGraph.cycleGraph 6) : ℝ))
        ≤ Real.rpow 2
            (Real.logb 2 209 * (B.edgeFinset.card : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent.le
    _ = (209 ^ B.edgeFinset.card : ℝ) :=
      (matching_power_as_rpow B.edgeFinset.card).symm
    _ ≤ (labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * m) : ℝ) :=
      hcountReal

/-- The explicit infinite subsequence on which the Morris--Saxton
improvement holds. -/
theorem morrisSaxtonLowerBoundIndices_cycleGraph_six :
    (lowerBoundIndices (SimpleGraph.cycleGraph 6) (1 / 100)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hbound⟩ :=
    morrisSaxtonArbitrarilyLarge_of_eventual_extremal_upper
      eventually_extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths (N + 1)
  exact ⟨n, hbound, by omega⟩

/-- The quantitative Morris--Saxton lower bound, witnessed explicitly by
`c = 1 / 100`. -/
theorem hasMorrisSaxtonLowerBound_cycleGraph_six :
    HasMorrisSaxtonLowerBound (SimpleGraph.cycleGraph 6) :=
  ⟨1 / 100, by norm_num, morrisSaxtonLowerBoundIndices_cycleGraph_six⟩

/-- Consequently the proposed `2 ^ ((1 + o(1)) ex(n,C₆))` upper bound is
false. -/
theorem morrisSaxtonDisprovesErdos59 :
    ¬ HasErdos59UpperBound (SimpleGraph.cycleGraph 6) :=
  hasMorrisSaxtonLowerBound_not_hasErdos59UpperBound
    hasMorrisSaxtonLowerBound_cycleGraph_six
    eventuallyPositiveExtremalNumber_cycleGraph_six

end Erdos59
