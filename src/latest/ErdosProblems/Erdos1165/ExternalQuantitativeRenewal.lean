/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.QuantitativeRenewal
import ErdosProblems.Erdos1165.ExternalGreenTail

/-!
# Quantitative renewal bounds for the external walk

This file specializes the generic distant-horizon renewal theorem to the
retained-block external walk.  Its hypotheses concern only the return
coefficients: after subtracting `c/k`, one needs a bound on one partial
remainder and on one remainder increment.  The conclusion is first a lower
bound on the probability of no return, and then the geometric upper tail for
the origin local time.

In the HLOZ application the local central limit theorem supplies
`c = 15/(16π)` and a summable coefficient remainder.  No local-time-tail
estimate is assumed here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalQuantitativeRenewal

open ExternalWalk ExternalOnePoint LazyDecomposition
open Erdos1165.ExternalRenewal
open Erdos1165.QuantitativeRenewal

variable (o : Orientation)

/-! ## The genuine no-return event -/

/-- The external walk makes no positive return to the origin through time
`n`. -/
def externalNoReturnThrough (n : ℕ) : Set (ℕ → RetainedBlock o) :=
  {eta | ∀ k ∈ Finset.Icc 1 n, externalPosition o eta k ≠ 0}

lemma externalNoReturnThrough_eq_compl_firstReturnUnion (n : ℕ) :
    externalNoReturnThrough o n =
      (⋃ k ∈ Finset.Icc 1 n, externalFirstReturnAt o k)ᶜ := by
  ext eta
  constructor
  · intro hnone hfirst
    rw [Set.mem_iUnion₂] at hfirst
    obtain ⟨k, hk, hkfirst⟩ := hfirst
    exact hnone k hk hkfirst.2.1
  · intro hnone k hk hreturn
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    obtain ⟨j, hjk, hjfirst⟩ :=
      externalFirstReturnAt_exists_of_return o hkpos hreturn
    apply hnone
    rw [Set.mem_iUnion₂]
    exact ⟨j, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hjk).1,
        (Finset.mem_Icc.mp hjk).2.trans (Finset.mem_Icc.mp hk).2⟩, hjfirst⟩

lemma measurableSet_externalNoReturnThrough (n : ℕ) :
    MeasurableSet (externalNoReturnThrough o n) := by
  rw [externalNoReturnThrough_eq_compl_firstReturnUnion]
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro hk
  exact measurableSet_externalFirstReturnAt o k

/-- Exact ENNReal probability of the no-return event. -/
theorem externalNoReturnThrough_probability (n : ℕ) :
    externalBlocks o (externalNoReturnThrough o n) =
      1 - externalFirstReturnMassENNReal o n := by
  have hmeas : MeasurableSet
      (⋃ k ∈ Finset.Icc 1 n, externalFirstReturnAt o k) := by
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro hk
    exact measurableSet_externalFirstReturnAt o k
  have hunion :
      externalBlocks o (⋃ k ∈ Finset.Icc 1 n, externalFirstReturnAt o k) =
        ∑ k ∈ Finset.Icc 1 n,
          externalBlocks o (externalFirstReturnAt o k) := by
    apply measure_biUnion_finset
    · intro i hi j hj hij
      exact externalFirstReturnAt_pairwise_disjoint o hij
    · intro k hk
      exact measurableSet_externalFirstReturnAt o k
  rw [externalNoReturnThrough_eq_compl_firstReturnUnion,
    MeasureTheory.measure_compl hmeas (measure_ne_top _ _), measure_univ, hunion]
  rfl

/-- Real-valued form: the algebraic `noReturnMass` used by the generic
renewal theorem is exactly the probability of the external no-return event. -/
theorem externalNoReturnThrough_probability_toReal (n : ℕ) :
    (externalBlocks o (externalNoReturnThrough o n)).toReal =
      noReturnMass (externalFirstReturnProbability o) n := by
  rw [externalNoReturnThrough_probability,
    ENNReal.toReal_sub_of_le (externalFirstReturnMassENNReal_le_one o n)
      (by simp), ENNReal.toReal_one,
    externalFirstReturnMassENNReal_toReal]
  rfl

/-- The accumulated reciprocal-coefficient error for the external return
probabilities. -/
noncomputable def externalReciprocalRemainderSum (c : ℝ) (N : ℕ) : ℝ :=
  reciprocalRemainderSum (externalReturnProbability o) c N

/-- Quantitative no-return lower bound for the retained-block walk.  The
only non-structural inputs are the two displayed coefficient-remainder
bounds. -/
theorem externalNoReturnMass_lower_of_remainder
    (c E delta : ℝ) (n m : ℕ)
    (hc : 0 ≤ c)
    (hrem_global : externalReciprocalRemainderSum o c m ≤ E)
    (hrem_increment : externalReciprocalRemainderSum o c (n + m) -
      externalReciprocalRemainderSum o c m ≤ delta)
    (hdelta : c * (n : ℝ) / (m + 1 : ℝ) + delta ≤ 1) :
    (1 - (c * (n : ℝ) / (m + 1 : ℝ) + delta)) /
        (1 + c * (1 + Real.log m) + E) ≤
      noReturnMass (externalFirstReturnProbability o) n := by
  exact reciprocalCoefficient_noReturn_lower
    (externalFirstReturnProbability o) (externalReturnProbability o)
    (externalFirstReturnProbability_nonneg o)
    (externalReturnProbability_nonneg o)
    (externalFirstReturnProbability_zero o)
    (externalReturnProbability_zero o)
    (fun r hr ↦ externalReturnProbabilityReal_renewal o hr)
    c E delta n m hc hrem_global hrem_increment hdelta

/-- The preceding bound stated directly for the probability of the
measurable no-return event. -/
theorem externalNoReturnThrough_probability_lower_of_remainder
    (c E delta : ℝ) (n m : ℕ)
    (hc : 0 ≤ c)
    (hrem_global : externalReciprocalRemainderSum o c m ≤ E)
    (hrem_increment : externalReciprocalRemainderSum o c (n + m) -
      externalReciprocalRemainderSum o c m ≤ delta)
    (hdelta : c * (n : ℝ) / (m + 1 : ℝ) + delta ≤ 1) :
    (1 - (c * (n : ℝ) / (m + 1 : ℝ) + delta)) /
        (1 + c * (1 + Real.log m) + E) ≤
      (externalBlocks o (externalNoReturnThrough o n)).toReal := by
  rw [externalNoReturnThrough_probability_toReal]
  exact externalNoReturnMass_lower_of_remainder
    o c E delta n m hc hrem_global hrem_increment hdelta

/-- Equivalent upper bound on the probability of a first positive return
through time `n`. -/
theorem externalFirstReturnMass_upper_of_remainder
    (c E delta : ℝ) (n m : ℕ)
    (hc : 0 ≤ c)
    (hrem_global : externalReciprocalRemainderSum o c m ≤ E)
    (hrem_increment : externalReciprocalRemainderSum o c (n + m) -
      externalReciprocalRemainderSum o c m ≤ delta)
    (hdelta : c * (n : ℝ) / (m + 1 : ℝ) + delta ≤ 1) :
    externalFirstReturnMass o n ≤
      1 - (1 - (c * (n : ℝ) / (m + 1 : ℝ) + delta)) /
        (1 + c * (1 + Real.log m) + E) := by
  exact reciprocalCoefficient_firstReturn_upper
    (externalFirstReturnProbability o) (externalReturnProbability o)
    (externalFirstReturnProbability_nonneg o)
    (externalReturnProbability_nonneg o)
    (externalFirstReturnProbability_zero o)
    (externalReturnProbability_zero o)
    (fun r hr ↦ externalReturnProbabilityReal_renewal o hr)
    c E delta n m hc hrem_global hrem_increment hdelta

/-- The coefficient estimate combined with the exact excursion recursion.
This is the external-walk one-point local-time tail in the form used in
HLOZ's first screening step. -/
theorem externalOriginLocalTime_tail_le_of_remainder
    (r n m : ℕ) (c E delta : ℝ)
    (hc : 0 ≤ c)
    (hrem_global : externalReciprocalRemainderSum o c m ≤ E)
    (hrem_increment : externalReciprocalRemainderSum o c (n + m) -
      externalReciprocalRemainderSum o c m ≤ delta)
    (hdelta : c * (n : ℝ) / (m + 1 : ℝ) + delta ≤ 1) :
    externalBlocks o {eta | r + 1 ≤ externalOriginLocalTime o eta n} ≤
      (ENNReal.ofReal
        (1 - (1 - (c * (n : ℝ) / (m + 1 : ℝ) + delta)) /
          (1 + c * (1 + Real.log m) + E))) ^ r := by
  let B : ℝ :=
    1 - (1 - (c * (n : ℝ) / (m + 1 : ℝ) + delta)) /
      (1 + c * (1 + Real.log m) + E)
  have hreal : externalFirstReturnMass o n ≤ B := by
    exact externalFirstReturnMass_upper_of_remainder
      o c E delta n m hc hrem_global hrem_increment hdelta
  have hmass : 0 ≤ externalFirstReturnMass o n :=
    RenewalTail.firstReturnMass_nonneg
      (externalFirstReturnProbability_nonneg o) n
  have hB : 0 ≤ B := hmass.trans hreal
  have hENN : externalFirstReturnMassENNReal o n ≤ ENNReal.ofReal B := by
    apply (ENNReal.toReal_le_toReal
      (externalFirstReturnMassENNReal_ne_top o n) ENNReal.ofReal_ne_top).mp
    rw [externalFirstReturnMassENNReal_toReal o n, ENNReal.toReal_ofReal hB]
    exact hreal
  exact (externalReturnTail_le_firstReturnMass_pow o r n).trans
    (pow_le_pow_left' hENN r)

end Erdos1165.ExternalQuantitativeRenewal
