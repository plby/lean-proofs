/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Screening

/-!
# Finite gap-screening machinery for Erdős Problem 1165

This file isolates the part of Hao--Li--Okada--Zheng Lemma 4.10 which is
independent of the planar-walk estimates.  After conditioning on the external
walk, the proof has the following finite form.

* The possible local-time deficits are divided into finitely many bands.
* Each band has a finite list of candidate sites.
* The gap event is covered by the event that some listed candidate accumulates
  a prescribed number of returns before the old favorite is hit.
* If one return avoids the old favorite with probability at most `1 - p`, then
  `h` successive returns cost at most `(1-p)^h`, hence at most `exp (-p*h)`.
* A union bound multiplies the one-candidate cost by the candidate budget and
  then sums over the deficit bands.

The two random-walk inputs are deliberately named hypotheses below:
`CandidateCountBound` and `PerCandidateReturnCostBound` (or its geometric
specialization `PerCandidateGeometricReturnBound`).  Thus no planar hitting
estimate, stopping-time enumeration, or conclusion of Lemma 4.10 is hidden in
this module.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.Gap

/-! ## Finite deficit bands and their candidate events -/

section FiniteUnion

variable {Ω Band Candidate : Type*}

/-- In one deficit band, at least one of its listed candidates realizes its
return event. -/
def someBandCandidateSucceeds (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) (band : Band) : Set Ω :=
  Screening.someCandidateBad (candidates band) (succeeds band)

/-- At least one listed candidate in one of the finitely many deficit bands
realizes its return event. -/
def someGapCandidateSucceeds (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) : Set Ω :=
  Screening.someCandidateBad bands (someBandCandidateSucceeds candidates succeeds)

@[simp] theorem mem_someBandCandidateSucceeds
    {candidates : Band → Finset Candidate}
    {succeeds : Band → Candidate → Set Ω} {band : Band} {ω : Ω} :
    ω ∈ someBandCandidateSucceeds candidates succeeds band ↔
      ∃ x ∈ candidates band, ω ∈ succeeds band x := by
  simp [someBandCandidateSucceeds, Screening.someCandidateBad]

@[simp] theorem mem_someGapCandidateSucceeds
    {bands : Finset Band} {candidates : Band → Finset Candidate}
    {succeeds : Band → Candidate → Set Ω} {ω : Ω} :
    ω ∈ someGapCandidateSucceeds bands candidates succeeds ↔
      ∃ band ∈ bands, ∃ x ∈ candidates band, ω ∈ succeeds band x := by
  simp [someGapCandidateSucceeds, someBandCandidateSucceeds,
    Screening.someCandidateBad]

/-- The deterministic stopping-time enumeration input in the gap argument:
every realization of the target gap event is witnessed by a listed candidate
in one of the chosen deficit bands. -/
def GapEventCovered (gapEvent : Set Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) : Prop :=
  gapEvent ⊆ someGapCandidateSucceeds bands candidates succeeds

/-- The candidate-count input, normally supplied band by band by HLOZ
Proposition 4.8 after conditioning on the external walk. -/
def CandidateCountBound (bands : Finset Band)
    (candidates : Band → Finset Candidate) (budget : Band → ℕ) : Prop :=
  ∀ band ∈ bands, (candidates band).card ≤ budget band

variable [MeasurableSpace Ω]

/-- The one-candidate return-cost input.  In the random-walk application this
comes from the strong Markov property and a one-return hitting estimate. -/
def PerCandidateReturnCostBound (μ : Measure Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) (cost : Band → ℝ≥0∞) : Prop :=
  ∀ band ∈ bands, ∀ x ∈ candidates band, μ (succeeds band x) ≤ cost band

/-- The nested finite union bound in the exact form needed by the gap lemma.
It first sums over candidates in a band and then over deficit bands. -/
theorem measure_gapEvent_le_sum_budget_mul_cost
    (μ : Measure Ω) (gapEvent : Set Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) (budget : Band → ℕ)
    (cost : Band → ℝ≥0∞)
    (hcover : GapEventCovered gapEvent bands candidates succeeds)
    (hcount : CandidateCountBound bands candidates budget)
    (hcost : PerCandidateReturnCostBound μ bands candidates succeeds cost) :
    μ gapEvent ≤ ∑ band ∈ bands, (budget band : ℝ≥0∞) * cost band := by
  calc
    μ gapEvent ≤ μ (someGapCandidateSucceeds bands candidates succeeds) :=
      measure_mono hcover
    _ ≤ ∑ band ∈ bands,
        μ (someBandCandidateSucceeds candidates succeeds band) :=
      Screening.measure_someCandidateBad_le_sum μ bands
        (someBandCandidateSucceeds candidates succeeds)
    _ ≤ ∑ band ∈ bands, (budget band : ℝ≥0∞) * cost band := by
      apply Finset.sum_le_sum
      intro band hband
      exact Screening.measure_someCandidateBad_le_budget μ (candidates band)
        (succeeds band) (budget band) (cost band) (hcount band hband)
        (hcost band hband)

end FiniteUnion

/-! ## Geometric avoidance and its exponential form -/

/-- The geometric upper bound for `returns` successful revisits when each
revisit avoids the old favorite with chance at most `1 - escapeChance`. -/
noncomputable def geometricReturnCost (escapeChance : ℝ) (returns : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - escapeChance) ^ returns)

/-- The exponential relaxation of `geometricReturnCost`. -/
noncomputable def exponentialReturnCost (escapeChance : ℝ) (returns : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(escapeChance * returns)))

/-- The elementary inequality behind HLOZ (7.10): repeated avoidance has an
exponential cost. -/
theorem one_sub_pow_le_exp_neg_mul {escapeChance : ℝ}
    (_hzero : 0 ≤ escapeChance) (hone : escapeChance ≤ 1) (returns : ℕ) :
    (1 - escapeChance) ^ returns ≤
      Real.exp (-(escapeChance * returns)) := by
  calc
    (1 - escapeChance) ^ returns ≤ (Real.exp (-escapeChance)) ^ returns :=
      pow_le_pow_left₀ (sub_nonneg.mpr hone)
        (Real.one_sub_le_exp_neg escapeChance) returns
    _ = Real.exp (-(escapeChance * returns)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- `ENNReal` form of `one_sub_pow_le_exp_neg_mul`, suitable for comparison
with a measure. -/
theorem geometricReturnCost_le_exponentialReturnCost {escapeChance : ℝ}
    (hzero : 0 ≤ escapeChance) (hone : escapeChance ≤ 1) (returns : ℕ) :
    geometricReturnCost escapeChance returns ≤
      exponentialReturnCost escapeChance returns := by
  exact ENNReal.ofReal_le_ofReal
    (one_sub_pow_le_exp_neg_mul hzero hone returns)

section GeometricUnion

variable {Ω Band Candidate : Type*} [MeasurableSpace Ω]

/-- The random-walk-specific per-candidate hypothesis in geometric form.
The proof that a concrete stopped walk satisfies it is intentionally outside
this finite module. -/
def PerCandidateGeometricReturnBound (μ : Measure Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω)
    (escapeChance : Band → ℝ) (requiredReturns : Band → ℕ) : Prop :=
  ∀ band ∈ bands, ∀ x ∈ candidates band,
    μ (succeeds band x) ≤
      geometricReturnCost (escapeChance band) (requiredReturns band)

/-- Candidate counting plus the geometric one-candidate estimate gives a
finite sum of geometric costs. -/
theorem measure_gapEvent_le_geometric_sum
    (μ : Measure Ω) (gapEvent : Set Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) (budget : Band → ℕ)
    (escapeChance : Band → ℝ) (requiredReturns : Band → ℕ)
    (hcover : GapEventCovered gapEvent bands candidates succeeds)
    (hcount : CandidateCountBound bands candidates budget)
    (hreturn : PerCandidateGeometricReturnBound μ bands candidates succeeds
      escapeChance requiredReturns) :
    μ gapEvent ≤ ∑ band ∈ bands, (budget band : ℝ≥0∞) *
      geometricReturnCost (escapeChance band) (requiredReturns band) := by
  exact measure_gapEvent_le_sum_budget_mul_cost μ gapEvent bands candidates succeeds
    budget (fun band ↦ geometricReturnCost (escapeChance band) (requiredReturns band))
    hcover hcount hreturn

/-- Exponential version of the finite-band gap bound. -/
theorem measure_gapEvent_le_exponential_sum
    (μ : Measure Ω) (gapEvent : Set Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) (budget : Band → ℕ)
    (escapeChance : Band → ℝ) (requiredReturns : Band → ℕ)
    (hcover : GapEventCovered gapEvent bands candidates succeeds)
    (hcount : CandidateCountBound bands candidates budget)
    (hreturn : PerCandidateGeometricReturnBound μ bands candidates succeeds
      escapeChance requiredReturns)
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1) :
    μ gapEvent ≤ ∑ band ∈ bands, (budget band : ℝ≥0∞) *
      exponentialReturnCost (escapeChance band) (requiredReturns band) := by
  refine (measure_gapEvent_le_geometric_sum μ gapEvent bands candidates succeeds
    budget escapeChance requiredReturns hcover hcount hreturn).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  gcongr
  exact geometricReturnCost_le_exponentialReturnCost
    (hzero band hband) (hone band hband) (requiredReturns band)

/-- If every candidate-budget/exponential-cost product is at most `q`, the
remaining loss is only the number of deficit bands. -/
theorem measure_gapEvent_le_card_bands_mul
    (μ : Measure Ω) (gapEvent : Set Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) (budget : Band → ℕ)
    (escapeChance : Band → ℝ) (requiredReturns : Band → ℕ) (q : ℝ≥0∞)
    (hcover : GapEventCovered gapEvent bands candidates succeeds)
    (hcount : CandidateCountBound bands candidates budget)
    (hreturn : PerCandidateGeometricReturnBound μ bands candidates succeeds
      escapeChance requiredReturns)
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1)
    (hband : ∀ band ∈ bands, (budget band : ℝ≥0∞) *
      exponentialReturnCost (escapeChance band) (requiredReturns band) ≤ q) :
    μ gapEvent ≤ (bands.card : ℝ≥0∞) * q := by
  refine (measure_gapEvent_le_exponential_sum μ gapEvent bands candidates succeeds
    budget escapeChance requiredReturns hcover hcount hreturn hzero hone).trans ?_
  calc
    ∑ band ∈ bands, (budget band : ℝ≥0∞) *
        exponentialReturnCost (escapeChance band) (requiredReturns band) ≤
        ∑ _band ∈ bands, q := Finset.sum_le_sum hband
    _ = (bands.card : ℝ≥0∞) * q := by simp

end GeometricUnion

/-! ## The negative exponential beating the candidate budget -/

/-- Real-valued arithmetic used after the HLOZ choices of deficit exponents:
if `exponent` exceeds `log J + target`, then the candidate factor `J` is
absorbed by the negative exponential. -/
theorem nat_mul_exp_neg_le_exp_neg {J : ℕ} (hJ : 0 < J)
    {exponent target : ℝ} (hdominates : Real.log J + target ≤ exponent) :
    (J : ℝ) * Real.exp (-exponent) ≤ Real.exp (-target) := by
  calc
    (J : ℝ) * Real.exp (-exponent) =
        Real.exp (Real.log J) * Real.exp (-exponent) := by
      rw [Real.exp_log (by exact_mod_cast hJ : (0 : ℝ) < J)]
    _ = Real.exp (Real.log J + -exponent) := by
      rw [Real.exp_add]
    _ =
        Real.exp (Real.log J - exponent) := by
      rfl
    _ ≤ Real.exp (-target) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- `ENNReal` lifting of `nat_mul_exp_neg_le_exp_neg`. -/
theorem ennreal_nat_mul_exp_neg_le_exp_neg {J : ℕ} (hJ : 0 < J)
    {exponent target : ℝ} (hdominates : Real.log J + target ≤ exponent) :
    (J : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-exponent)) ≤
      ENNReal.ofReal (Real.exp (-target)) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (nat_mul_exp_neg_le_exp_neg hJ hdominates)

/-- A convenient checked endgame for the finite gap argument.  The hypothesis
`hdominates` is precisely where the HLOZ exponent calculation enters: in each
band the negative return exponent must dominate the logarithm of the candidate
budget plus a common target exponent. -/
theorem measure_gapEvent_le_card_bands_mul_exp_neg
    {Ω Band Candidate : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (gapEvent : Set Ω) (bands : Finset Band)
    (candidates : Band → Finset Candidate)
    (succeeds : Band → Candidate → Set Ω) (budget : Band → ℕ)
    (escapeChance : Band → ℝ) (requiredReturns : Band → ℕ) (target : ℝ)
    (hcover : GapEventCovered gapEvent bands candidates succeeds)
    (hcount : CandidateCountBound bands candidates budget)
    (hreturn : PerCandidateGeometricReturnBound μ bands candidates succeeds
      escapeChance requiredReturns)
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1)
    (hdominates : ∀ band ∈ bands, 0 < budget band →
      Real.log (budget band) + target ≤
        escapeChance band * requiredReturns band) :
    μ gapEvent ≤ (bands.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-target)) := by
  apply measure_gapEvent_le_card_bands_mul μ gapEvent bands candidates succeeds
    budget escapeChance requiredReturns (ENNReal.ofReal (Real.exp (-target)))
    hcover hcount hreturn hzero hone
  intro band hband
  by_cases hbudget : budget band = 0
  · simp [hbudget]
  · exact ennreal_nat_mul_exp_neg_le_exp_neg (Nat.pos_of_ne_zero hbudget)
      (hdominates band hband (Nat.pos_of_ne_zero hbudget))

end Erdos1165.Gap
