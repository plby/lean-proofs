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

import Mathlib

/-!
# Independent-block amplification for Erdős Problem 1165

This file supplies the measure-theoretic bookkeeping used after the one-block
thick-point construction in Hao--Li--Okada--Zheng.  It deliberately separates
that bookkeeping from the walk-specific estimates:

* an event proved before a random exit time is transferred to a deterministic
  time, at the price of the exit-time tail;
* a monotone statistic is interpolated from a checkpoint to an intermediate
  deterministic time;
* independent blocks turn a uniform one-block failure bound `q` into `q ^ N`;
* an exponential one-block bound and exponentially many blocks give a
  double-exponential failure bound.

All hypotheses below are explicit.  In particular, independence is expressed
by Mathlib's `ProbabilityTheory.iIndepSet`; no independence or random-walk
estimate is postulated in this module.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.BlockAmplification

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-! ## Passing from an exit-time construction to deterministic time -/

omit [MeasurableSpace Ω] in
/-- If success before the exit, together with exiting no later than `L`,
implies success by deterministic time `L`, then deterministic-time failure can
only arise from exit-time failure or a late exit. -/
theorem deterministicFailure_subset_exitFailure_union_late
    (exitSuccess timedSuccess : Set Ω) (exitTime : Ω → ℕ) (L : ℕ)
    (htransfer : exitSuccess ∩ {ω | exitTime ω ≤ L} ⊆ timedSuccess) :
    timedSuccessᶜ ⊆ exitSuccessᶜ ∪ {ω | L < exitTime ω} := by
  intro ω hω
  by_cases hsuccess : ω ∈ exitSuccess
  · right
    by_contra hlate
    have hexit : exitTime ω ≤ L := Nat.le_of_not_gt hlate
    exact hω (htransfer ⟨hsuccess, hexit⟩)
  · exact Or.inl hsuccess

/-- The real-valued union-bound form of
`deterministicFailure_subset_exitFailure_union_late`. -/
theorem measureReal_deterministicFailure_le_exitFailure_add_late
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (exitSuccess timedSuccess : Set Ω) (exitTime : Ω → ℕ) (L : ℕ)
    (htransfer : exitSuccess ∩ {ω | exitTime ω ≤ L} ⊆ timedSuccess) :
    μ.real timedSuccessᶜ ≤
      μ.real exitSuccessᶜ + μ.real {ω | L < exitTime ω} := by
  calc
    μ.real timedSuccessᶜ ≤
        μ.real (exitSuccessᶜ ∪ {ω | L < exitTime ω}) :=
      measureReal_mono
        (deterministicFailure_subset_exitFailure_union_late
          exitSuccess timedSuccess exitTime L htransfer)
    _ ≤ μ.real exitSuccessᶜ + μ.real {ω | L < exitTime ω} :=
      measureReal_union_le _ _

/-- Numerical form of the exit-time transfer: separate estimates for failure
of the stopped construction and for a late exit add. -/
theorem measureReal_deterministicFailure_le
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (exitSuccess timedSuccess : Set Ω) (exitTime : Ω → ℕ) (L : ℕ)
    {stoppedError exitError : ℝ}
    (htransfer : exitSuccess ∩ {ω | exitTime ω ≤ L} ⊆ timedSuccess)
    (hstopped : μ.real exitSuccessᶜ ≤ stoppedError)
    (hexit : μ.real {ω | L < exitTime ω} ≤ exitError) :
    μ.real timedSuccessᶜ ≤ stoppedError + exitError := by
  exact (measureReal_deterministicFailure_le_exitFailure_add_late
    μ exitSuccess timedSuccess exitTime L htransfer).trans (add_le_add hstopped hexit)

/-- A lower bound on a measurable success probability gives the corresponding
upper bound on its failure probability. -/
theorem measureReal_compl_le_one_sub_of_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (success : Set Ω)
    (hsuccess : MeasurableSet success) {p : ℝ}
    (hp : p ≤ μ.real success) :
    μ.real successᶜ ≤ 1 - p := by
  rw [probReal_compl_eq_one_sub hsuccess]
  exact sub_le_sub_left hp 1

/-! ## Interpolation between deterministic checkpoints -/

omit [MeasurableSpace Ω] in
/-- The bad event at an intermediate time is contained in a bad checkpoint
event whenever the statistic is pathwise monotone and the checkpoint level
dominates the desired intermediate level.  The separate `checkpointLevel`
parameter records the slack used in the HLOZ interpolation. -/
theorem badEvent_interpolation_subset
    (statistic : Ω → ℕ → ℝ) (threshold checkpointLevel : ℕ → ℝ)
    (checkpoint : ℕ → ℕ) (q n : ℕ)
    (hmono : ∀ ω, Monotone (statistic ω))
    (hcheckpoint : checkpoint q ≤ n)
    (hlevel : threshold n ≤ checkpointLevel q) :
    {ω | statistic ω n < threshold n} ⊆
      {ω | statistic ω (checkpoint q) < checkpointLevel q} := by
  intro ω hbad
  exact lt_of_le_of_lt (hmono ω hcheckpoint) (hbad.trans_le hlevel)

/-- A checkpoint probability estimate therefore controls every intermediate
time satisfying the two deterministic comparison hypotheses. -/
theorem measureReal_badEvent_interpolation_le
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (statistic : Ω → ℕ → ℝ) (threshold checkpointLevel : ℕ → ℝ)
    (checkpoint : ℕ → ℕ) (q n : ℕ)
    (hmono : ∀ ω, Monotone (statistic ω))
    (hcheckpoint : checkpoint q ≤ n)
    (hlevel : threshold n ≤ checkpointLevel q) :
    μ.real {ω | statistic ω n < threshold n} ≤
      μ.real {ω | statistic ω (checkpoint q) < checkpointLevel q} :=
  measureReal_mono
    (badEvent_interpolation_subset statistic threshold checkpointLevel checkpoint q n
      hmono hcheckpoint hlevel)

/-- Uniform interpolation over a range of times.  A caller supplies, for each
time, the checkpoint index and the two deterministic comparison estimates. -/
theorem measureReal_badEvent_interpolation_le_of_forall
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (statistic : Ω → ℕ → ℝ) (threshold checkpointLevel : ℕ → ℝ)
    (checkpoint checkpointIndex : ℕ → ℕ) (times : Set ℕ)
    (hmono : ∀ ω, Monotone (statistic ω))
    (hcheckpoint : ∀ n ∈ times, checkpoint (checkpointIndex n) ≤ n)
    (hlevel : ∀ n ∈ times, threshold n ≤ checkpointLevel (checkpointIndex n)) :
    ∀ n ∈ times,
      μ.real {ω | statistic ω n < threshold n} ≤
        μ.real {ω |
          statistic ω (checkpoint (checkpointIndex n)) <
            checkpointLevel (checkpointIndex n)} := by
  intro n hn
  exact measureReal_badEvent_interpolation_le μ statistic threshold checkpointLevel
    checkpoint (checkpointIndex n) n hmono (hcheckpoint n hn) (hlevel n hn)

/-! ## Independent finite-block amplification -/

/-- Independence of success events gives the exact product formula for the
event that every selected block fails.  This uses independence itself, not a
union bound. -/
theorem measure_all_fail_eq_prod
    (μ : Measure Ω) (success : ι → Set Ω)
    (hIndep : ProbabilityTheory.iIndepSet success μ) (blocks : Finset ι) :
    μ (⋂ i ∈ blocks, (success i)ᶜ) =
      ∏ i ∈ blocks, μ (success i)ᶜ := by
  rw [ProbabilityTheory.iIndepSet_iff] at hIndep
  apply hIndep blocks
  intro i hi
  exact (MeasurableSpace.measurableSet_generateFrom (by simp)).compl

/-- Real-valued version of `measure_all_fail_eq_prod`. -/
theorem measureReal_all_fail_eq_prod
    (μ : Measure Ω) (success : ι → Set Ω)
    (hIndep : ProbabilityTheory.iIndepSet success μ) (blocks : Finset ι) :
    μ.real (⋂ i ∈ blocks, (success i)ᶜ) =
      ∏ i ∈ blocks, μ.real (success i)ᶜ := by
  rw [measureReal_def, measure_all_fail_eq_prod μ success hIndep blocks,
    ENNReal.toReal_prod]
  simp only [← measureReal_def]

/-- If every selected independent block fails with probability at most `q`,
then all selected blocks fail with probability at most `q ^ #blocks`. -/
theorem measureReal_all_fail_le_pow
    (μ : Measure Ω) (success : ι → Set Ω)
    (hIndep : ProbabilityTheory.iIndepSet success μ) (blocks : Finset ι)
    {q : ℝ}
    (hfail : ∀ i ∈ blocks, μ.real (success i)ᶜ ≤ q) :
    μ.real (⋂ i ∈ blocks, (success i)ᶜ) ≤ q ^ blocks.card := by
  rw [measureReal_all_fail_eq_prod μ success hIndep blocks]
  calc
    (∏ i ∈ blocks, μ.real (success i)ᶜ) ≤ ∏ _i ∈ blocks, q := by
      gcongr with i hi
      exact hfail i hi
    _ = q ^ blocks.card := by simp

/-- The common `Fin N` specialization of independent-block amplification. -/
theorem measureReal_all_fin_fail_le_pow
    (μ : Measure Ω) {N : ℕ} (success : Fin N → Set Ω)
    (hIndep : ProbabilityTheory.iIndepSet success μ)
    {q : ℝ}
    (hfail : ∀ i, μ.real (success i)ᶜ ≤ q) :
    μ.real (⋂ i, (success i)ᶜ) ≤ q ^ N := by
  simpa using measureReal_all_fail_le_pow μ success hIndep Finset.univ
    (fun i _ ↦ hfail i)

omit [MeasurableSpace Ω] in
/-- If success in any selected block implies a global success, then global
failure forces failure in every selected block. -/
theorem globalFailure_subset_allBlockFailures
    (success : ι → Set Ω) (globalSuccess : Set Ω) (blocks : Finset ι)
    (hcover : ∀ i ∈ blocks, success i ⊆ globalSuccess) :
    globalSuccessᶜ ⊆ ⋂ i ∈ blocks, (success i)ᶜ := by
  intro ω hglobal
  simp only [mem_iInter]
  intro i hi hsuccess
  exact hglobal (hcover i hi hsuccess)

/-- Independent-block amplification for a global event containing every
selected block-success event. -/
theorem measureReal_globalFailure_le_pow
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (success : ι → Set Ω) (globalSuccess : Set Ω)
    (hIndep : ProbabilityTheory.iIndepSet success μ) (blocks : Finset ι)
    (hcover : ∀ i ∈ blocks, success i ⊆ globalSuccess)
    {q : ℝ}
    (hfail : ∀ i ∈ blocks, μ.real (success i)ᶜ ≤ q) :
    μ.real globalSuccessᶜ ≤ q ^ blocks.card := by
  exact (measureReal_mono
    (globalFailure_subset_allBlockFailures success globalSuccess blocks hcover)).trans
      (measureReal_all_fail_le_pow μ success hIndep blocks hfail)

/-! ## Exponential and double-exponential forms -/

/-- Raising an exponential failure probability to `N` independent trials
multiplies its exponent by `N`. -/
theorem exp_neg_pow_eq (a : ℝ) (N : ℕ) :
    (Real.exp (-a)) ^ N = Real.exp (-((N : ℝ) * a)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- If `N * a` dominates `exp u`, then `N` failures each bounded by
`exp (-a)` have a double-exponential product bound. -/
theorem exp_neg_pow_le_doubleExp {a u : ℝ} {N : ℕ}
    (hblocks : Real.exp u ≤ (N : ℝ) * a) :
    (Real.exp (-a)) ^ N ≤ Real.exp (-Real.exp u) := by
  rw [exp_neg_pow_eq]
  exact Real.exp_le_exp.mpr (neg_le_neg hblocks)

/-- Independent blocks with a uniform exponential failure estimate satisfy a
double-exponential all-failure estimate as soon as there are enough blocks. -/
theorem measureReal_all_fail_le_doubleExp
    (μ : Measure Ω) (success : ι → Set Ω)
    (hIndep : ProbabilityTheory.iIndepSet success μ) (blocks : Finset ι)
    {a u : ℝ}
    (hfail : ∀ i ∈ blocks, μ.real (success i)ᶜ ≤ Real.exp (-a))
    (hblocks : Real.exp u ≤ (blocks.card : ℝ) * a) :
    μ.real (⋂ i ∈ blocks, (success i)ᶜ) ≤ Real.exp (-Real.exp u) := by
  exact (measureReal_all_fail_le_pow μ success hIndep blocks
    hfail).trans (exp_neg_pow_le_doubleExp hblocks)

/-- Double-exponential global-failure bound obtained from independent block
successes whose union is contained in the global success event. -/
theorem measureReal_globalFailure_le_doubleExp
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (success : ι → Set Ω) (globalSuccess : Set Ω)
    (hIndep : ProbabilityTheory.iIndepSet success μ) (blocks : Finset ι)
    (hcover : ∀ i ∈ blocks, success i ⊆ globalSuccess)
    {a u : ℝ}
    (hfail : ∀ i ∈ blocks, μ.real (success i)ᶜ ≤ Real.exp (-a))
    (hblocks : Real.exp u ≤ (blocks.card : ℝ) * a) :
    μ.real globalSuccessᶜ ≤ Real.exp (-Real.exp u) := by
  exact (measureReal_globalFailure_le_pow μ success globalSuccess hIndep blocks hcover
    hfail).trans (exp_neg_pow_le_doubleExp hblocks)

/-- Complete amplification interface used after a one-block stopped
construction.  Each stopped block fails with probability at most
`stoppedError`; the probability that its exit time exceeds the deterministic
block length has the explicit exponential bound `exp (-exitRate)`; and the
stopped success transfers to success in the deterministic block.  If the sum
of those errors is at most `exp (-blockRate)`, independence and the final
cardinality inequality produce the desired double-exponential estimate. -/
theorem measureReal_exitTail_amplification_le_doubleExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (blocks : Finset ι)
    (exitSuccess timedSuccess : ι → Set Ω)
    (exitTime : ι → Ω → ℕ) (blockLength : ι → ℕ)
    {stoppedError exitRate blockRate u : ℝ}
    (htransfer : ∀ i ∈ blocks,
      exitSuccess i ∩ {ω | exitTime i ω ≤ blockLength i} ⊆ timedSuccess i)
    (hstopped : ∀ i ∈ blocks, μ.real (exitSuccess i)ᶜ ≤ stoppedError)
    (hexit : ∀ i ∈ blocks,
      μ.real {ω | blockLength i < exitTime i ω} ≤ Real.exp (-exitRate))
    (honeBlock : stoppedError + Real.exp (-exitRate) ≤ Real.exp (-blockRate))
    (hIndep : ProbabilityTheory.iIndepSet timedSuccess μ)
    (hblocks : Real.exp u ≤ (blocks.card : ℝ) * blockRate) :
    μ.real (⋂ i ∈ blocks, (timedSuccess i)ᶜ) ≤ Real.exp (-Real.exp u) := by
  apply measureReal_all_fail_le_doubleExp μ timedSuccess hIndep blocks
  · intro i hi
    exact (measureReal_deterministicFailure_le μ (exitSuccess i) (timedSuccess i)
      (exitTime i) (blockLength i) (htransfer i hi) (hstopped i hi) (hexit i hi)).trans
        honeBlock
  · exact hblocks

/-- Variant whose one-block input is a lower bound `successProbability` on
the stopped success probability.  This is the form directly fed by a
Paley--Zygmund estimate in the thick-point argument. -/
theorem measureReal_oneBlockSuccess_exitTail_amplification_le_doubleExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (blocks : Finset ι)
    (exitSuccess timedSuccess : ι → Set Ω)
    (exitTime : ι → Ω → ℕ) (blockLength : ι → ℕ)
    {successProbability exitRate blockRate u : ℝ}
    (hmeas : ∀ i ∈ blocks, MeasurableSet (exitSuccess i))
    (htransfer : ∀ i ∈ blocks,
      exitSuccess i ∩ {ω | exitTime i ω ≤ blockLength i} ⊆ timedSuccess i)
    (hsuccess : ∀ i ∈ blocks, successProbability ≤ μ.real (exitSuccess i))
    (hexit : ∀ i ∈ blocks,
      μ.real {ω | blockLength i < exitTime i ω} ≤ Real.exp (-exitRate))
    (honeBlock : 1 - successProbability + Real.exp (-exitRate) ≤
      Real.exp (-blockRate))
    (hIndep : ProbabilityTheory.iIndepSet timedSuccess μ)
    (hblocks : Real.exp u ≤ (blocks.card : ℝ) * blockRate) :
    μ.real (⋂ i ∈ blocks, (timedSuccess i)ᶜ) ≤ Real.exp (-Real.exp u) := by
  apply measureReal_exitTail_amplification_le_doubleExp μ blocks exitSuccess timedSuccess
    exitTime blockLength htransfer
  · intro i hi
    exact measureReal_compl_le_one_sub_of_le μ (exitSuccess i) (hmeas i hi) (hsuccess i hi)
  · exact hexit
  · exact honeBlock
  · exact hIndep
  · exact hblocks

/-- Global-event form of
`measureReal_oneBlockSuccess_exitTail_amplification_le_doubleExp`.  It is the
direct abstract shape of the last amplification step in Proposition 1.3: a
thick point produced in any deterministic block is also a thick point of the
whole walk segment. -/
theorem measureReal_oneBlockSuccess_exitTail_globalFailure_le_doubleExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (blocks : Finset ι)
    (exitSuccess timedSuccess : ι → Set Ω) (globalSuccess : Set Ω)
    (exitTime : ι → Ω → ℕ) (blockLength : ι → ℕ)
    {successProbability exitRate blockRate u : ℝ}
    (hmeas : ∀ i ∈ blocks, MeasurableSet (exitSuccess i))
    (htransfer : ∀ i ∈ blocks,
      exitSuccess i ∩ {ω | exitTime i ω ≤ blockLength i} ⊆ timedSuccess i)
    (hsuccess : ∀ i ∈ blocks, successProbability ≤ μ.real (exitSuccess i))
    (hexit : ∀ i ∈ blocks,
      μ.real {ω | blockLength i < exitTime i ω} ≤ Real.exp (-exitRate))
    (honeBlock : 1 - successProbability + Real.exp (-exitRate) ≤
      Real.exp (-blockRate))
    (hIndep : ProbabilityTheory.iIndepSet timedSuccess μ)
    (hcover : ∀ i ∈ blocks, timedSuccess i ⊆ globalSuccess)
    (hblocks : Real.exp u ≤ (blocks.card : ℝ) * blockRate) :
    μ.real globalSuccessᶜ ≤ Real.exp (-Real.exp u) := by
  calc
    μ.real globalSuccessᶜ ≤
        μ.real (⋂ i ∈ blocks, (timedSuccess i)ᶜ) :=
      measureReal_mono
        (globalFailure_subset_allBlockFailures timedSuccess globalSuccess blocks hcover)
    _ ≤ Real.exp (-Real.exp u) :=
      measureReal_oneBlockSuccess_exitTail_amplification_le_doubleExp
        μ blocks exitSuccess timedSuccess exitTime blockLength hmeas htransfer
          hsuccess hexit honeBlock hIndep hblocks

end Erdos1165.BlockAmplification
