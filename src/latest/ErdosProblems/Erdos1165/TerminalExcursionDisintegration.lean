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

import ErdosProblems.Erdos1165.TerminalExcursionPathwise
import ErdosProblems.Erdos1165.Proposition13Measurability
import ErdosProblems.Erdos1165.PlanarPotential

/-!
# Sequential disintegration of terminal excursion visits

The terminal visit vector in `TerminalExcursionPathwise` is stopped at the
*next hit of the outer boundary*.  It is not stopped on exiting the closed
disc.  Moreover, after conditioning on an exact outer-exit horizon and the
whole successful excursion profile, the visit counts need not have an exact
product law on a coarse entrance-vector fibre.

Accordingly this file uses the valid one-sided interface needed in Appendix
A.7.  A probability measure `dataLaw` carries the complete stopped past and
boundary data.  Given these data, `actualKernel` is the sequential
conditional success probability.  The strong Markov input has two parts:

* a pointwise lower comparison of a model kernel with `actualKernel`; and
* a one-sided disintegration inequality from the conditional mean to the
  desired stopped thick event.

No equality of conditional laws is postulated.  The aggregation theorem
below proves that a uniform model-kernel comparison survives this sequential
conditioning.  The final section records the literal boundary-stopping
convention used by the actual terminal segments.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.TerminalExcursionDisintegration

noncomputable section

/-! ## Full stopped-data sequential kernel interface -/

/-- Pointwise sequential strong-Markov comparison after conditioning on the
complete stopped past and boundary data.  `entranceData d` is only the part
of the full datum used by the model kernel; `actualKernel d` may depend on all
of `d`.

This deliberately asks only for a lower bound.  In particular it does not
assert that visit vectors have an exact product law after conditioning on a
coarser event such as an exact terminal horizon or excursion profile. -/
def SequentialConditionalKernelLower
    {Data Entrance : Type*} {m : ℕ}
    (entranceData : Data → Fin m → Entrance)
    (modelKernel : (Fin m → Entrance) → ℝ)
    (actualKernel : Data → ℝ) : Prop :=
  ∀ d, modelKernel (entranceData d) ≤ actualKernel d

/-- One-sided stopped-event disintegration.  `dataLaw` is the normalized law
of the complete stopped data conditional on `successful`; hence its integral
is the conditional success probability.  Only the lower inequality needed
for the thick event is exposed. -/
def StoppedDataDisintegrationLower
    {Omega Data : Type*} [MeasurableSpace Omega] [MeasurableSpace Data]
    (mu : Measure Omega) (successful thick : Set Omega)
    (dataLaw : Measure Data) (actualKernel : Data → ℝ) : Prop :=
  mu.real successful * ∫ d, actualKernel d ∂dataLaw ≤ mu.real thick

/-- A uniform model-kernel lower comparison passes through sequential
conditioning on the complete stopped data. -/
theorem event_lower_of_sequentialKernelComparison
    {Omega Data Entrance : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Data] [Fintype Entrance]
    {m : ℕ} (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful thick : Set Omega)
    (dataLaw : Measure Data) [IsProbabilityMeasure dataLaw]
    (entranceData : Data → Fin m → Entrance)
    (modelKernel : (Fin m → Entrance) → ℝ)
    (actualKernel : Data → ℝ) (hactual : Integrable actualKernel dataLaw)
    (epsilon reference : ℝ)
    (hcompare : AppendixLocalTimeTransfer.TerminalKernelComparison
      epsilon reference modelKernel)
    (hsequential : SequentialConditionalKernelLower
      entranceData modelKernel actualKernel)
    (hdisintegrate : StoppedDataDisintegrationLower
      mu successful thick dataLaw actualKernel) :
    ((1 - epsilon) * reference) * mu.real successful ≤ mu.real thick := by
  have hpoint (d : Data) :
      (1 - epsilon) * reference ≤ actualKernel d :=
    (hcompare (entranceData d)).1.trans (hsequential d)
  have hintegral : (1 - epsilon) * reference ≤
      ∫ d, actualKernel d ∂dataLaw := by
    have hconst : Integrable (fun _ : Data ↦ (1 - epsilon) * reference) dataLaw :=
      integrable_const _
    have hle := integral_mono hconst hactual hpoint
    simpa [MeasureTheory.integral_const, MeasureTheory.probReal_univ] using hle
  calc
    ((1 - epsilon) * reference) * mu.real successful =
        mu.real successful * ((1 - epsilon) * reference) := by ring
    _ ≤ mu.real successful * ∫ d, actualKernel d ∂dataLaw :=
      mul_le_mul_of_nonneg_left hintegral measureReal_nonneg
    _ ≤ mu.real thick := hdisintegrate

/-- The exact Appendix-A.7 numerical reduction with full stopped-data
conditioning.  The iid Bernoulli--geometric concentration supplies the
reference bound, while the two sequential hypotheses are precisely the
remaining strong-Markov/disintegration obligations. -/
theorem event_terminal_lower_of_sequentialKernelComparison
    {Omega Data Entrance : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Data] [Fintype Entrance]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful thick : Set Omega)
    {scale : ℕ} (profileDelta thickDelta : ℝ)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin
      scale profileDelta thickDelta q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance
        scale profileDelta q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin
        scale profileDelta thickDelta q p) ^ 2 ≤ (scale : ℝ)⁻¹)
    (dataLaw : Measure Data) [IsProbabilityMeasure dataLaw]
    (entranceData : Data →
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → Entrance)
    (modelKernel :
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → Entrance) → ℝ)
    (actualKernel : Data → ℝ) (hactual : Integrable actualKernel dataLaw)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilonInv : epsilon ≤ (scale : ℝ)⁻¹)
    (hcompare : AppendixLocalTimeTransfer.TerminalKernelComparison epsilon
      (AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta) modelKernel)
    (hsequential : SequentialConditionalKernelLower
      entranceData modelKernel actualKernel)
    (hdisintegrate : StoppedDataDisintegrationLower
      mu successful thick dataLaw actualKernel) :
    (1 - 2 * (scale : ℝ)⁻¹) * mu.real successful ≤ mu.real thick := by
  let reference := AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
    scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta
  have href : 1 - (scale : ℝ)⁻¹ ≤ reference :=
    AppendixLocalTime.required_hlozThreshold_probability_ge_one_sub_inv
      scale profileDelta thickDelta q p hq0 hq1 hp0 hp1 hmargin hratio
  have hinv0 : 0 ≤ (scale : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg scale)
  have hepsilon1 : epsilon ≤ 1 := by
    by_cases hs : scale = 0
    · subst scale
      norm_num at hepsilonInv
      linarith
    · exact hepsilonInv.trans
        (inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hs)))
  have hfactorReference :
      (1 - epsilon) * (1 - (scale : ℝ)⁻¹) ≤
        (1 - epsilon) * reference :=
    mul_le_mul_of_nonneg_left href (sub_nonneg.mpr hepsilon1)
  have hcross : 0 ≤ epsilon * (scale : ℝ)⁻¹ :=
    mul_nonneg hepsilon0 hinv0
  have hfactor : 1 - 2 * (scale : ℝ)⁻¹ ≤
      (1 - epsilon) * reference := by
    calc
      1 - 2 * (scale : ℝ)⁻¹ ≤
          1 - (scale : ℝ)⁻¹ - epsilon := by linarith
      _ ≤ (1 - epsilon) * (1 - (scale : ℝ)⁻¹) := by nlinarith
      _ ≤ (1 - epsilon) * reference := hfactorReference
  have hkernel := event_lower_of_sequentialKernelComparison
    mu successful thick dataLaw entranceData modelKernel actualKernel hactual
    epsilon reference hcompare hsequential hdisintegrate
  exact (mul_le_mul_of_nonneg_right hfactor measureReal_nonneg).trans hkernel

/-! ## The literal boundary convention -/

open ThickPoint

/-- A target is hit before the *next visit* to `boundary`.  This is the
stopping convention of `TerminalExcursionPathwise.innerVisitTimes`: the
endpoint at the boundary is excluded from the visit segment. -/
def walkHitBeforeBoundary (boundary : Set Point) (target : Point) : Set WalkPath :=
  ⋃ n, {s | s n = target ∧ ∀ k < n, s k ∉ boundary}

lemma measurableSet_walkHitBeforeBoundary (boundary : Set Point) (target : Point) :
    MeasurableSet (walkHitBeforeBoundary boundary target) := by
  unfold walkHitBeforeBoundary
  measurability

/-- Literal one-walk hit probability for the boundary-stopped terminal
segment.  Unlike `RadialHarnackSpecialization.closedDiscHitKernel`, this
stops on hitting a designated vertex boundary, not on exiting a closed disc.
-/
def boundaryStoppedHitKernel (boundary : Set Point) (target start : Point) : ℝ :=
  (PlanarPotential.simpleRandomWalkFrom start
    (walkHitBeforeBoundary boundary target)).toReal

end

end Erdos1165.TerminalExcursionDisintegration
