/-
Copyright 2026 The Lean-Proofs Authors.

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
import Wikipedia.VinogradovsTheorem.MinorArc
import Wikipedia.VinogradovsTheorem.PrimePowerTail

/-!
# Analytic conclusion for Erdős Problem 471

The major-arc main term is positive for odd targets, while the major-arc
approximation error and the minor-arc integral are both `o(n^2)`.  Combining
the two pieces with Fourier inversion gives the quadratic lower bound for the
ternary von Mangoldt coefficient.
-/

noncomputable section

namespace VinogradovsTheorem.Analytic

open Filter MeasureTheory

theorem torusMajorArcs_measurableSet (D P : ℕ) :
    MeasurableSet (torusMajorArcs D P) := by
  unfold torusMajorArcs
  exact Finset.measurableSet_biUnion _ fun aq _ =>
    torusLocalArc_measurableSet D aq

theorem torusMajorArcs_subset_Icc (D P : ℕ) :
    torusMajorArcs D P ⊆ Set.Icc (0 : ℝ) 1 := by
  intro α hα
  simp only [torusMajorArcs, Set.mem_iUnion] at hα
  rcases hα with ⟨aq, _haq, hα⟩
  exact torusLocalArc_subset_Icc D aq hα

theorem circle_integral_eq_major_add_minor (n D P : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1, integrand n α) =
      (∫ α in torusMajorArcs D P, integrand n α) +
        ∫ α in torusMinorArcs D P, integrand n α := by
  have hint : IntegrableOn (integrand n) (Set.Icc (0 : ℝ) 1) volume :=
    (integrand_continuous n).integrableOn_Icc
  have hdiff := setIntegral_sdiff (μ := volume)
    (torusMajorArcs_measurableSet D P) hint
    (torusMajorArcs_subset_Icc D P)
  change (∫ α in Set.Icc (0 : ℝ) 1, integrand n α) =
    (∫ α in torusMajorArcs D P, integrand n α) +
      ∫ α in Set.Icc (0 : ℝ) 1 \ torusMajorArcs D P, integrand n α
  rw [hdiff]
  ring

theorem vonMangoldtTripleWeight_eq_integral (n : ℕ) :
    (VinogradovsTheorem.PrimePowerTail.vonMangoldtTripleWeight n : ℂ) =
      ∫ α in Set.Icc (0 : ℝ) 1, integrand n α := by
  simpa [integrand, Vinogradov.negAddChar,
    Vinogradov.vonMangoldtExpSum, Vinogradov.addChar,
    VinogradovsTheorem.CircleMethod.vonMangoldtExpSum,
    VinogradovsTheorem.CircleMethod.addChar] using
    VinogradovsTheorem.PrimePowerTail.vonMangoldtTripleWeight_eq_circleIntegral n

/-- The completed circle method: on every sufficiently large odd target,
the ternary von Mangoldt coefficient has a fixed positive quadratic lower
bound. -/
theorem eventually_vonMangoldtTripleWeight_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      Odd n →
        c * (n : ℝ) ^ 2 ≤
          VinogradovsTheorem.PrimePowerTail.vonMangoldtTripleWeight n := by
  obtain ⟨c, hc, hmodel⟩ := eventually_denominator_model_re_lower
  have hmajor := eventually_norm_major_integral_sub_model_le_mul
    (show 0 < c / 4 by positivity)
  have hminor := eventually_norm_minor_integral_le_mul
    (show 0 < c / 4 by positivity)
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hmodel, hmajor, hminor] with n hnModel hnMajor hnMinor
  intro hodd
  let model : ℂ :=
    ∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n),
      singularTerm q n * localBetaIntegral (dirichletCutoff n) q n
  let major : ℂ :=
    ∫ α in torusMajorArcs (dirichletCutoff n)
      (majorDenominatorCutoff n), integrand n α
  let minor : ℂ :=
    ∫ α in torusMinorArcs (dirichletCutoff n)
      (majorDenominatorCutoff n), integrand n α
  have hModel : c * (n : ℝ) ^ 2 ≤ model.re := by
    simpa [model] using hnModel hodd
  have hMajor : ‖major - model‖ ≤ (c / 4) * (n : ℝ) ^ 2 := by
    simpa [major, model] using hnMajor
  have hMinor : ‖minor‖ ≤ (c / 4) * (n : ℝ) ^ 2 := by
    simpa [minor] using hnMinor
  have hreMajor : |major.re - model.re| ≤ (c / 4) * (n : ℝ) ^ 2 := by
    have hre := Complex.abs_re_le_norm (major - model)
    have hre' : |major.re - model.re| ≤ ‖major - model‖ := by
      simpa using hre
    exact hre'.trans hMajor
  have hreMinor : |minor.re| ≤ (c / 4) * (n : ℝ) ^ 2 :=
    (Complex.abs_re_le_norm minor).trans hMinor
  have hmajorLower : model.re - (c / 4) * (n : ℝ) ^ 2 ≤ major.re := by
    have := (abs_le.mp hreMajor).1
    linarith
  have hminorLower : -(c / 4) * (n : ℝ) ^ 2 ≤ minor.re := by
    have := (abs_le.mp hreMinor).1
    linarith
  have hsplit := circle_integral_eq_major_add_minor n
    (dirichletCutoff n) (majorDenominatorCutoff n)
  have hfourier := vonMangoldtTripleWeight_eq_integral n
  have hweight : VinogradovsTheorem.PrimePowerTail.vonMangoldtTripleWeight n =
      major.re + minor.re := by
    have hre := congrArg Complex.re (hfourier.trans hsplit)
    simpa [major, minor] using hre
  rw [hweight]
  nlinarith [sq_nonneg (n : ℝ)]

end VinogradovsTheorem.Analytic
