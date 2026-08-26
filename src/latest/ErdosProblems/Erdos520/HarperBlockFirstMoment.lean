import ErdosProblems.Erdos520.HarperBlockLaw
import Mathlib.Probability.Distributions.Gaussian.Fernique

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory

namespace Erdos
namespace Problem520

/-!
# First moments of the one-block comparison laws

These facts supply the absolute-integrability hypotheses used by the exact
Fejér CDF inversion argument.
-/

/-- The centered linear block has a finite first moment.  Its source cube is
finite, so this does not require a quantitative moment estimate. -/
theorem integrable_id_harperCenteredLinearBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    Integrable id (harperCenteredLinearBlockLaw y S t u) := by
  unfold harperCenteredLinearBlockLaw
  rw [integrable_map_measure (by fun_prop)
    (measurable_of_finite _).aemeasurable]
  exact Integrable.of_finite

/-- Absolute first moment of the centered linear block. -/
theorem integrable_abs_harperCenteredLinearBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    Integrable (fun x : ℝ ↦ |x|)
      (harperCenteredLinearBlockLaw y S t u) := by
  simpa only [Real.norm_eq_abs, id_eq] using!
    (integrable_id_harperCenteredLinearBlockLaw y S t u).norm

/-- The variance-matched Gaussian has a finite first moment, including in
the degenerate zero-variance case. -/
theorem integrable_id_harperGaussianBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    Integrable id (harperGaussianBlockLaw y S t u) := by
  unfold harperGaussianBlockLaw
  exact IsGaussian.integrable_id

/-- Absolute first moment of the variance-matched Gaussian. -/
theorem integrable_abs_harperGaussianBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    Integrable (fun x : ℝ ↦ |x|)
      (harperGaussianBlockLaw y S t u) := by
  simpa only [Real.norm_eq_abs, id_eq] using!
    (integrable_id_harperGaussianBlockLaw y S t u).norm

/-- Product first-moment helper used in Fubini arguments. -/
theorem Integrable.abs_fst_add_abs_snd_prod
    {mu nu : Measure ℝ} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : Integrable (fun x : ℝ ↦ |x|) mu)
    (hnu : Integrable (fun x : ℝ ↦ |x|) nu) :
    Integrable (fun p : ℝ × ℝ ↦ |p.1| + |p.2|) (mu.prod nu) := by
  exact (hmu.comp_fst nu).add (hnu.comp_snd mu)

/-- In particular, the absolute difference of two variables with finite
first moments is integrable under their product law. -/
theorem Integrable.abs_fst_sub_snd_prod
    {mu nu : Measure ℝ} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : Integrable id mu) (hnu : Integrable id nu) :
    Integrable (fun p : ℝ × ℝ ↦ |p.1 - p.2|) (mu.prod nu) := by
  have hdiff : Integrable (fun p : ℝ × ℝ ↦ p.1 - p.2) (mu.prod nu) :=
    (hmu.comp_fst nu).sub (hnu.comp_snd mu)
  simpa only [Real.norm_eq_abs] using! hdiff.norm

end Problem520
end Erdos
