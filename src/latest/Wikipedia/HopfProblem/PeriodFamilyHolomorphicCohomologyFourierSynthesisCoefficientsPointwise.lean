import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsBasic

/-!
# Pointwise absolute summability of the actual coefficients

Applying the compact-uniform bounds to a singleton gives absolute
summability of every weighted original derivative word, and hence of
the coefficient values themselves at each point of the original base.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification FourierParameter

namespace SmoothRapidCoefficients

variable {U : Opens ℂ} {c : Coefficients}

/-- Every actual weighted derivative word is absolutely summable at each base point. -/
theorem summable_weighted_word (hc : SmoothRapidCoefficients U c)
    (s : List ℂ) (b : U) (r : ℕ) :
    Summable (fun k => (1 + ‖integerFrequency k‖) ^ r *
      ‖iteratedDirectionalDerivativeList s (c k) (b : ℂ)‖) := by
  obtain ⟨u, _, hsum, hbound⟩ := hc.majorant s {b} isCompact_singleton r
  exact hsum.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun k => hbound b (Set.mem_singleton b) k)

/-- The original coefficient values are absolutely summable at each actual base point. -/
theorem summable_norm (hc : SmoothRapidCoefficients U c) (b : U) :
    Summable (fun k => ‖c k (b : ℂ)‖) := by
  simpa only [pow_zero, one_mul, iteratedDirectionalDerivativeList] using
    hc.summable_weighted_word [] b 0

/-- The original complex coefficient values have an actual sum at each base point. -/
theorem summable (hc : SmoothRapidCoefficients U c) (b : U) :
    Summable (fun k => c k (b : ℂ)) :=
  (hc.summable_norm b).of_norm

end SmoothRapidCoefficients

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
