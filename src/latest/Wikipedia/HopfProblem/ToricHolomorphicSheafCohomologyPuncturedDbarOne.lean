import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneSequence
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneSmooth

/-!
# Actual global smooth closed-form primitives on `ℂ × ℂ*`

The hypotheses are only smoothness of the two actual coefficients on
the punctured product and their actual closedness equation there. Local
Cauchy–Green primitives, proved finite Laurent approximations, and
convergent analytic tails construct the global primitive. No Stein,
Cousin, or globally closed extension hypothesis is used.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

open PeriodTorusLineBundleClassification

/-- Every actual smooth closed `(0,1)` form on `ℂ × ℂ*` has an actual
smooth primitive throughout that domain. -/
theorem exists_smooth_global_dbar_primitive {f g : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (hg : ContDiffOn ℝ ∞ g domain)
    (hclosed : ∀ q ∈ domain, dbarFirst g q = dbarSecond f q) :
    ∃ u : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ u domain ∧
      ∀ q ∈ domain, dbarFirst u q = f q ∧ dbarSecond u q = g q := by
  obtain ⟨u, hu, hstage, hb⟩ := exists_compatible_primitiveSequence hf hg hclosed
  exact exists_smoothOn_primitive_of_exhaustion isOpen_exhaustionDomain monotone_exhaustionDomain
    exhaustionDomain_subset_domain cover_exhaustionDomain hu hstage hb

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
