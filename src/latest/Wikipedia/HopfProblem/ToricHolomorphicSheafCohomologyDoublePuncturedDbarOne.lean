import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneSequence
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneSmooth
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOnePartialLaurent

/-!
# Actual global closed-form primitives on `(ℂ*)²`

The hypotheses are only smoothness of the actual coefficients on the
doubly punctured product and their actual closedness equation there.
Two-axis cutoffs, local Cauchy–Green integrals, finite Laurent
approximations and convergent analytic tails construct the primitive.
No Stein, Cousin, or globally closed extension hypothesis occurs.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open PeriodTorusLineBundleClassification

/-- Every actual smooth closed `(0,1)` form on `(ℂ*)²` has an actual
smooth primitive throughout that domain. -/
theorem exists_smooth_global_dbar_primitive {f g : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (hg : ContDiffOn ℝ ∞ g domain)
    (hclosed : ∀ q ∈ domain, dbarFirst g q = dbarSecond f q) :
    ∃ u : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ u domain ∧
      ∀ q ∈ domain, dbarFirst u q = f q ∧ dbarSecond u q = g q := by
  obtain ⟨u, hu, hstage, hb⟩ := exists_compatible_primitiveSequence hf hg hclosed
  exact exists_smoothOn_primitive_of_exhaustion isOpen_domain
    isOpen_exhaustionDomain monotone_exhaustionDomain exhaustionDomain_subset_domain
    cover_exhaustionDomain hu hstage hb

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
