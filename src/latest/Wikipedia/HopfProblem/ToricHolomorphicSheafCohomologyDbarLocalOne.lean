import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneBidisc

/-!
# The actual local smooth Dolbeault lemma in complex dimension two

Every smooth closed `(0,1)` form on an arbitrary open subset of `ℂ × ℂ`
has an actual smooth primitive near each point. The proof first extends
the two coefficient germs separately by compact smooth cutoffs, retains
closedness only near the chosen point, and applies the local two-integral
Cauchy–Green construction. No globally closed extension is assumed.
-/

noncomputable section

open Complex Set Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne

open PeriodTorusLineBundleClassification

/-- The local smooth `∂̄` Poincaré lemma for actual closed `(0,1)` forms on
arbitrary open subsets of the two-dimensional complex vector space. -/
theorem exists_smooth_primitive_germ {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {f g : ℂ × ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hclosed : ∀ q ∈ U, dbarFirst g q = dbarSecond f q)
    {x : ℂ × ℂ} (hx : x ∈ U) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧
      dbarFirst u =ᶠ[𝓝 x] f ∧ dbarSecond u =ᶠ[𝓝 x] g := by
  obtain ⟨v, hv, _, hev⟩ := exists_compact_smooth_representative hU hf hx
  obtain ⟨w, hw, _, hew⟩ := exists_compact_smooth_representative hU hg hx
  have hclosed' : ∀ᶠ q in 𝓝 x, dbarFirst w q = dbarSecond v q := by
    filter_upwards [hU.mem_nhds hx, dbarFirst_eventuallyEq hew,
      dbarSecond_eventuallyEq hev] with q hq hqw hqv
    rw [hqw, hqv]
    exact hclosed q hq
  obtain ⟨u, hu, huf, hug⟩ := exists_smooth_primitive_of_eventually_closed hv hw hclosed'
  exact ⟨u, hu, huf.trans hev, hug.trans hew⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne
