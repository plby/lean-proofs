import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreSections
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertEtaSections

/-!
# The actual distinguished holomorphic line bundles and their section spaces

The bundle here is the already constructed analytic `VectorBundleCore`,
identified with the independently topologized lattice orbit quotient.
Its model fibre really is one-dimensional over `ℂ`. For every nonzero
integer multiple of `η`, every Mathlib holomorphic section of this actual
bundle is zero; its holomorphic-section module therefore has dimension zero.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

/-- The actual holomorphic line-bundle core of the canonical factor for `nη`. -/
abbrev etaLineBundle (p : PeriodDomain) (n : ℤ) : VectorBundleCore ℂ p.Torus ℂ p.Torus :=
  (Core.data (etaFactor p n)).core

theorem etaLineBundle_fibre_finrank (p : PeriodDomain) (n : ℤ) (b : p.Torus) :
    Module.finrank ℂ ((etaLineBundle p n).Fiber b) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

theorem etaLineBundle_isHolomorphic (p : PeriodDomain) (n : ℤ) :
    ContMDiffVectorBundle ω ℂ (etaLineBundle p n).Fiber
      (modelWithCornersSelf ℂ ComplexPlane₂) :=
  Core.core_contMDiffVectorBundle (etaFactor p n)

/-- Vanishing is asserted for the standard, genuine holomorphic-section type of the bundle. -/
theorem etaBundleSection_eq_zero (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0)
    (s : Core.HolomorphicSection (etaFactor p n)) : s = 0 := by
  apply Core.quotientSection_injective (etaFactor p n)
  rw [Core.quotientSection_zero]
  exact etaSection_eq_zero p n hn (Core.quotientSection (etaFactor p n) s)
    (Core.quotientSection_holomorphic (etaFactor p n) s)

theorem etaBundleSections_subsingleton (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    Subsingleton (Core.HolomorphicSection (etaFactor p n)) := by
  constructor
  intro s t
  exact (etaBundleSection_eq_zero p n hn s).trans (etaBundleSection_eq_zero p n hn t).symm

/-- The actual vector space of holomorphic sections has dimension zero. -/
theorem etaBundleSections_finrank_zero (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    Module.finrank ℂ (Core.HolomorphicSection (etaFactor p n)) = 0 := by
  letI := etaBundleSections_subsingleton p n hn
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
