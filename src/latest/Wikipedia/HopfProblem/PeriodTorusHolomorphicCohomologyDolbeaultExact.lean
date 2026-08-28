import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultKernel
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultLocal
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultSheafExact
import Wikipedia.HopfProblem.HolomorphicExponentialSheafExactLocal
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData

/-!
# The genuine Dolbeault sheaf resolution on a period torus

The terms of `0 → O → A⁰ → A⁰¹ → A⁰² → 0` are actual holomorphic
functions, actual smooth functions, and pairs of actual smooth coefficients
on the original period-lattice quotient. The maps are the literal inclusion
and the two native coordinate differentials. The analytic kernel theorem
and the proved local primitives give exactness in the genuine sheaf category.
No exactness or local-solvability property is assumed.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

variable (p : PeriodDomain)

/-- The genuine smooth Dolbeault terms with their actual native differentials. -/
abbrev dolbeaultComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of p.Torus)) :=
  ShortComplex.mk (differential p) (topDifferential p) (differential_topDifferential p)

/-- The original holomorphic inclusion followed by the native first differential. -/
abbrev initialComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of p.Torus)) :=
  ShortComplex.mk (inclusion p) (differential p) (inclusion_differential p)

/-- The proved analytic kernel identifies the initial kernel on every torus open. -/
theorem initialComplex_exact : (initialComplex p).Exact := by
  apply HolomorphicSheafCohomology.DolbeaultLocal.exact_of_section_kernels
    (initialComplex p)
  intro U s hs
  exact exists_holomorphic_preimage p U s hs

/-- Actual local closed-form primitives prove middle exactness on the native torus. -/
theorem dolbeaultComplex_exact : (dolbeaultComplex p).Exact := by
  apply HolomorphicExponentialSheaf.exact_of_local_section_kernels (dolbeaultComplex p)
  intro U x hx s hs
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_local_primitive p U x hx s hs
  exact ⟨V, hVU, hxV, t, ht⟩

/-- Genuine local top-form primitives make the native top derivative epic. -/
instance topDifferential_epi : Epi (topDifferential p) := by
  apply HolomorphicSheafCohomology.DolbeaultLocal.epi_of_local_section_lifts
    (topDifferential p)
  intro U x hx s
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_local_top_primitive p U x hx s
  exact ⟨V, hVU, hxV, t, ht⟩

/-- The actual augmented Dolbeault resolution of the original holomorphic sheaf.
Its kernel, local exactness, and endpoint properties are all proved. -/
def resolution : CuspNormalization.SheafCohomologyResolution.AugmentedResolution
    (TopCat.Sheaf AddCommGrpCat (TopCat.of p.Torus)) where
  F := holomorphicSheaf p
  complex := dolbeaultComplex p
  ι := inclusion p
  zero := inclusion_differential p
  initial_exact := initialComplex_exact p
  exact := dolbeaultComplex_exact p
  mono_ι := inclusion_mono p
  epi_g := topDifferential_epi p

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
