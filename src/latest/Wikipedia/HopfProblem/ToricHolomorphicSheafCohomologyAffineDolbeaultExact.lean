import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultKernel
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultLocal
import Wikipedia.HopfProblem.HolomorphicExponentialSheafExactLocal
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData

/-!
# The genuine affine Dolbeault sheaf resolution

The exact sequence is `0 → O → A⁰ → A⁰¹ → A⁰² → 0` on the actual
space `ℂ × ℂ`. Its terms are actual holomorphic functions, actual smooth
functions, and actual smooth coefficient pairs. Its maps are the literal
inclusion and the two actual coordinate differentials. Exactness follows
from the proved analytic kernel and the actual local primitives on stalks.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

/-- The three genuine smooth terms and their actual differential maps. -/
abbrev dolbeaultComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ℂ × ℂ))) :=
  ShortComplex.mk differential topDifferential differential_topDifferential

/-- The actual holomorphic inclusion followed by the first differential. -/
abbrev initialComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ℂ × ℂ))) :=
  ShortComplex.mk inclusion differential inclusion_differential

/-- Joint Cauchy--Riemann analyticity identifies the genuine first kernel. -/
theorem initialComplex_exact : initialComplex.Exact := by
  apply DolbeaultLocal.exact_of_section_kernels initialComplex
  intro U s hs
  exact exists_holomorphic_preimage U s hs

/-- Genuine local closed-form primitives give exactness in the middle. -/
theorem dolbeaultComplex_exact : dolbeaultComplex.Exact := by
  apply HolomorphicExponentialSheaf.exact_of_local_section_kernels dolbeaultComplex
  intro U x hx s hs
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_local_primitive U x hx s hs
  exact ⟨V, hVU, hxV, t, ht⟩

/-- Actual local Cauchy--Green primitives make the top derivative epic. -/
instance topDifferential_epi : Epi topDifferential := by
  apply DolbeaultLocal.epi_of_local_section_lifts topDifferential
  intro U x hx s
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_local_top_primitive U x hx s
  exact ⟨V, hVU, hxV, t, ht⟩

/-- The actual exact sequence `0 → O → smooth → smooth² → smooth → 0`.
All exactness and endpoint properties are proved, not parameters. -/
def resolution : CuspNormalization.SheafCohomologyResolution.AugmentedResolution
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ℂ × ℂ))) where
  F := holomorphicSheaf
  complex := dolbeaultComplex
  ι := inclusion
  zero := inclusion_differential
  initial_exact := initialComplex_exact
  exact := dolbeaultComplex_exact
  mono_ι := inclusion_mono
  epi_g := topDifferential_epi

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
