import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferentialSheaf
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalManifold
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultSheafExact

/-!
# The actual native degree-one Dolbeault short exact sequence

The original holomorphic kernel and the genuine local Cauchy--Green
primitives prove `0 → O → A⁰ → Z¹ → 0` in the actual abelian-sheaf
category.  Closedness, local solvability, and exactness are all proved;
none of them is a hypothesis of this native threefold statement.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

variable (M : Type) [TopologicalSpace M] [ChartedSpace Model M]
  [IsManifold 𝓘(ℂ, Model) ω M] [IsManifold 𝓘(ℝ, Model) ∞ M]

/-- The initial kernel is the actual holomorphic function sheaf. -/
theorem initialComplex_exact : (initialComplex Model M).Exact := by
  apply HolomorphicSheafCohomology.DolbeaultLocal.exact_of_section_kernels
    (initialComplex Model M)
  intro U s hs
  have hplain := congrArg (ClosedForms.toFormLinearMap Model M U) hs
  change differentialSection Model M U s = 0 at hplain
  exact exists_holomorphic_preimage M U s hplain

/-- Every germ of an actual native closed form has a genuine smooth
primitive; hence the original native sheaf differential is epic. -/
instance closedDifferential_epi : Epi (closedDifferential Model M) := by
  apply HolomorphicSheafCohomology.DolbeaultLocal.epi_of_local_section_lifts
    (closedDifferential Model M)
  intro U x hx s
  obtain ⟨V, hVU, hxV, t, ht⟩ := LocalManifold.exists_local_primitive M s ⟨x, hx⟩
  refine ⟨V, hVU, hxV, t, ?_⟩
  apply ClosedForms.toFormLinearMap_injective Model M V
  exact ht

/-- The genuine native short exact sequence `0 → O → A⁰ → Z¹ → 0`. -/
theorem initialComplex_shortExact : (initialComplex Model M).ShortExact where
  exact := initialComplex_exact M
  mono_f := Functions.inclusion_mono Model M
  epi_g := closedDifferential_epi M

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential
