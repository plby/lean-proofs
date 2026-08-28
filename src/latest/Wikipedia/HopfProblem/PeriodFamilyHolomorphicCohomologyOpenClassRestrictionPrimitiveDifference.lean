import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionPrimitiveDifferenceBasic

/-!
# Holomorphy of differences between continuous local primitives

The common map is holomorphic in the original varying-period quotient atlas.
Its arbitrary continuous local lifts need not be holomorphic: their primitive
difference agrees locally with a holomorphic lattice character on the base.
-/

noncomputable section

open Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.PrimitiveDifference

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The literal difference of the actual primitive along two continuous local
lifts is holomorphic at the point whenever their common projected map is
holomorphic there in the original total-space atlas. -/
theorem difference_holomorphicAt (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) (f : M → P.TotalSpace)
    (l₀ l₁ : M → B × ComplexPlane₂) {x : M}
    (h₀ : ContinuousAt l₀ x) (h₁ : ContinuousAt l₁ x)
    (hq₀ : (P.quotientMap ∘ l₀) =ᶠ[𝓝 x] f)
    (hq₁ : (P.quotientMap ∘ l₁) =ᶠ[𝓝 x] f)
    (hf : letI := P.totalChartedSpace
      ContMDiffAt I (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω f x) :
    ContMDiffAt I 𝓘(ℂ) ω
      (fun y => Cocycle.primitive P a (l₀ y) - Cocycle.primitive P a (l₁ y)) x := by
  let := P.totalChartedSpace
  obtain ⟨g, hg⟩ := difference_eventually_character P a f l₀ l₁ h₀ h₁ hq₀ hq₁
  have h := ((Cocycle.character_holomorphic a g).comp
    P.projection_holomorphic).contMDiffAt.comp x hf
  exact h.congr_of_eventuallyEq hg

end OpenClassRestriction.PrimitiveDifference
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
