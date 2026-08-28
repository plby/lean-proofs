import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackBundle

/-!
# Holomorphicity descends through surjective local biholomorphisms

A map is holomorphic if its composition with a surjective local
biholomorphism is holomorphic.  At each point, an actual local inverse
gives the required holomorphic expression on a neighborhood.  Neither
continuity of the descended map nor a transported atlas is assumed.
The target can have any complex manifold model.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent

local notation "I" => modelWithCornersSelf ℂ Model

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace Model M]
  [TopologicalSpace N] [ChartedSpace Model N]
  {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {J : ModelWithCorners ℂ E H}
  [TopologicalSpace Z] [ChartedSpace H Z]

/-- Pointwise holomorphic descent using the original local inverse. -/
theorem contMDiffAt_of_comp_localDiffeomorph {q : M → N} {x : M} {F : N → Z}
    (hq : IsLocalDiffeomorphAt I I ω q x)
    (hF : ContMDiffAt I J ω (F ∘ q) x) : ContMDiffAt I J ω F (q x) := by
  have hFi : ContMDiffAt I J ω (F ∘ q) (hq.localInverse (q x)) := by
    rw [hq.localInverse_left_inv hq.localInverse_mem_target]
    exact hF
  have hc : ContMDiffAt I J ω ((F ∘ q) ∘ hq.localInverse) (q x) :=
    hFi.comp (q x) hq.localInverse_contMDiffAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hq.localInverse_eventuallyEq_right] with y hy
  exact (congrArg F hy).symm

/-- Holomorphicity descends through a surjective local biholomorphism,
without any continuity hypothesis on the descended function. -/
theorem contMDiff_of_comp_surjective_localDiffeomorph {q : M → N} {F : N → Z}
    (hq : IsLocalDiffeomorph I I ω q) (hs : Function.Surjective q)
    (hF : ContMDiff I J ω (F ∘ q)) : ContMDiff I J ω F := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  exact contMDiffAt_of_comp_localDiffeomorph (hq x) (hF x)

/-- Holomorphicity can be checked after pullback by a surjective local
biholomorphism, using the given source, target, and codomain atlases. -/
theorem contMDiff_iff_comp_surjective_localDiffeomorph {q : M → N} {F : N → Z}
    (hq : IsLocalDiffeomorph I I ω q) (hs : Function.Surjective q) :
    ContMDiff I J ω F ↔ ContMDiff I J ω (F ∘ q) :=
  ⟨fun hF => hF.comp hq.contMDiff,
    contMDiff_of_comp_surjective_localDiffeomorph hq hs⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent
