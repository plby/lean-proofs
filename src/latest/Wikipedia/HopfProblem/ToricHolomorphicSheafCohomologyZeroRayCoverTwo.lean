import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverSections
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyProjectiveCocycleTwo

/-!
# Actual triple-section surjectivity for the zero-ray cover

The proved projective Laurent splitting is applied to the literal analytic
coefficient of an actual triple-overlap section. Its three outputs are
pulled back through the actual pair-coordinate inverses. Their actual
alternating restrictions equal the original triple-overlap section.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

/-- The actual map `(c₀₁,c₀₂,c₁₂) ↦ c₀₁ - c₀₂ + c₁₂` onto triple sections is surjective. -/
theorem cechTwoSurjective : ThreeCover.CechTwoSurjective componentSheaf cover := by
  intro s
  change Section tripleOpen at s
  obtain ⟨g01, g02, g12, hg01, hg02, hg12, he⟩ :=
    ProjectiveCocycle.exists_triple_overlap_splitting (coefficient_analytic tripleBiholomorph s)
  refine ⟨(sectionFromCoefficient pair01Biholomorph g01 hg01,
    sectionFromCoefficient pair02Biholomorph g02 hg02,
    sectionFromCoefficient pair12Biholomorph g12 hg12), ?_⟩
  apply ContMDiffMap.ext
  intro x
  obtain ⟨q, rfl⟩ := tripleBiholomorph.surjective x
  change g01 (pair01Biholomorph.symm (tripleToPair01 (tripleBiholomorph q))) -
    g02 (pair02Biholomorph.symm (tripleToPair02 (tripleBiholomorph q))) +
      g12 (pair12Biholomorph.symm (tripleToPair12 (tripleBiholomorph q))) = s (tripleBiholomorph q)
  rw [pair01_symm_triple, pair02_symm_triple, pair12_symm_triple]
  exact (he (q : ℂ × ℂ).1 (q : ℂ × ℂ).2 q.property.1 q.property.2).symm.trans
    (coefficient_apply tripleBiholomorph s q)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
