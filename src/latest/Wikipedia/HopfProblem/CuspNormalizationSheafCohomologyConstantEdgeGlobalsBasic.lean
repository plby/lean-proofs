import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCompact
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# Actual constant-to-holomorphic global-section isomorphisms

On a compact connected complex manifold every actual holomorphic global
section is constant. Its scalar value lifts through the literal constant
sheafification unit. Together with the proved actual inclusion, this
gives an isomorphism on genuine global sections, including actual direct
images. No higher constant-sheaf acyclicity is used.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafCohomologyResolution SheafCohomologyGlobalSections HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I 1 M] [CompactSpace M] [ConnectedSpace M]

/-- The genuine constant-sheaf unit supplies a preimage of every actual
holomorphic global section, by the compact maximum principle. -/
theorem constantsGlobal_surjective : Function.Surjective
    ((globalSectionsFunctor (TopCat.of M)).map (SheafConstants.holomorphicAdditiveMap I M)) := by
  intro s
  change GlobalSections I M at s
  let x : M := Classical.choice inferInstance
  refine ⟨(SheafConstants.additiveUnit (TopCat.of M)).app (op ⊤)
    (s (toTopOpen M x)), ?_⟩
  apply ContMDiffMap.ext
  intro y
  exact (SheafConstants.holomorphicAdditiveMap_unit I M ⊤ _ y).trans
    (compact_global_apply_eq I M s x y)

/-- This is the actual global-sections map of the actual constants inclusion. -/
theorem constantsGlobal_isIso :
    IsIso ((globalSectionsFunctor (TopCat.of M)).map
      (SheafConstants.holomorphicAdditiveMap I M)) := by
  have : Mono ((globalSectionsFunctor (TopCat.of M)).map
      (SheafConstants.holomorphicAdditiveMap I M)) := by infer_instance
  have : Epi ((globalSectionsFunctor (TopCat.of M)).map
      (SheafConstants.holomorphicAdditiveMap I M)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (constantsGlobal_surjective I M)
  exact isIso_of_mono_of_epi _

variable {Y : TopCat.{0}} (p : TopCat.of M ⟶ Y)

/-- Direct-image global sections are the literal source global sections. -/
theorem pushforwardConstantsGlobal_surjective : Function.Surjective
    ((globalSectionsFunctor Y).map ((TopCat.Sheaf.pushforward AddCommGrpCat p).map
      (SheafConstants.holomorphicAdditiveMap I M))) :=
  constantsGlobal_surjective I M

/-- The actual constants inclusion on an actual direct image is likewise
an isomorphism on actual global sections. -/
theorem pushforwardConstantsGlobal_isIso :
    IsIso ((globalSectionsFunctor Y).map ((TopCat.Sheaf.pushforward AddCommGrpCat p).map
      (SheafConstants.holomorphicAdditiveMap I M))) :=
  constantsGlobal_isIso I M

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge
