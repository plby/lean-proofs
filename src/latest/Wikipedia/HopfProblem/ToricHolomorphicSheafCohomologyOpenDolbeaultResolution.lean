import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultExact
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultSmooth
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionSheaf
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionGlobal
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# The true Dolbeault resolution restricted to an actual affine open set

Exact open restriction preserves the already proved actual Dolbeault
resolution. The holomorphic and smooth terms are identified with the
actual function sheaves on the open submanifold by literal flattening.
The actual global-section comparison retains the original coordinate
derivative formulas on the original open domain.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

open CuspNormalization.SheafCohomologyResolution

abbrev restriction (Ω : Opens (ℂ × ℂ)) := OpenRestriction.restriction (X := TopCat.of (ℂ × ℂ)) Ω

instance restriction_additive (Ω : Opens (ℂ × ℂ)) : (restriction Ω).Additive :=
  OpenRestriction.restriction_additive (X := TopCat.of (ℂ × ℂ)) Ω

instance restriction_preservesFiniteLimits (Ω : Opens (ℂ × ℂ)) :
    PreservesFiniteLimits (restriction Ω) :=
  OpenRestriction.restriction_preservesFiniteLimits (X := TopCat.of (ℂ × ℂ)) Ω

instance restriction_preservesFiniteColimits (Ω : Opens (ℂ × ℂ)) :
    PreservesFiniteColimits (restriction Ω) :=
  OpenRestriction.restriction_preservesFiniteColimits (X := TopCat.of (ℂ × ℂ)) Ω

abbrev restrictedHolomorphicSheaf (Ω : Opens (ℂ × ℂ)) :=
  (restriction Ω).obj AffineDolbeault.holomorphicSheaf
abbrev restrictedSmoothSheaf (Ω : Opens (ℂ × ℂ)) :=
  (restriction Ω).obj AffineDolbeault.smoothSheaf
abbrev restrictedPairSheaf (Ω : Opens (ℂ × ℂ)) :=
  (restriction Ω).obj AffineDolbeault.pairSheaf

/-- The actual restricted complex, with no replacement differential. -/
abbrev restrictedComplex (Ω : Opens (ℂ × ℂ)) :=
  AffineDolbeault.dolbeaultComplex.map (restriction Ω)

/-- Exact restriction gives the genuine exact Dolbeault sheaf sequence on Ω. -/
def restrictedResolution (Ω : Opens (ℂ × ℂ)) :
    AugmentedResolution (TopCat.Sheaf AddCommGrpCat (TopCat.of Ω)) where
  F := restrictedHolomorphicSheaf Ω
  complex := restrictedComplex Ω
  ι := (restriction Ω).map AffineDolbeault.inclusion
  zero := (AffineDolbeault.initialComplex.map (restriction Ω)).zero
  initial_exact := AffineDolbeault.initialComplex_exact.map (restriction Ω)
  exact := AffineDolbeault.dolbeaultComplex_exact.map (restriction Ω)
  mono_ι := by
    change Mono ((restriction Ω).map AffineDolbeault.inclusion)
    infer_instance
  epi_g := by
    change Epi ((restriction Ω).map AffineDolbeault.topDifferential)
    infer_instance

/-- The first term is the actual holomorphic function sheaf of Ω. -/
def holomorphicSheafIso (Ω : Opens (ℂ × ℂ)) :
    restrictedHolomorphicSheaf Ω ≅ HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) Ω :=
  HolomorphicRestriction.sheafIso 𝓘(ℂ, ℂ × ℂ) Ω

/-- The smooth terms are the actual smooth function sheaf of Ω. -/
def smoothIso (Ω : Opens (ℂ × ℂ)) :
    restrictedSmoothSheaf Ω ≅ SmoothFunctions.additiveSheaf 𝓘(ℝ, ℂ × ℂ) Ω :=
  smoothSheafIso 𝓘(ℝ, ℂ × ℂ) Ω

/-- The literal section complex on the original open domain. -/
def sectionComplex (Ω : Opens (ℂ × ℂ)) : ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    (AddCommGrpCat.ofHom (AffineDolbeault.differentialSection Ω).toAddMonoidHom)
    (AddCommGrpCat.ofHom (AffineDolbeault.topSection Ω).toAddMonoidHom)
    (by
      apply AddCommGrpCat.hom_ext
      exact AddMonoidHom.ext (AffineDolbeault.topSection_differentialSection Ω))

/-- Restriction's canonical global-section equivalence intertwines the
actual differentials with their literal derivative formulas on Ω. -/
def globalComplexIso (Ω : Opens (ℂ × ℂ)) :
    (restrictedResolution Ω).globalComplex ≅ sectionComplex Ω :=
  ShortComplex.isoMk
    (OpenRestriction.restrictionGlobalEquiv (X := TopCat.of (ℂ × ℂ)) Ω
      AffineDolbeault.smoothSheaf).toAddCommGrpIso
    (OpenRestriction.restrictionGlobalEquiv (X := TopCat.of (ℂ × ℂ)) Ω
      AffineDolbeault.pairSheaf).toAddCommGrpIso
    (OpenRestriction.restrictionGlobalEquiv (X := TopCat.of (ℂ × ℂ)) Ω
      AffineDolbeault.smoothSheaf).toAddCommGrpIso
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (OpenRestriction.restrictionGlobalEquiv_naturality (X := TopCat.of (ℂ × ℂ)) Ω
        AffineDolbeault.differential s).symm)
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (OpenRestriction.restrictionGlobalEquiv_naturality (X := TopCat.of (ℂ × ℂ)) Ω
        AffineDolbeault.topDifferential s).symm)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
