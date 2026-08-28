import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyCech
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreClass
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorph
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionRepresentation

/-!
# Agreement with the original biholomorphic cohomology equivalence

Both maps preserve actual Čech extension classes by the proved native
comparison theorems, and their original holomorphic coefficient maps
are literally the same functions. Every native degree-one class has a
proved genuine Čech representative, so the two original cohomology maps
agree on every class. The only Hausdorff premise is the one already
required by the original finite-closed biholomorphic comparison.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicCohomology

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open HolomorphicSheafCohomology

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]

/-- The coefficient map is the original biholomorphic sheaf isomorphism,
as an equality of actual all-open holomorphic pullbacks. -/
theorem pushforwardCoefficientMap_biholomorph (e : Diffeomorph I J M N ω) :
    pushforwardCoefficientMap I J (Biholomorph.underlyingMap e)
        e.toHomeomorph.isOpenEmbedding e.contMDiff =
      (Biholomorph.additiveSheafIso e).hom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- On every original native degree-one class, the actual holomorphic
pullback equals the original biholomorphic cohomology comparison. -/
theorem pullback_biholomorph [T2Space M] (e : Diffeomorph I J M N ω)
    (a : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) 1) :
    pullback I J (Biholomorph.underlyingMap e) e.toHomeomorph.isOpenEmbedding e.contMDiff 1 a =
      Biholomorph.cohomologyEquiv e 1 a := by
  obtain ⟨U, hU, c, rfl⟩ := exists_classOf_eq (X := TopCat.of N)
    (HolomorphicFunctionSheaf.additiveSheaf J N) a
  have hc := pullback_classOf I J (Biholomorph.underlyingMap e)
    e.toHomeomorph.isOpenEmbedding e.contMDiff c hU
  have he := congrArg (fun κ => CechFibre.pullbackCocycle (Biholomorph.underlyingMap e) κ c)
    (pushforwardCoefficientMap_biholomorph I J e)
  have hb := CechFibre.cohomologyEquiv_map_classOf (Biholomorph.underlyingMap e)
    e.toHomeomorph.isClosedMap (Biholomorph.underlyingMap_fibre_finite e)
    (Biholomorph.additiveSheafIso e).hom c hU
  exact hc.trans ((congrArg (fun d => classOf d
    (CechFibre.pullbackCover_covers (Biholomorph.underlyingMap e) hU)) he).trans hb.symm)

end OpenClassRestriction.HolomorphicCohomology
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
