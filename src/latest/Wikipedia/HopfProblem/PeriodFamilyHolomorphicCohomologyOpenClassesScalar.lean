import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesScalarRestriction
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorph

/-!
# Original coefficient scalars and native biholomorphic cohomology

The literal pullback isomorphism of holomorphic sheaves commutes with
the original scalar endomorphisms. Naturality of the actual finite
closed pushforward Ext comparison then proves scalar compatibility of
the existing biholomorphic cohomology equivalence in every degree.
The only separation hypothesis is the source Hausdorff hypothesis of
that existing comparison. No vector-space structure is transported.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses

open HolomorphicSheafCohomology

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (e : Diffeomorph I J M N ω)

/-- The actual holomorphic pullback sheaf isomorphism commutes with
the original scalar maps, by its literal composition formula. -/
@[reassoc] theorem biholomorph_sheafIso_scalar (c : ℂ) :
    HolomorphicFunctionSheaf.scalarSheafEnd J N c ≫
        (Biholomorph.additiveSheafIso e).hom =
      (Biholomorph.additiveSheafIso e).hom ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).map
          (HolomorphicFunctionSheaf.scalarSheafEnd I M c) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The existing native biholomorphic cohomology comparison commutes
with the actual coefficient-scalar maps in every degree. -/
theorem biholomorph_cohomologyEquiv_scalar [T2Space M] (q : ℕ) (c : ℂ)
    (x : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) q) :
    Biholomorph.cohomologyEquiv e q
        (CategoryTheory.Sheaf.H.map (HolomorphicFunctionSheaf.scalarSheafEnd J N c) q x) =
      CategoryTheory.Sheaf.H.map (HolomorphicFunctionSheaf.scalarSheafEnd I M c) q
        (Biholomorph.cohomologyEquiv e q x) := by
  let ef := CuspNormalization.SheafCohomologyFinitePushforward.cohomologyEquiv
    (Biholomorph.underlyingMap e) e.toHomeomorph.isClosedMap
    (Biholomorph.underlyingMap_fibre_finite e)
    (HolomorphicFunctionSheaf.additiveSheaf I M) q
  have hscalar : CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q
      (CategoryTheory.Sheaf.H.map (HolomorphicFunctionSheaf.scalarSheafEnd J N c) q x) =
    CategoryTheory.Sheaf.H.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).map
        (HolomorphicFunctionSheaf.scalarSheafEnd I M c)) q
      (CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q x) := by
    have hl := CategoryTheory.Sheaf.H.map_comp_apply
      (HolomorphicFunctionSheaf.scalarSheafEnd J N c) (Biholomorph.additiveSheafIso e).hom x
    have hr := CategoryTheory.Sheaf.H.map_comp_apply (Biholomorph.additiveSheafIso e).hom
      ((TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).map
        (HolomorphicFunctionSheaf.scalarSheafEnd I M c)) x
    have hm := congrArg
      (fun f : HolomorphicFunctionSheaf.additiveSheaf J N ⟶
          (TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).obj
            (HolomorphicFunctionSheaf.additiveSheaf I M) => CategoryTheory.Sheaf.H.map f q x)
      (biholomorph_sheafIso_scalar e c)
    exact hl.symm.trans (hm.trans hr)
  change ef (CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q
      (CategoryTheory.Sheaf.H.map (HolomorphicFunctionSheaf.scalarSheafEnd J N c) q x)) =
    CategoryTheory.Sheaf.H.map (HolomorphicFunctionSheaf.scalarSheafEnd I M c) q
      (ef (CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q x))
  rw [hscalar]
  exact CuspNormalization.SheafCohomologyFinitePushforward.cohomologyEquiv_naturality
    (Biholomorph.underlyingMap e) e.toHomeomorph.isClosedMap
    (Biholomorph.underlyingMap_fibre_finite e)
    (HolomorphicFunctionSheaf.scalarSheafEnd I M c) q _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses
