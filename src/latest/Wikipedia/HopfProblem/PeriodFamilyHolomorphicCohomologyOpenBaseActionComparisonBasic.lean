import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorph

/-!
# Coefficient naturality of the original biholomorphic comparison

An actual square of holomorphic sheaf endomorphisms induces the same square
on native sheaf cohomology under the existing biholomorphic comparison.
The proof uses the original coefficient maps and the naturality of finite
closed pushforward in every degree; it does not transport a module structure.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction

open HolomorphicSheafCohomology

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (e : Diffeomorph I J M N ω)

/-- The original biholomorphic cohomology comparison respects any actual
coefficient square, in every degree. -/
theorem biholomorph_cohomologyEquiv_naturality [T2Space M]
    (f : HolomorphicFunctionSheaf.additiveSheaf J N ⟶
      HolomorphicFunctionSheaf.additiveSheaf J N)
    (g : HolomorphicFunctionSheaf.additiveSheaf I M ⟶
      HolomorphicFunctionSheaf.additiveSheaf I M)
    (hfg : f ≫ (Biholomorph.additiveSheafIso e).hom =
      (Biholomorph.additiveSheafIso e).hom ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).map g)
    (q : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) q) :
    Biholomorph.cohomologyEquiv e q (CategoryTheory.Sheaf.H.map f q x) =
      CategoryTheory.Sheaf.H.map g q (Biholomorph.cohomologyEquiv e q x) := by
  let ef := CuspNormalization.SheafCohomologyFinitePushforward.cohomologyEquiv
    (Biholomorph.underlyingMap e) e.toHomeomorph.isClosedMap
    (Biholomorph.underlyingMap_fibre_finite e)
    (HolomorphicFunctionSheaf.additiveSheaf I M) q
  have hnatural : CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q
      (CategoryTheory.Sheaf.H.map f q x) =
    CategoryTheory.Sheaf.H.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).map g) q
      (CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q x) := by
    have hl := CategoryTheory.Sheaf.H.map_comp_apply f (Biholomorph.additiveSheafIso e).hom x
    have hr := CategoryTheory.Sheaf.H.map_comp_apply (Biholomorph.additiveSheafIso e).hom
      ((TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).map g) x
    have hm := congrArg
      (fun k : HolomorphicFunctionSheaf.additiveSheaf J N ⟶
          (TopCat.Sheaf.pushforward AddCommGrpCat (Biholomorph.underlyingMap e)).obj
            (HolomorphicFunctionSheaf.additiveSheaf I M) => CategoryTheory.Sheaf.H.map k q x)
      hfg
    exact hl.symm.trans (hm.trans hr)
  change ef (CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q
      (CategoryTheory.Sheaf.H.map f q x)) =
    CategoryTheory.Sheaf.H.map g q
      (ef (CategoryTheory.Sheaf.H.map (Biholomorph.additiveSheafIso e).hom q x))
  rw [hnatural]
  exact CuspNormalization.SheafCohomologyFinitePushforward.cohomologyEquiv_naturality
    (Biholomorph.underlyingMap e) e.toHomeomorph.isClosedMap
    (Biholomorph.underlyingMap_fibre_finite e) g q _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction
