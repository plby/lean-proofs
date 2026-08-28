import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology

/-!
# Coefficient naturality of the original holomorphic open restriction

An actual coefficient square across the literal holomorphic restriction
sheaf isomorphism induces the corresponding square on native cohomology.
The proof uses exact open restriction and the original coefficient maps
in every degree, with no separation or additional manifold hypothesis.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction.GlobalRestriction

open HolomorphicSheafCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The actual ambient-open comparison respects any original coefficient
square with the open-submanifold holomorphic sheaf, in every degree. -/
theorem holomorphicRestriction_cohomologyEquiv_naturality (U : Opens M)
    (f : HolomorphicFunctionSheaf.additiveSheaf I M ⟶
      HolomorphicFunctionSheaf.additiveSheaf I M)
    (g : HolomorphicFunctionSheaf.additiveSheaf I U ⟶
      HolomorphicFunctionSheaf.additiveSheaf I U)
    (hfg : (OpenRestriction.restriction (X := TopCat.of M) U).map f ≫
        (HolomorphicRestriction.sheafIso I U).hom =
      (HolomorphicRestriction.sheafIso I U).hom ≫ g)
    (q : ℕ) (x : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf I M) q U) :
    HolomorphicRestriction.cohomologyEquiv I U q
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of M)) q).map f).app (op U) x) =
      CategoryTheory.Sheaf.H.map g q (HolomorphicRestriction.cohomologyEquiv I U q x) := by
  change CategoryTheory.Sheaf.H.map (HolomorphicRestriction.sheafIso I U).hom q
      (OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
        (HolomorphicFunctionSheaf.additiveSheaf I M) q
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of M)) q).map f).app (op U) x)) =
    CategoryTheory.Sheaf.H.map g q
      (CategoryTheory.Sheaf.H.map (HolomorphicRestriction.sheafIso I U).hom q
        (OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
          (HolomorphicFunctionSheaf.additiveSheaf I M) q x))
  let y := OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
    (HolomorphicFunctionSheaf.additiveSheaf I M) q x
  have hn := OpenRestriction.cohomologyEquiv_naturality (X := TopCat.of M) U f q x
  have hl := CategoryTheory.Sheaf.H.map_comp_apply
    ((OpenRestriction.restriction (X := TopCat.of M) U).map f)
    (HolomorphicRestriction.sheafIso I U).hom y
  have hr := CategoryTheory.Sheaf.H.map_comp_apply
    (HolomorphicRestriction.sheafIso I U).hom g y
  have hm := congrArg
    (fun k : (OpenRestriction.restriction (X := TopCat.of M) U).obj
        (HolomorphicFunctionSheaf.additiveSheaf I M) ⟶
          HolomorphicFunctionSheaf.additiveSheaf I U => CategoryTheory.Sheaf.H.map k q y)
    hfg
  exact (congrArg (CategoryTheory.Sheaf.H.map (HolomorphicRestriction.sheafIso I U).hom q)
    hn).trans (hl.symm.trans (hm.trans hr))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction.GlobalRestriction
