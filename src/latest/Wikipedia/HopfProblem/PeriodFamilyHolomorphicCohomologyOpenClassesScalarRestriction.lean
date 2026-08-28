import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroScalars

/-!
# Original coefficient scalars and the native open-restriction comparison

The literal holomorphic sheaf isomorphism for an open submanifold
commutes with multiplication by complex constants on the original
sections. Naturality of the actual open-restriction Ext comparison
therefore gives scalar compatibility in every native cohomology degree.
No module structure is transported through a cohomology equivalence.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses

open HolomorphicSheafCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The genuine open-submanifold sheaf comparison commutes with the
original coefficient scalar endomorphisms, by its literal section formula. -/
@[reassoc] theorem holomorphicRestriction_sheafIso_scalar (U : Opens M) (c : ℂ) :
    (OpenRestriction.restriction (X := TopCat.of M) U).map
        (HolomorphicFunctionSheaf.scalarSheafEnd I M c) ≫
      (HolomorphicRestriction.sheafIso I U).hom =
    (HolomorphicRestriction.sheafIso I U).hom ≫
      HolomorphicFunctionSheaf.scalarSheafEnd I U c := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The actual ambient-open cohomology comparison preserves the map
induced by the original scalar sheaf endomorphism in every degree. -/
theorem holomorphicRestriction_cohomologyEquiv_scalar (U : Opens M) (q : ℕ)
    (c : ℂ) (x : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf I M) q U) :
    HolomorphicRestriction.cohomologyEquiv I U q
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of M)) q).map
            (HolomorphicFunctionSheaf.scalarSheafEnd I M c)).app (op U) x) =
      CategoryTheory.Sheaf.H.map (HolomorphicFunctionSheaf.scalarSheafEnd I U c) q
        (HolomorphicRestriction.cohomologyEquiv I U q x) := by
  change CategoryTheory.Sheaf.H.map (HolomorphicRestriction.sheafIso I U).hom q
      (OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
        (HolomorphicFunctionSheaf.additiveSheaf I M) q
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of M)) q).map
            (HolomorphicFunctionSheaf.scalarSheafEnd I M c)).app (op U) x)) =
    CategoryTheory.Sheaf.H.map (HolomorphicFunctionSheaf.scalarSheafEnd I U c) q
      (CategoryTheory.Sheaf.H.map (HolomorphicRestriction.sheafIso I U).hom q
        (OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
          (HolomorphicFunctionSheaf.additiveSheaf I M) q x))
  let y := OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
    (HolomorphicFunctionSheaf.additiveSheaf I M) q x
  have hn := OpenRestriction.cohomologyEquiv_naturality (X := TopCat.of M) U
    (HolomorphicFunctionSheaf.scalarSheafEnd I M c) q x
  have hl := CategoryTheory.Sheaf.H.map_comp_apply
    ((OpenRestriction.restriction (X := TopCat.of M) U).map
      (HolomorphicFunctionSheaf.scalarSheafEnd I M c))
    (HolomorphicRestriction.sheafIso I U).hom y
  have hr := CategoryTheory.Sheaf.H.map_comp_apply
    (HolomorphicRestriction.sheafIso I U).hom
    (HolomorphicFunctionSheaf.scalarSheafEnd I U c) y
  have hm := congrArg
    (fun f : (OpenRestriction.restriction (X := TopCat.of M) U).obj
        (HolomorphicFunctionSheaf.additiveSheaf I M) ⟶
          HolomorphicFunctionSheaf.additiveSheaf I U => CategoryTheory.Sheaf.H.map f q y)
    (holomorphicRestriction_sheafIso_scalar I U c)
  exact (congrArg (CategoryTheory.Sheaf.H.map (HolomorphicRestriction.sheafIso I U).hom q)
    hn).trans (hl.symm.trans (hm.trans hr))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses
