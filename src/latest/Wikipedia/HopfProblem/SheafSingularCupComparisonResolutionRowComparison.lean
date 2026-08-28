import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRowAcyclic

/-!
# The actual row comparison is the original singular-cohomology comparison

Naturality for the genuine map of partial resolutions, followed by the
original window isomorphism, identifies the row comparisons with the
original `LowExt.CochainResolution.h1Iso` and `h2Iso`. The augmentation
map in both squares is the original complex constant-sheaf comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow

open CuspNormalization ConstantSheafSingularComparison

variable (X : TopCat.{0})

/-- The original row map on global degree-one homology, followed by its standard window map. -/
def rowOneToOriginalHomology (hLC : LocallyContractibleSpace X) :
    (rowPartialResolution X hLC).globalOneComplex.homology ⟶
      (originalResolution X hLC).globalCochainComplex.homology 1 :=
  ShortComplex.homologyMap (rowToOriginal X hLC).globalOneMap ≫
    (Resolution.oneWindowIso (originalResolution X hLC)).hom

/-- The original row map on global degree-two homology, followed by its standard window map. -/
def rowTwoToOriginalHomology (hLC : LocallyContractibleSpace X) :
    (rowPartialResolution X hLC).globalTwoComplex.homology ⟶
      (originalResolution X hLC).globalCochainComplex.homology 2 :=
  ShortComplex.homologyMap (rowToOriginal X hLC).globalTwoMap ≫
    (Resolution.twoWindowIso (originalResolution X hLC)).hom

variable [CompactSpace X] [T2Space X]

local instance original_zero_one_subsingleton (hLC : LocallyContractibleSpace X) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} ((originalResolution X hLC).K.X 0) 1) :=
  FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 0 0

local instance original_zero_two_subsingleton (hLC : LocallyContractibleSpace X) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} ((originalResolution X hLC).K.X 0) 2) :=
  FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 0 1

local instance original_one_one_subsingleton (hLC : LocallyContractibleSpace X) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} ((originalResolution X hLC).K.X 1) 1) :=
  FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 1 0

/-- The exact comparison square with the original native degree-one resolution isomorphism. -/
theorem rowToOriginal_h1Iso (hLC : LocallyContractibleSpace X) :
    (CategoryTheory.Sheaf.functorH _ 1).map (SheafConstants.complexAdditiveSheafIso X).hom ≫
        (originalResolution X hLC).h1Iso.hom =
      (rowH1Iso X hLC).hom ≫ rowOneToOriginalHomology X hLC := by
  let R := rowPartialResolution X hLC
  let S := Resolution.ofCochain (originalResolution X hLC)
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1) := row_zero_one_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 1) :=
    original_zero_one_subsingleton X hLC
  let w := (Resolution.oneWindowIso (originalResolution X hLC)).hom
  let f := (CategoryTheory.Sheaf.functorH _ 1).map
    (SheafConstants.complexAdditiveSheafIso X).hom
  have h : S.h1IsoAcyclic.hom ≫ w = (originalResolution X hLC).h1Iso.hom :=
    congrArg Iso.hom (Resolution.ofCochain_h1IsoAcyclic (originalResolution X hLC))
  have hn := (rowToOriginal X hLC).h1IsoAcyclic_naturality
  exact (congrArg (fun a => f ≫ a) h.symm).trans
    ((Category.assoc f S.h1IsoAcyclic.hom w).symm.trans
      ((congrArg (fun a => a ≫ w) hn).trans
        (Category.assoc R.h1IsoAcyclic.hom
          (ShortComplex.homologyMap (rowToOriginal X hLC).globalOneMap) w)))

/-- The exact comparison square with the original native degree-two resolution isomorphism. -/
theorem rowToOriginal_h2Iso (hLC : LocallyContractibleSpace X) :
    (CategoryTheory.Sheaf.functorH _ 2).map (SheafConstants.complexAdditiveSheafIso X).hom ≫
        (originalResolution X hLC).h2Iso.hom =
      (rowH2Iso X hLC).hom ≫ rowTwoToOriginalHomology X hLC := by
  let R := rowPartialResolution X hLC
  let S := Resolution.ofCochain (originalResolution X hLC)
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1) := row_zero_one_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 2) := row_zero_two_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₁ 1) := row_one_one_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 1) :=
    original_zero_one_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 2) :=
    original_zero_two_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₁ 1) :=
    original_one_one_subsingleton X hLC
  let w := (Resolution.twoWindowIso (originalResolution X hLC)).hom
  let f := (CategoryTheory.Sheaf.functorH _ 2).map
    (SheafConstants.complexAdditiveSheafIso X).hom
  have h : S.h2IsoAcyclic.hom ≫ w = (originalResolution X hLC).h2Iso.hom :=
    congrArg Iso.hom (Resolution.ofCochain_h2IsoAcyclic (originalResolution X hLC))
  have hn := (rowToOriginal X hLC).h2IsoAcyclic_naturality
  exact (congrArg (fun a => f ≫ a) h.symm).trans
    ((Category.assoc f S.h2IsoAcyclic.hom w).symm.trans
      ((congrArg (fun a => a ≫ w) hn).trans
        (Category.assoc R.h2IsoAcyclic.hom
          (ShortComplex.homologyMap (rowToOriginal X hLC).globalTwoMap) w)))

end Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow
