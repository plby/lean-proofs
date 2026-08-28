import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryDifferential
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalHomologyBasic

/-!
# Canonical homology comparisons for the actual total terms

The isomorphisms are induced by the original binary-biproduct coordinate
maps. They therefore retain the original total cycles and boundaries.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]

/-- The original degree-one total short complex after the actual functor. -/
def mapOneIso : D.oneComplex.map F ≅ (D.mapData F).oneComplex :=
  ShortComplex.isoMk (Iso.refl _) (D.oneEquiv F).toAddCommGrpIso
    (D.twoEquiv F).toAddCommGrpIso
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (D.oneEquiv_map_d0 F s).symm)
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (D.twoEquiv_map_d1 F s).symm)

/-- The original degree-two total short complex after the actual functor. -/
def mapTwoIso : D.twoComplex.map F ≅ (D.mapData F).twoComplex :=
  ShortComplex.isoMk (D.oneEquiv F).toAddCommGrpIso
    (D.twoEquiv F).toAddCommGrpIso (D.threeEquiv F).toAddCommGrpIso
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (D.twoEquiv_map_d1 F s).symm)
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (D.threeEquiv_map_d2 F s).symm)

/-- Genuine degree-one homology under the canonical component comparison. -/
def mapOneHomologyIso : (D.oneComplex.map F).homology ≅
    (D.mapData F).oneComplex.homology := ShortComplex.homologyMapIso (D.mapOneIso F)

/-- Genuine degree-two homology under the canonical component comparison. -/
def mapTwoHomologyIso : (D.twoComplex.map F).homology ≅
    (D.mapData F).twoComplex.homology := ShortComplex.homologyMapIso (D.mapTwoIso F)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data
