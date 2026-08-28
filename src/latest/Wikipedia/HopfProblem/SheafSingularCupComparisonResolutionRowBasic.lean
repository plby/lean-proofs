import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionTruncation
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingDifferential
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingAugmentation

/-!
# The actual singular-cochain row with its original constant augmentation

The terms are the actual ring-cochain sheaves with multiplication
forgotten. The augmentation and differentials are the original ring
augmentation and literal alternating coface maps. Their comparison
with the original additive singular complex proves that this is a
complex, on every topological space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow

open CuspNormalization ConstantSheafSingularComparison
open RingCochains

variable (X : TopCat.{0})

/-- The actual additive sheaf underlying the ring of singular cochains. -/
abbrev rowTerm (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (forgetSheaf X).obj (sheaf X n)

/-- The original ring augmentation, retaining its actual additive map. -/
abbrev rowAugmentation : SheafConstants.complexAdditiveSheaf X ⟶ rowTerm X 0 :=
  (forgetSheaf X).map (augmentation X)

/-- The original constant augmentation is killed by the first actual differential. -/
theorem rowAugmentation_d0 : rowAugmentation X ≫ d0 X = 0 := by
  apply (cancel_mono (forgetSheafIso X 1).hom).mp
  change ((forgetSheaf X).map (augmentation X) ≫ d0 X) ≫
    (forgetSheafIso X 1).hom = 0 ≫ (forgetSheafIso X 1).hom
  rw [zero_comp, Category.assoc, d0_additive, ← Category.assoc,
    augmentation_additive]
  exact (Category.assoc (SheafConstants.complexAdditiveSheafIso X).hom
    (sheafAugmentation X (AddCommGrpCat.of ℂ))
    (sheafDifferential X (AddCommGrpCat.of ℂ) 0 1)).trans
      ((congrArg (fun f => (SheafConstants.complexAdditiveSheafIso X).hom ≫ f)
        (sheafAugmentation_d X (AddCommGrpCat.of ℂ))).trans (comp_zero))

/-- The two literal first alternating differentials compose to zero. -/
theorem row_d0_d1 : d0 X ≫ d1 X = 0 := by
  have h : sheafDifferential X (AddCommGrpCat.of ℂ) 0 1 ≫
      sheafDifferential X (AddCommGrpCat.of ℂ) 1 2 = 0 :=
    (cochainSheafComplex X (AddCommGrpCat.of ℂ)).d_comp_d 0 1 2
  apply (cancel_mono (forgetSheafIso X 2).hom).mp
  rw [zero_comp, Category.assoc, d1_additive, ← Category.assoc,
    d0_additive, Category.assoc, h, comp_zero]

/-- The two literal next alternating differentials compose to zero. -/
theorem row_d1_d2 : d1 X ≫ d2 X = 0 := by
  have h : sheafDifferential X (AddCommGrpCat.of ℂ) 1 2 ≫
      sheafDifferential X (AddCommGrpCat.of ℂ) 2 3 = 0 :=
    (cochainSheafComplex X (AddCommGrpCat.of ℂ)).d_comp_d 1 2 3
  apply (cancel_mono (forgetSheafIso X 3).hom).mp
  rw [zero_comp, Category.assoc, d2_additive, ← Category.assoc,
    d1_additive, Category.assoc, h, comp_zero]

/-- The original augmented first three terms of the actual row. -/
abbrev rowInitialComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (rowAugmentation X) (d0 X) (rowAugmentation_d0 X)

abbrev rowOneComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (d0 X) (d1 X) (row_d0_d1 X)

abbrev rowTwoComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (d1 X) (d2 X) (row_d1_d2 X)

/-- The comparison is the original constant and cochain isomorphisms, term by term. -/
def rowInitialIso : rowInitialComplex X ≅
    initialSheafComplex X (AddCommGrpCat.of ℂ) :=
  ShortComplex.isoMk (SheafConstants.complexAdditiveSheafIso X)
    (forgetSheafIso X 0) (forgetSheafIso X 1)
    (augmentation_additive X).symm (d0_additive X).symm

/-- The original first cochain window, with no replaced differential. -/
def rowOneIso : rowOneComplex X ≅
    (cochainSheafComplex X (AddCommGrpCat.of ℂ)).sc' 0 1 2 :=
  ShortComplex.isoMk (forgetSheafIso X 0) (forgetSheafIso X 1) (forgetSheafIso X 2)
    (d0_additive X).symm (d1_additive X).symm

/-- The original second cochain window, with no replaced differential. -/
def rowTwoIso : rowTwoComplex X ≅
    (cochainSheafComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3 :=
  ShortComplex.isoMk (forgetSheafIso X 1) (forgetSheafIso X 2) (forgetSheafIso X 3)
    (d1_additive X).symm (d2_additive X).symm

end Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow
