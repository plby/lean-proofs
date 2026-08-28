import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalSections
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupNativePairs
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowBasic
import Wikipedia.HopfProblem.SheafCupProductGodementExactSheaf

/-!
# Actual Dolbeault row augmentations in the total diagram

The column maps are the original section-to-germs map, its literal pair
map, and the unique isomorphism between the two genuine zero sheaves.
Commutation with the original Dolbeault row is reduced to the actual
derivation--germ squares.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total

open SheafCupProduct SheafSingularCupComparison

variable (p : PeriodDomain)

/-- The original smooth-function column augmentation. -/
def columnUnit0 : PeriodTorusHolomorphicCohomology.Dolbeault.smoothSheaf p ⟶
    GodementExact.I0 (Derivation.smoothRingSheaf p) :=
  GodementExact.augmentation (Derivation.smoothRingSheaf p)

/-- Actual iterated derivations with their original germ naturality. -/
structure CompatibleOperators where
  ringOperators : RingOperators (Derivation.smoothRingSheaf p)
  unit_derivative : ∀ i, columnUnit0 p ≫ (ringOperators.deriv0 i).map =
    Derivation.derivativeMap p i ≫ columnUnit0 p

/-- The original pair column augmentation, retaining the native two coefficients. -/
def columnUnit1 : PeriodTorusHolomorphicCohomology.Dolbeault.pairSheaf p ⟶
    Pairs.sheaf (GodementExact.I0 (Derivation.smoothRingSheaf p)) :=
  (nativePairIso p).hom ≫ Pairs.map (columnUnit0 p)

/-- The original top-coefficient column has the same genuine germ map. -/
abbrev columnUnit2 := columnUnit0 p

/-- The last column is the actual zero-sheaf isomorphism. -/
def columnUnit3 : (0 : Pairs.AbSheaf (TopCat.of p.Torus)) ⟶
    zeroSheaf (TopCat.of p.Torus) := (zeroSheafIso _).inv

namespace CompatibleOperators

variable {p} (D : CompatibleOperators p)

abbrev categoryData := D.ringOperators.categoryData
abbrev globalData := D.ringOperators.globalData

/-- The first native Dolbeault differential commutes with the original germ map. -/
theorem columnUnit_d0 : columnUnit0 p ≫ D.categoryData.h00 =
    PeriodTorusHolomorphicCohomology.Dolbeault.differential p ≫ columnUnit1 p := by
  apply Pairs.hom_ext
  · exact D.unit_derivative 0
  · exact D.unit_derivative 1

/-- The alternating top derivative retains its original sign in the germ square. -/
theorem columnUnit_d1 : columnUnit1 p ≫ D.categoryData.h01 =
    PeriodTorusHolomorphicCohomology.Dolbeault.topDifferential p ≫ columnUnit2 p := by
  apply (cancel_epi (nativePairIso p).inv).mp
  simp only [columnUnit1, Category.assoc, Iso.inv_hom_id_assoc]
  change Pairs.map (columnUnit0 p) ≫ D.ringOperators.operators.top0 =
    (nativePairIso p).inv ≫
      PeriodTorusHolomorphicCohomology.Dolbeault.topDifferential p ≫ columnUnit0 p
  rw [← Category.assoc, nativePair_topDifferential]
  simp only [Operators.top0, Preadditive.comp_sub, Preadditive.sub_comp,
    Pairs.map_snd_assoc, Pairs.map_fst_assoc, Category.assoc]
  exact congrArg₂ (fun f g => Pairs.snd _ ≫ f - Pairs.fst _ ≫ g)
    (D.unit_derivative 0) (D.unit_derivative 1)

/-- The final row and column are literally zero. -/
theorem columnUnit_d2 : columnUnit2 p ≫ D.categoryData.h02 =
    (Row.partialResolution p).d₂ ≫ columnUnit3 p := by
  change columnUnit2 p ≫ 0 = 0 ≫ columnUnit3 p
  simp

end CompatibleOperators

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total
