import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtCokernelBasic

/-!
# Equality of the two original cycle-cokernel comparisons

Both constructions use the same actual global kernel inclusion and
cokernel projection. Uniqueness at that kernel and cokernel proves their
comparison isomorphisms equal. Neither comparison is redefined.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution

open CuspNormalization.SheafCohomologyResolution
open ConstantSheafSingularComparison.LowExt

variable {X : TopCat.{0}} (R : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- Both original cycle identifications are the same map into the native cycles. -/
theorem globalTwoCyclesIso_inv_eq_mapped :
    R.globalTwoHomologyData.cyclesIso.inv =
      (CycleCokernel.mappedLeftHomologyData (globalSectionsFunctor X)
        R.twoComplex).cyclesIso.inv := by
  apply (cancel_mono R.globalTwoComplex.iCycles).mp
  exact R.globalTwoHomologyData.cyclesIso_inv_comp_iCycles.trans
    (CycleCokernel.mappedLeftHomologyData (globalSectionsFunctor X)
      R.twoComplex).cyclesIso_inv_comp_iCycles.symm

/-- The original partial-resolution cokernel comparison equals the original
preserved-kernel comparison, by their actual universal properties. -/
theorem globalTwoCokernelIso_eq_shortCokernelIsoHomology :
    R.globalTwoCokernelIso =
      CycleCokernel.shortCokernelIsoHomology (globalSectionsFunctor X) R.twoComplex := by
  apply Iso.ext
  apply (cancel_epi (cokernel.π R.toAugmented.globalComplex.g)).mp
  exact R.globalTwoCokernelIso_π.trans
    ((congrArg (fun f => f ≫ R.globalTwoComplex.homologyπ)
      R.globalTwoCyclesIso_inv_eq_mapped).trans
      (CycleCokernel.mappedLeftHomologyData (globalSectionsFunctor X)
        R.twoComplex).π_comp_homologyIso_inv.symm)

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution
