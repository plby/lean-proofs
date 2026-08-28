import Wikipedia.HopfProblem.ExponentialChernComparisonGlobalCycleBasic
import Wikipedia.HopfProblem.ExponentialChernComparisonGlobalCycleWindow

/-!
# The original global singular cycle in the actual resolution comparison

The global section of the genuine degree-two cycle sheaf represents the
class induced by the original global singular-cochain comparison. The
proof uses the actual preserved-kernel cokernel comparison and the actual
full-complex window isomorphism, both retaining the literal representative.
No cohomology-class equality or sign convention is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle

open ConstantSheafSingularComparison ConstantSheafSingularComparison.LowExt.CycleCokernel
open CuspNormalization.SheafCohomologyResolution SheafHigherDirectImage.ExtBridge

/-- The canonical degree-two resolution comparison sends the original
global cycle-kernel section to the homology map of the same actual closed
singular two-cochain. Compactness is not needed for this representative formula. -/
theorem sectionOfCochain_class (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)
    (ζ : Cochains X (AddCommGrpCat.of ℂ) 2)
    (hζ : (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 2 3 ζ = 0) :
    (singularSheafResolution X (AddCommGrpCat.of ℂ) hLC).globalSecondHomologyIso.hom
        (cokernel.π (DLog.resolution X hLC).globalComplex.g
          (sectionOfCochain X hLC ζ hζ)) =
      HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2
        (cycleClass (singularCochainComplex X (AddCommGrpCat.of ℂ)) 2 ζ
          (closed_sc (singularCochainComplex X (AddCommGrpCat.of ℂ)) ζ hζ)) := by
  let K := globalSheafCochainComplex X (AddCommGrpCat.of ℂ)
  let z := globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ
  have hz : K.d 2 3 z = 0 := globalUnit_closed X ζ hζ
  calc
    _ = (windowHomologyIso₂ K).inv
        ((shortCokernelIsoHomology (globalSectionsFunctor X)
          ((cochainSheafComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3)).hom
          (cokernel.π (DLog.resolution X hLC).globalComplex.g
            (sectionOfCochain X hLC ζ hζ))) := rfl
    _ = (windowHomologyIso₂ K).inv (shortCycleClass (K.sc' 1 2 3) z hz) :=
      congrArg (windowHomologyIso₂ K).inv (sectionOfCochain_shortClass X hLC ζ hζ)
    _ = cycleClass K 2 z (closed_sc K z hz) :=
      windowHomologyIso₂_inv_shortCycleClass K z hz
    _ = _ := (homologyMap_cycleClass (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2 ζ
      (closed_sc (singularCochainComplex X (AddCommGrpCat.of ℂ)) ζ hζ)
      (closed_sc K z hz)).symm

end Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle
