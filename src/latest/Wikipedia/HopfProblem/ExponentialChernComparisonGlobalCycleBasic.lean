import Wikipedia.HopfProblem.ExponentialChernComparisonGlobalCycleKernel
import Wikipedia.HopfProblem.ExponentialChernComparisonDLogResolution
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalComplex
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech

/-!
# Global sections of the original singular degree-two cycle sheaf

A closed singular two-cochain maps by the actual global sheafification
unit to a closed global cochain-sheaf section. Preservation of the original
degree-two kernel produces its literal global cycle section. The original
cokernel comparison keeps the class of that same unit image.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle

open ConstantSheafSingularComparison ConstantSheafSingularComparison.LowExt.CycleCokernel
open CuspNormalization.SheafCohomologyResolution HolomorphicFunctionSheaf.SphereH1
open SheafHigherDirectImage.ExtBridge

/-- The actual global cochain comparison preserves the literal
degree-two closedness equation. -/
theorem globalUnit_closed (X : TopCat.{0}) (ζ : Cochains X (AddCommGrpCat.of ℂ) 2)
    (hζ : (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 2 3 ζ = 0) :
    (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).d 2 3
        (globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ) = 0 := by
  rw [← globalCochainComparison_d_apply, hζ, map_zero]
  rfl

/-- The original closed cochain lifted into the actual global sections
of the original degree-two cycle kernel. -/
def sectionOfCochain (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)
    (ζ : Cochains X (AddCommGrpCat.of ℂ) 2)
    (hζ : (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 2 3 ζ = 0) :
    Section (DLog.resolution X hLC).complex.X₃ ⊤ :=
  preservedCycle (globalSectionsFunctor X)
    ((cochainSheafComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3)
    (globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ) (globalUnit_closed X ζ hζ)

/-- Including the actual kernel returns the original global unit image
of the given singular two-cochain. -/
theorem sectionOfCochain_inclusion (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)
    (ζ : Cochains X (AddCommGrpCat.of ℂ) 2)
    (hζ : (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 2 3 ζ = 0) :
    (kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.app (op ⊤)
        (sectionOfCochain X hLC ζ hζ) = globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ :=
  preservedCycle_inclusion (globalSectionsFunctor X)
    ((cochainSheafComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3)
    (globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ) (globalUnit_closed X ζ hζ)

/-- Before the full-complex window comparison, the original cokernel
projection is the ordinary short-complex class of the literal unit image. -/
theorem sectionOfCochain_shortClass (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)
    (ζ : Cochains X (AddCommGrpCat.of ℂ) 2)
    (hζ : (singularCochainComplex X (AddCommGrpCat.of ℂ)).d 2 3 ζ = 0) :
    (shortCokernelIsoHomology (globalSectionsFunctor X)
        ((cochainSheafComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3)).hom
      (cokernel.π (DLog.resolution X hLC).globalComplex.g
        (sectionOfCochain X hLC ζ hζ)) =
      shortCycleClass ((globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3)
        (globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ) (globalUnit_closed X ζ hζ) :=
  preservedCycle_class (globalSectionsFunctor X)
    ((cochainSheafComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3)
    (globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ) (globalUnit_closed X ζ hζ)

end Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle
