import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsResolution
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsSections
import Wikipedia.HopfProblem.SheafCupProductResolutionGlobalMaps

/-!
# The original short-complex maps and their actual global component maps

The short-complex maps exist on every space. Local contractibility is
needed only to view the same maps as maps of the proved resolutions.
The global maps then use the original global-sections functor and the
canonical total biproduct comparison.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization
open SheafCohomologyResolution

variable (X : TopCat.{0})

def firstOneSheafMap : GodementExact.complex1 (SheafConstants.complexSheaf X) ⟶
    TotalSheaf.oneComplex X where
  τ₁ := first0 X
  τ₂ := first1 X
  τ₃ := first2 X
  comm₁₂ := first_comm0 X
  comm₂₃ := first_comm1 X

def firstTwoSheafMap : GodementExact.complex2 (SheafConstants.complexSheaf X) ⟶
    TotalSheaf.twoComplex X where
  τ₁ := first1 X
  τ₂ := first2 X
  τ₃ := first3 X
  comm₁₂ := first_comm1 X
  comm₂₃ := first_comm2 X

def lastOneSheafMap : ResolutionRow.rowOneComplex X ⟶ TotalSheaf.oneComplex X where
  τ₁ := last0 X
  τ₂ := last1 X
  τ₃ := last2 X
  comm₁₂ := last_comm0 X
  comm₂₃ := last_comm1 X

def lastTwoSheafMap : ResolutionRow.rowTwoComplex X ⟶ TotalSheaf.twoComplex X where
  τ₁ := last1 X
  τ₂ := last2 X
  τ₃ := last3 X
  comm₁₂ := last_comm1 X
  comm₂₃ := last_comm2 X

abbrev firstToTotal (hLC : LocallyContractibleSpace X) := first X hLC
abbrev lastToTotal (hLC : LocallyContractibleSpace X) := last X hLC

theorem firstToTotal_globalOneMap (hLC : LocallyContractibleSpace X) :
    (firstToTotal X hLC).globalOneMap =
      (globalSectionsFunctor X).mapShortComplex.map (firstOneSheafMap X) := rfl

theorem firstToTotal_globalTwoMap (hLC : LocallyContractibleSpace X) :
    (firstToTotal X hLC).globalTwoMap =
      (globalSectionsFunctor X).mapShortComplex.map (firstTwoSheafMap X) := rfl

theorem lastToTotal_globalOneMap (hLC : LocallyContractibleSpace X) :
    (lastToTotal X hLC).globalOneMap =
      (globalSectionsFunctor X).mapShortComplex.map (lastOneSheafMap X) := rfl

theorem lastToTotal_globalTwoMap (hLC : LocallyContractibleSpace X) :
    (lastToTotal X hLC).globalTwoMap =
      (globalSectionsFunctor X).mapShortComplex.map (lastTwoSheafMap X) := rfl

def globalFirstOneMap : SheafCupProductResolution.Coface.oneComplex (constantData X) ⟶
    (TotalSheaf.globalData X).complexData.oneComplex :=
  (globalSectionsFunctor X).mapShortComplex.map (firstOneSheafMap X) ≫
    (TotalSheaf.globalOneIso X).hom

def globalFirstTwoMap : SheafCupProductResolution.Coface.twoComplex (constantData X) ⟶
    (TotalSheaf.globalData X).complexData.twoComplex :=
  (globalSectionsFunctor X).mapShortComplex.map (firstTwoSheafMap X) ≫
    (TotalSheaf.globalTwoIso X).hom

def globalLastOneMap : SheafCupProductResolution.Coface.oneComplex (RingCochains.globalData X) ⟶
    (TotalSheaf.globalData X).complexData.oneComplex :=
  (globalSectionsFunctor X).mapShortComplex.map (lastOneSheafMap X) ≫
    (TotalSheaf.globalOneIso X).hom

def globalLastTwoMap : SheafCupProductResolution.Coface.twoComplex (RingCochains.globalData X) ⟶
    (TotalSheaf.globalData X).complexData.twoComplex :=
  (globalSectionsFunctor X).mapShortComplex.map (lastTwoSheafMap X) ≫
    (TotalSheaf.globalTwoIso X).hom

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
