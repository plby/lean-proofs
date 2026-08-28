import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsComplex
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsAbHomology

/-!
# Actual first-column and last-row maps on cocycles and quotient classes

The maps descend the genuine short-complex maps through the original
kernel/range quotients. Their representative formulas retain the actual
first or last total component. They exist on every topological space.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization

variable (X : TopCat.{0})

def firstCocycleOne : (constantData X).CocycleOne →+ (TotalSheaf.globalData X).CocycleOne :=
  abCycleMap (globalFirstOneMap X)

def firstCocycleTwo : (constantData X).CocycleTwo →+ (TotalSheaf.globalData X).CocycleTwo :=
  abCycleMap (globalFirstTwoMap X)

def lastCocycleOne : (RingCochains.globalData X).CocycleOne →+
    (TotalSheaf.globalData X).CocycleOne :=
  abCycleMap (globalLastOneMap X)

def lastCocycleTwo : (RingCochains.globalData X).CocycleTwo →+
    (TotalSheaf.globalData X).CocycleTwo :=
  abCycleMap (globalLastTwoMap X)

theorem firstCocycleOne_val (a : (constantData X).CocycleOne) :
    (firstCocycleOne X a : (TotalSheaf.globalData X).One) = ((firstValues X).f1 a, 0) :=
  first1_global X a.val

theorem firstCocycleTwo_val (a : (constantData X).CocycleTwo) :
    (firstCocycleTwo X a : (TotalSheaf.globalData X).Two) = ((firstValues X).f2 a, 0, 0) :=
  first2_global X a.val

theorem lastCocycleOne_val (a : (RingCochains.globalData X).CocycleOne) :
    (lastCocycleOne X a : (TotalSheaf.globalData X).One) = (0, (lastValues X).f1 a) :=
  last1_global X a

theorem lastCocycleTwo_val (a : (RingCochains.globalData X).CocycleTwo) :
    (lastCocycleTwo X a : (TotalSheaf.globalData X).Two) = (0, 0, (lastValues X).f2 a) :=
  last2_global X a

/-- The original first Godement quotient maps to the actual first total quotient. -/
def firstH1 : (constantData X).CohomologyOne →+ (TotalSheaf.globalData X).CohomologyOne :=
  abQuotientMap (globalFirstOneMap X)

/-- The original second Godement quotient maps to the actual second total quotient. -/
def firstH2 : (constantData X).CohomologyTwo →+ (TotalSheaf.globalData X).CohomologyTwo :=
  abQuotientMap (globalFirstTwoMap X)

/-- The original first singular-row quotient maps to the actual first total quotient. -/
def lastH1 : (RingCochains.globalData X).CohomologyOne →+
    (TotalSheaf.globalData X).CohomologyOne :=
  abQuotientMap (globalLastOneMap X)

/-- The original second singular-row quotient maps to the actual second total quotient. -/
def lastH2 : (RingCochains.globalData X).CohomologyTwo →+
    (TotalSheaf.globalData X).CohomologyTwo :=
  abQuotientMap (globalLastTwoMap X)

@[simp] theorem firstH1_classOne (a : (constantData X).CocycleOne) :
    firstH1 X ((constantData X).classOne a) =
      (TotalSheaf.globalData X).classOne (firstCocycleOne X a) := rfl

@[simp] theorem firstH2_classTwo (a : (constantData X).CocycleTwo) :
    firstH2 X ((constantData X).classTwo a) =
      (TotalSheaf.globalData X).classTwo (firstCocycleTwo X a) := rfl

@[simp] theorem lastH1_classOne (a : (RingCochains.globalData X).CocycleOne) :
    lastH1 X ((RingCochains.globalData X).classOne a) =
      (TotalSheaf.globalData X).classOne (lastCocycleOne X a) := rfl

@[simp] theorem lastH2_classTwo (a : (RingCochains.globalData X).CocycleTwo) :
    lastH2 X ((RingCochains.globalData X).classTwo a) =
      (TotalSheaf.globalData X).classTwo (lastCocycleTwo X a) := rfl

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
