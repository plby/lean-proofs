import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraHomologyQuotient
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalHomologyRepresentatives

/-!
# Original cocycles under the canonical total homology comparison

The cycle inclusions and homology projections preserve the literal
cochain and its already defined quotient class in both degrees.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

universe u

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

/-- The first native cycle inclusion retains the original total cochain. -/
theorem oneCyclesIso_inv_iCycles (a : D.CocycleOne) :
    D.complexData.oneComplex.iCycles (D.oneCyclesIso.inv a) = a.val :=
  D.complexData.oneComplex.abCyclesIso_inv_apply_iCycles a

/-- The second native cycle inclusion retains the original total cochain. -/
theorem twoCyclesIso_inv_iCycles (a : D.CocycleTwo) :
    D.complexData.twoComplex.iCycles (D.twoCyclesIso.inv a) = a.val :=
  D.complexData.twoComplex.abCyclesIso_inv_apply_iCycles a

/-- The first native homology projection is the original quotient-class map. -/
theorem oneHomologyIso_class :
    D.oneCyclesIso.inv ≫ D.complexData.oneComplex.homologyπ ≫ D.oneHomologyIso.hom =
      AddCommGrpCat.ofHom D.classOne :=
  SheafSingularCupComparison.TotalHomology.abHomologyIso_class D.complexData.oneComplex

/-- The second native homology projection is the original quotient-class map. -/
theorem twoHomologyIso_class :
    D.twoCyclesIso.inv ≫ D.complexData.twoComplex.homologyπ ≫ D.twoHomologyIso.hom =
      AddCommGrpCat.ofHom D.classTwo :=
  SheafSingularCupComparison.TotalHomology.abHomologyIso_class D.complexData.twoComplex

/-- The first additive comparison preserves every original cocycle class. -/
theorem oneHomologyEquiv_class (a : D.CocycleOne) :
    D.oneHomologyEquiv (D.complexData.oneComplex.homologyπ (D.oneCyclesIso.inv a)) =
      D.classOne a :=
  ConcreteCategory.congr_hom D.oneHomologyIso_class a

/-- The second additive comparison preserves every original cocycle class. -/
theorem twoHomologyEquiv_class (a : D.CocycleTwo) :
    D.twoHomologyEquiv (D.complexData.twoComplex.homologyπ (D.twoCyclesIso.inv a)) =
      D.classTwo a :=
  ConcreteCategory.congr_hom D.twoHomologyIso_class a

/-- The inverse first comparison gives the original native homology representative. -/
theorem oneHomologyEquiv_symm_class (a : D.CocycleOne) :
    D.oneHomologyEquiv.symm (D.classOne a) =
      D.complexData.oneComplex.homologyπ (D.oneCyclesIso.inv a) := by
  apply D.oneHomologyEquiv.injective
  rw [D.oneHomologyEquiv.apply_symm_apply, D.oneHomologyEquiv_class]

/-- The inverse second comparison gives the original native homology representative. -/
theorem twoHomologyEquiv_symm_class (a : D.CocycleTwo) :
    D.twoHomologyEquiv.symm (D.classTwo a) =
      D.complexData.twoComplex.homologyπ (D.twoCyclesIso.inv a) := by
  apply D.twoHomologyEquiv.injective
  rw [D.twoHomologyEquiv.apply_symm_apply, D.twoHomologyEquiv_class]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data
