import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastAlgebraComplex
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastAlgebraCocycles
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsAbHomology

/-!
# The original row representatives under the actual total homology maps

The actual short-complex homology maps carry the original kernel and
projection representatives to the already defined literal total classes.
-/

noncomputable section

open CategoryTheory

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra

open SheafSingularCupComparison

/-- An actual additive short-complex map preserves the original kernel quotient class. -/
theorem abHomologyMap_class {S T : ShortComplex AddCommGrpCat.{u}} (f : S ⟶ T)
    (x : S.g.hom.ker) :
    T.abHomologyIso.hom
        (ShortComplex.homologyMap f (S.homologyπ (S.abCyclesIso.inv x))) =
      QuotientAddGroup.mk' T.abToCycles.range (TotalMaps.abCycleMap f x) := by
  have hx : S.abHomologyIso.hom (S.homologyπ (S.abCyclesIso.inv x)) =
      QuotientAddGroup.mk' S.abToCycles.range x :=
    ConcreteCategory.congr_hom (TotalHomology.abHomologyIso_class S) x
  calc
    _ = TotalMaps.abQuotientMap f
        (S.abHomologyIso.hom (S.homologyπ (S.abCyclesIso.inv x))) :=
      ConcreteCategory.congr_hom (TotalMaps.abQuotientMap_homology f)
        (S.homologyπ (S.abCyclesIso.inv x))
    _ = _ := by rw [hx, TotalMaps.abQuotientMap_class]

namespace Data

variable {A R0 R1 R2 R3 : Type u}
  [CommRing A] [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {D : Algebra.Data R0 R1 R2 R3} (F : Data A D)

/-- The original closed-pair homology representative maps to its literal total class. -/
theorem oneHomologyMap_class (x : A × A) (hx : F.rowD1 x = 0) :
    D.oneHomologyEquiv
        (ShortComplex.homologyMap F.oneComplexMap
          (F.rowOneComplex.homologyπ (F.rowOneComplex.abCyclesIso.inv ⟨x, hx⟩))) =
      F.oneClass x hx :=
  abHomologyMap_class F.oneComplexMap ⟨x, hx⟩

/-- The original top-coefficient homology representative maps to its literal total class. -/
theorem twoHomologyMap_class (x : A) :
    D.twoHomologyEquiv
        (ShortComplex.homologyMap F.twoComplexMap
          (F.rowTwoComplex.homologyπ
            (F.rowTwoComplex.abCyclesIso.inv ⟨x, F.rowD2_apply x⟩))) =
      F.twoClass x :=
  abHomologyMap_class F.twoComplexMap ⟨x, F.rowD2_apply x⟩

end Data

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra
