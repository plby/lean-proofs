import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalHomologyQuotient

/-!
# Original cycle representatives under canonical total homology

The kernel inclusions and quotient projections retain their literal
representatives. These formulas concern the actual total complex and
the already defined total cohomology groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison

universe u

namespace TotalHomology

/-- Canonical additive homology preserves the original kernel quotient projection. -/
theorem abHomologyIso_class (S : ShortComplex AddCommGrpCat.{u}) :
    S.abCyclesIso.inv ≫ S.homologyπ ≫ S.abHomologyIso.hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' S.abToCycles.range) := by
  change S.abLeftHomologyData.cyclesIso.inv ≫ S.homologyπ ≫
    S.abLeftHomologyData.homologyIso.hom = S.abLeftHomologyData.π
  rw [S.abLeftHomologyData.homologyπ_comp_homologyIso_hom,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end TotalHomology

namespace TotalAlgebra.Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

/-- The first cycle comparison retains the original total cochain. -/
theorem oneCyclesIso_inv_iCycles (a : D.CocycleOne) :
    D.complexData.oneComplex.iCycles (D.oneCyclesIso.inv a) = a.val :=
  D.complexData.oneComplex.abCyclesIso_inv_apply_iCycles a

/-- The second cycle comparison retains the original total cochain. -/
theorem twoCyclesIso_inv_iCycles (a : D.CocycleTwo) :
    D.complexData.twoComplex.iCycles (D.twoCyclesIso.inv a) = a.val :=
  D.complexData.twoComplex.abCyclesIso_inv_apply_iCycles a

/-- The canonical first total homology comparison keeps the original quotient class. -/
theorem oneHomologyIso_class :
    D.oneCyclesIso.inv ≫ D.complexData.oneComplex.homologyπ ≫ D.oneHomologyIso.hom =
      AddCommGrpCat.ofHom D.classOne :=
  TotalHomology.abHomologyIso_class D.complexData.oneComplex

/-- The canonical second total homology comparison keeps the original quotient class. -/
theorem twoHomologyIso_class :
    D.twoCyclesIso.inv ≫ D.complexData.twoComplex.homologyπ ≫ D.twoHomologyIso.hom =
      AddCommGrpCat.ofHom D.classTwo :=
  TotalHomology.abHomologyIso_class D.complexData.twoComplex

/-- Pointwise first-class compatibility for the actual total representative. -/
theorem oneHomologyEquiv_class (a : D.CocycleOne) :
    D.oneHomologyEquiv (D.complexData.oneComplex.homologyπ (D.oneCyclesIso.inv a)) =
      D.classOne a :=
  ConcreteCategory.congr_hom D.oneHomologyIso_class a

/-- Pointwise second-class compatibility for the actual total representative. -/
theorem twoHomologyEquiv_class (a : D.CocycleTwo) :
    D.twoHomologyEquiv (D.complexData.twoComplex.homologyπ (D.twoCyclesIso.inv a)) =
      D.classTwo a :=
  ConcreteCategory.congr_hom D.twoHomologyIso_class a

/-- The inverse first comparison represents each original first quotient class. -/
theorem oneHomologyEquiv_symm_class (a : D.CocycleOne) :
    D.oneHomologyEquiv.symm (D.classOne a) =
      D.complexData.oneComplex.homologyπ (D.oneCyclesIso.inv a) := by
  apply D.oneHomologyEquiv.injective
  rw [D.oneHomologyEquiv.apply_symm_apply, D.oneHomologyEquiv_class]

/-- The inverse second comparison represents each original second quotient class. -/
theorem twoHomologyEquiv_symm_class (a : D.CocycleTwo) :
    D.twoHomologyEquiv.symm (D.classTwo a) =
      D.complexData.twoComplex.homologyπ (D.twoCyclesIso.inv a) := by
  apply D.twoHomologyEquiv.injective
  rw [D.twoHomologyEquiv.apply_symm_apply, D.twoHomologyEquiv_class]

end TotalAlgebra.Data

end Wikipedia.HopfProblem.SheafSingularCupComparison
