import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalHomologyBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraQuotient

/-!
# Native total homology and the original total cocycle quotients

The comparisons are Mathlib's canonical kernel-and-quotient homology
isomorphisms. The original total algebra's cocycles, boundary subgroups,
and quotient groups are unchanged.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data

universe u

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

@[simp] theorem oneComplex_abToCycles :
    D.complexData.oneComplex.abToCycles = D.boundaryOne := rfl

@[simp] theorem twoComplex_abToCycles :
    D.complexData.twoComplex.abToCycles = D.boundaryTwo := rfl

/-- Canonical first total cycles are the original first total kernel. -/
def oneCyclesIso : D.complexData.oneComplex.cycles ≅ AddCommGrpCat.of D.CocycleOne :=
  D.complexData.oneComplex.abCyclesIso

/-- Canonical second total cycles are the original second total kernel. -/
def twoCyclesIso : D.complexData.twoComplex.cycles ≅ AddCommGrpCat.of D.CocycleTwo :=
  D.complexData.twoComplex.abCyclesIso

/-- Canonical first total homology is the original first total quotient. -/
def oneHomologyIso :
    D.complexData.oneComplex.homology ≅ AddCommGrpCat.of D.CohomologyOne :=
  D.complexData.oneComplex.abHomologyIso

/-- Canonical second total homology is the original second total quotient. -/
def twoHomologyIso :
    D.complexData.twoComplex.homology ≅ AddCommGrpCat.of D.CohomologyTwo :=
  D.complexData.twoComplex.abHomologyIso

/-- The first canonical total homology comparison as an additive equivalence. -/
def oneHomologyEquiv : D.complexData.oneComplex.homology ≃+ D.CohomologyOne :=
  D.oneHomologyIso.addCommGroupIsoToAddEquiv

/-- The second canonical total homology comparison as an additive equivalence. -/
def twoHomologyEquiv : D.complexData.twoComplex.homology ≃+ D.CohomologyTwo :=
  D.twoHomologyIso.addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data
