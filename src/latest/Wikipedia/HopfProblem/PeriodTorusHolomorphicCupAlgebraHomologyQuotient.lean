import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebra
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalHomologyBasic

/-!
# Canonical homology of the Godement–Dolbeault total algebra

Mathlib's additive short-complex homology is canonically the original
kernel/range quotient. The total differentials, cocycles, and boundary
subgroups are those already defined in the signed total algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

universe u

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

@[simp] theorem oneComplex_abToCycles :
    D.complexData.oneComplex.abToCycles = D.boundaryOne := rfl

@[simp] theorem twoComplex_abToCycles :
    D.complexData.twoComplex.abToCycles = D.boundaryTwo := rfl

/-- The first native cycle object is the original first total kernel. -/
def oneCyclesIso : D.complexData.oneComplex.cycles ≅ AddCommGrpCat.of D.CocycleOne :=
  D.complexData.oneComplex.abCyclesIso

/-- The second native cycle object is the original second total kernel. -/
def twoCyclesIso : D.complexData.twoComplex.cycles ≅ AddCommGrpCat.of D.CocycleTwo :=
  D.complexData.twoComplex.abCyclesIso

/-- First native total homology is the original first kernel/range quotient. -/
def oneHomologyIso :
    D.complexData.oneComplex.homology ≅ AddCommGrpCat.of D.CohomologyOne :=
  D.complexData.oneComplex.abHomologyIso

/-- Second native total homology is the original second kernel/range quotient. -/
def twoHomologyIso :
    D.complexData.twoComplex.homology ≅ AddCommGrpCat.of D.CohomologyTwo :=
  D.complexData.twoComplex.abHomologyIso

/-- The first canonical comparison, as an additive equivalence. -/
def oneHomologyEquiv : D.complexData.oneComplex.homology ≃+ D.CohomologyOne :=
  D.oneHomologyIso.addCommGroupIsoToAddEquiv

/-- The second canonical comparison, as an additive equivalence. -/
def twoHomologyEquiv : D.complexData.twoComplex.homology ≃+ D.CohomologyTwo :=
  D.twoHomologyIso.addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data
