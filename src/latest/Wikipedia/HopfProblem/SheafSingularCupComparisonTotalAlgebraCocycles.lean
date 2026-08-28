import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraBoundaries
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual total cocycles, boundaries, and the cocycle cup pairing

The groups are literal kernels of the shared total differential, and
the boundary subgroups are its literal ranges in those kernels. The
proved Leibniz identity and explicit boundary primitives supply the
pairing and its boundary identities without any comparison assumption.
-/

universe u

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

abbrev CocycleOne : Type u := D.d1.ker
abbrev CocycleTwo : Type u := D.d2.ker

def boundaryOne : R00 →+ D.CocycleOne where
  toFun r := ⟨D.d0 r, D.d1_d0 r⟩
  map_zero' := Subtype.ext (map_zero D.d0)
  map_add' r s := Subtype.ext (map_add D.d0 r s)

def boundaryTwo : D.One →+ D.CocycleTwo where
  toFun a := ⟨D.d1 a, D.d2_d1 a⟩
  map_zero' := Subtype.ext (map_zero D.d1)
  map_add' a b := Subtype.ext (map_add D.d1 a b)

@[simp] theorem boundaryOne_coe (r : R00) : (D.boundaryOne r : D.One) = D.d0 r := rfl
@[simp] theorem boundaryTwo_coe (a : D.One) : (D.boundaryTwo a : D.Two) = D.d1 a := rfl

def boundariesOne : AddSubgroup D.CocycleOne := D.boundaryOne.range
def boundariesTwo : AddSubgroup D.CocycleTwo := D.boundaryTwo.range

abbrev CohomologyOne : Type u := D.CocycleOne ⧸ D.boundariesOne
abbrev CohomologyTwo : Type u := D.CocycleTwo ⧸ D.boundariesTwo

def classOne : D.CocycleOne →+ D.CohomologyOne := QuotientAddGroup.mk' D.boundariesOne
def classTwo : D.CocycleTwo →+ D.CohomologyTwo := QuotientAddGroup.mk' D.boundariesTwo

theorem classOne_surjective : Function.Surjective D.classOne :=
  QuotientAddGroup.mk'_surjective D.boundariesOne

theorem classTwo_surjective : Function.Surjective D.classTwo :=
  QuotientAddGroup.mk'_surjective D.boundariesTwo

@[simp] theorem classOne_boundary (r : R00) : D.classOne (D.boundaryOne r) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨r, rfl⟩

@[simp] theorem classTwo_boundary (a : D.One) : D.classTwo (D.boundaryTwo a) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨a, rfl⟩

def cupCocycle (a b : D.CocycleOne) : D.CocycleTwo :=
  ⟨D.cupOne a b, D.cupOne_isCocycle a.property b.property⟩

@[simp] theorem cupCocycle_coe (a b : D.CocycleOne) :
    (D.cupCocycle a b : D.Two) = D.cupOne a b := rfl

def cupCocycles : D.CocycleOne →+ D.CocycleOne →+ D.CocycleTwo where
  toFun a :=
    { toFun := D.cupCocycle a
      map_zero' := Subtype.ext (D.cupOne_zero_right a)
      map_add' b c := Subtype.ext (D.cupOne_add_right a b c) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    exact Subtype.ext (D.cupOne_zero_left b)
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    exact Subtype.ext (D.cupOne_add_left a b c)

@[simp] theorem cupCocycles_apply (a b : D.CocycleOne) :
    D.cupCocycles a b = D.cupCocycle a b := rfl

theorem cupCocycles_boundary_left (r : R00) (b : D.CocycleOne) :
    D.cupCocycles (D.boundaryOne r) b = D.boundaryTwo (D.leftPrimitive r b) :=
  Subtype.ext (D.cupOne_d0_left r b.property)

theorem cupCocycles_boundary_right (a : D.CocycleOne) (r : R00) :
    D.cupCocycles a (D.boundaryOne r) = D.boundaryTwo (D.rightPrimitive a r) :=
  Subtype.ext (D.cupOne_d0_right a.property r)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data
