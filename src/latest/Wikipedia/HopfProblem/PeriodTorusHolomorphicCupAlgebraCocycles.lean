import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraBoundaries
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual kernels, ranges, and the total cocycle pairing
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

abbrev CocycleOne : Type u := D.d1.ker
abbrev CocycleTwo : Type u := D.d2.ker

def boundaryOne : R0 →+ D.CocycleOne where
  toFun u := ⟨D.d0 u, D.d1_d0 u⟩
  map_zero' := Subtype.ext (map_zero D.d0)
  map_add' u v := Subtype.ext (map_add D.d0 u v)

def boundaryTwo : D.One →+ D.CocycleTwo where
  toFun x := ⟨D.d1 x, D.d2_d1 x⟩
  map_zero' := Subtype.ext (map_zero D.d1)
  map_add' x y := Subtype.ext (map_add D.d1 x y)

@[simp] theorem boundaryOne_coe (u : R0) : (D.boundaryOne u : D.One) = D.d0 u := rfl
@[simp] theorem boundaryTwo_coe (x : D.One) : (D.boundaryTwo x : D.Two) = D.d1 x := rfl

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

@[simp] theorem classOne_boundary (u : R0) : D.classOne (D.boundaryOne u) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨u, rfl⟩

@[simp] theorem classTwo_boundary (x : D.One) : D.classTwo (D.boundaryTwo x) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨x, rfl⟩

def cupCocycle (x y : D.CocycleOne) : D.CocycleTwo :=
  ⟨D.cupOne x y, D.cupOne_isCocycle x.property y.property⟩

@[simp] theorem cupCocycle_coe (x y : D.CocycleOne) :
    (D.cupCocycle x y : D.Two) = D.cupOne x y := rfl

def cupCocycles : D.CocycleOne →+ D.CocycleOne →+ D.CocycleTwo where
  toFun x :=
    { toFun := D.cupCocycle x
      map_zero' := Subtype.ext (D.cupOne_zero_right x)
      map_add' y z := Subtype.ext (D.cupOne_add_right x y z) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact Subtype.ext (D.cupOne_zero_left y)
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    exact Subtype.ext (D.cupOne_add_left x y z)

@[simp] theorem cupCocycles_apply (x y : D.CocycleOne) :
    D.cupCocycles x y = D.cupCocycle x y := rfl

theorem cupCocycles_boundary_left (u : R0) (y : D.CocycleOne) :
    D.cupCocycles (D.boundaryOne u) y = D.boundaryTwo (D.leftPrimitive u y) :=
  Subtype.ext (D.cupOne_d0_left u y.property)

theorem cupCocycles_boundary_right (x : D.CocycleOne) (u : R0) :
    D.cupCocycles x (D.boundaryOne u) = D.boundaryTwo (D.rightPrimitive x u) :=
  Subtype.ext (D.cupOne_d0_right x.property u)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data
