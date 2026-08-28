import Wikipedia.HopfProblem.SheafCupProductCofaceIdentities
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual cocycles, boundaries, and their quotient groups

These are the kernels and images of the proved alternating differential.
The Alexander–Whitney pairing lands in the actual degree-two kernel, and
the two incoming boundary products are actual degree-two boundaries.
No comparison with sheaf cohomology is asserted in this algebraic helper.
-/

universe u₀ u₁ u₂ u₃

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface.Data

variable {R0 : Type u₀} {R1 : Type u₁} {R2 : Type u₂} {R3 : Type u₃}
variable [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
variable (D : Coface.Data R0 R1 R2 R3)

abbrev CocycleOne : Type u₁ := D.d1.ker

abbrev CocycleTwo : Type u₂ := D.d2.ker

def boundaryOne : R0 →+ D.CocycleOne where
  toFun r := ⟨D.d0 r, D.d1_d0 r⟩
  map_zero' := Subtype.ext (map_zero D.d0)
  map_add' r s := Subtype.ext (map_add D.d0 r s)

def boundaryTwo : R1 →+ D.CocycleTwo where
  toFun a := ⟨D.d1 a, D.d2_d1 a⟩
  map_zero' := Subtype.ext (map_zero D.d1)
  map_add' a b := Subtype.ext (map_add D.d1 a b)

@[simp] theorem boundaryOne_coe (r : R0) : (D.boundaryOne r : R1) = D.d0 r := rfl

@[simp] theorem boundaryTwo_coe (a : R1) : (D.boundaryTwo a : R2) = D.d1 a := rfl

def boundariesOne : AddSubgroup D.CocycleOne := D.boundaryOne.range

def boundariesTwo : AddSubgroup D.CocycleTwo := D.boundaryTwo.range

abbrev CohomologyOne : Type u₁ := D.CocycleOne ⧸ D.boundariesOne

abbrev CohomologyTwo : Type u₂ := D.CocycleTwo ⧸ D.boundariesTwo

def classOne : D.CocycleOne →+ D.CohomologyOne := QuotientAddGroup.mk' D.boundariesOne

def classTwo : D.CocycleTwo →+ D.CohomologyTwo := QuotientAddGroup.mk' D.boundariesTwo

theorem classOne_surjective : Function.Surjective D.classOne :=
  QuotientAddGroup.mk'_surjective D.boundariesOne

theorem classTwo_surjective : Function.Surjective D.classTwo :=
  QuotientAddGroup.mk'_surjective D.boundariesTwo

@[simp] theorem classOne_boundary (r : R0) : D.classOne (D.boundaryOne r) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨r, rfl⟩

@[simp] theorem classTwo_boundary (a : R1) : D.classTwo (D.boundaryTwo a) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨a, rfl⟩

def cupCocycle (a b : D.CocycleOne) : D.CocycleTwo :=
  ⟨D.cupOne a b, D.cupOne_isCocycle a.property b.property⟩

@[simp] theorem cupCocycle_coe (a b : D.CocycleOne) :
    (D.cupCocycle a b : R2) = D.cupOne a b := rfl

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

theorem cupCocycles_boundary_left (r : R0) (b : D.CocycleOne) :
    D.cupCocycles (D.boundaryOne r) b = D.boundaryTwo (D.δ0 1 r * (b : R1)) :=
  Subtype.ext (D.cupOne_d0_left r b.property)

theorem cupCocycles_boundary_right (a : D.CocycleOne) (r : R0) :
    D.cupCocycles a (D.boundaryOne r) = D.boundaryTwo (-((a : R1) * D.δ0 0 r)) :=
  Subtype.ext (D.cupOne_d0_right a.property r)

end Wikipedia.HopfProblem.SheafCupProduct.Coface.Data
