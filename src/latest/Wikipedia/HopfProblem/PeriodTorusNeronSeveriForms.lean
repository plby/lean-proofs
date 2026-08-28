import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingRealForms

/-!
# The integral type `(1,1)` subgroup in actual singular cohomology

This file records the subgroup cut out by the actual complex-structure
condition on the period form of a native cohomology class.  The later
Chern-image theorem identifies it with the image of original native line
bundles; that identification is not part of this definition.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open SingularCohomologyFree PeriodTorusCohomology PeriodTorusTypeOneOne
open SpecialPeriods UpperHalfPlane

/-- Native integral classes whose actual real tangent forms are invariant under `I`. -/
def integralTypeOneOneSubgroup (p : PeriodDomain) :
    AddSubgroup (SingularCohomology p.Torus 2) where
  carrier := {a | IsTypeOneOne (cohomologyRealForm p a)}
  zero_mem' := by
    change IsTypeOneOne (cohomologyRealForm p 0)
    rw [cohomologyRealForm_zero]
    intro x y
    rfl
  add_mem' := by
    intro a b ha hb
    change IsTypeOneOne (cohomologyRealForm p (a + b))
    rw [cohomologyRealForm_add]
    intro x y
    simp only [LinearMap.add_apply, ha x y, hb x y]
  neg_mem' := by
    intro a ha
    change IsTypeOneOne (cohomologyRealForm p (-a))
    have hneg : cohomologyRealForm p (-a) = -cohomologyRealForm p a := by
      simpa only [neg_one_zsmul, Int.cast_neg, Int.cast_one, neg_one_smul] using
        cohomologyRealForm_zsmul p (-1) a
    rw [hneg]
    intro x y
    simp only [LinearMap.neg_apply, ha x y]

@[simp] theorem mem_integralTypeOneOneSubgroup (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    a ∈ integralTypeOneOneSubgroup p ↔ IsTypeOneOne (cohomologyRealForm p a) := Iff.rfl

/-- The distinguished class belongs to the intrinsic type subgroup on every period torus. -/
theorem etaClass_mem_integralTypeOneOneSubgroup (p : PeriodDomain) :
    etaClass p ∈ integralTypeOneOneSubgroup p := by
  rw [mem_integralTypeOneOneSubgroup, cohomologyRealForm_etaClass]
  exact etaTangent_isTypeOneOne p

/-- The previously proved countable exception set controls this actual subgroup. -/
theorem integralTypeOneOneSubgroup_eq_zmultiples_eta (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) :
    integralTypeOneOneSubgroup (specialPeriodMap.point z) =
      AddSubgroup.zmultiples (etaClass (specialPeriodMap.point z)) := by
  ext a
  rw [mem_integralTypeOneOneSubgroup,
    cohomologyRealForm_typeOneOne_iff_of_not_exceptional z hz,
    AddSubgroup.mem_zmultiples_iff]
  exact exists_congr fun _ => eq_comm

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
