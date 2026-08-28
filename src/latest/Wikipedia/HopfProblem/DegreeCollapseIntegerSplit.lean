import Wikipedia.NoExoticSixSphere.IntegralSplitting

/-!
# The original exact integral splitting interface

Retain the original inclusion, coordinate, marked sum map and product
equivalence. The existing general integral-splitting implementation proves
these statements with the same native integer actions and literal summand
maps. Primitive-coordinate complement calculations live separately in
`DegreeCollapsePrimitiveIntegerCoordinate`.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSplitting

variable {H W : Type*} [AddCommGroup H] [Module ℤ H]
  [AddCommGroup W] [Module ℤ W] (j : H →ₗ[ℤ] W) (c : W →ₗ[ℤ] ℤ)

def sumMap (w : W) : H × ℤ →ₗ[ℤ] W := NoExoticSixSphere.IntegralSplitting.sumMap j w

theorem sumMap_apply (w : W) (x : H × ℤ) : sumMap j w x = j x.1 + x.2 • w := rfl

variable (hj : Injective j) (he : LinearMap.range j = LinearMap.ker c)

include he in
theorem coordinate_inclusion (x : H) : c (j x) = 0 :=
  NoExoticSixSphere.IntegralSplitting.coordinate_inclusion j c he x

include he in
theorem coordinate_sumMap (w : W) (hw : c w = 1) (x : H × ℤ) :
    c (sumMap j w x) = x.2 :=
  NoExoticSixSphere.IntegralSplitting.sumMap_coordinate j c he w hw x

include hj he in
theorem sumMap_bijective (w : W) (hw : c w = 1) : Bijective (sumMap j w) :=
  NoExoticSixSphere.IntegralSplitting.sumMap_bijective j c hj he w hw

variable (hc : Surjective c)

def splitEquiv : W ≃ₗ[ℤ] H × ℤ :=
  (LinearEquiv.ofBijective (sumMap j (hc 1).choose)
    (sumMap_bijective j c hj he (hc 1).choose (hc 1).choose_spec)).symm

theorem splitEquiv_symm_inl (x : H) : (splitEquiv j c hj he hc).symm (x, 0) = j x := by
  change j x + (0 : ℤ) • (hc 1).choose = j x
  rw [zero_zsmul, add_zero]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSplitting
