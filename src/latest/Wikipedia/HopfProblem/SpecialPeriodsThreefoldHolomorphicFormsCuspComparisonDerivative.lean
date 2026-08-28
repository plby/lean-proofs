import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonBase

/-!
# The actual derivative of the logarithmic-to-regular comparison

In the existing source and target atlases, the comparison multiplies only
the base coordinate by the cusp width. Differentiating the exact chart
equation identifies its genuine manifold derivative with that linear map.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open HolomorphicDifferentialForms.Coordinates

local notation "EL" => ℂ × ComplexPlane₂
local notation "IL" => modelWithCornersSelf ℂ EL

attribute [local instance] RegularCover.coverChartedSpace RegularCover.cover_isManifold

/-- The literal width scaling, leaving both original fibre coordinates unchanged. -/
def baseWidthLinear : EL →L[ℂ] EL :=
  ((Triangle.width : ℂ) • ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).prod
    (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂)

@[simp] theorem baseWidthLinear_apply (v : EL) :
    baseWidthLinear v = ((Triangle.width : ℂ) * v.1, v.2) := rfl

/-- The exact equation between the unchanged native extended charts. -/
theorem toRegularCover_extChart_eq (x : LogDomain) :
    (extChartAt IL (toRegularCover x)) ∘ toRegularCover =
      baseWidthLinear ∘ extChartAt IL x := by
  funext y
  exact toRegularCover_chart_apply x y

/-- The genuine manifold derivative is the literal base-width linear map. -/
theorem toRegularCover_mfderiv (x : LogDomain) :
    (mfderiv IL IL toRegularCover x : EL →L[ℂ] EL) = baseWidthLinear := by
  have hf := toRegularCover_holomorphic.mdifferentiable (by simp) x
  have hs : MDifferentiableAt IL IL (extChartAt IL x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source EL x)
  have ht : MDifferentiableAt IL IL
      (extChartAt IL (toRegularCover x)) (toRegularCover x) :=
    mdifferentiableAt_extChartAt (mem_chart_source EL (toRegularCover x))
  have h := mfderiv_congr (I := IL) (I' := IL)
    (x := x) (toRegularCover_extChart_eq x)
  rw [mfderiv_comp x ht hf, mfderiv_comp x baseWidthLinear.mdifferentiableAt hs,
    mfderiv_extChartAt_self, mfderiv_extChartAt_self, ContinuousLinearMap.mfderiv_eq] at h
  ext v
  exact congrArg (fun L : EL →L[ℂ] EL => L v) h

/-- The derivative scales only the base component of each actual tangent vector. -/
theorem toRegularCover_mfderiv_apply (x : LogDomain) (v : EL) :
    mfderiv IL IL toRegularCover x v = ((Triangle.width : ℂ) * v.1, v.2) := by
  exact (congrArg (fun L : EL →L[ℂ] EL => L v) (toRegularCover_mfderiv x)).trans
    (baseWidthLinear_apply v)

@[simp] theorem baseWidthLinear_basis_zero :
    baseWidthLinear (basis 0) = (Triangle.width : ℂ) • basis 0 := by
  simp [basis, TrianglePeriodFamily.Canonical.basis,
    TrianglePeriodFamily.Canonical.coordinateEquiv_symm_apply, baseWidthLinear_apply]

@[simp] theorem baseWidthLinear_basis_one : baseWidthLinear (basis 1) = basis 1 := by
  simp [basis, TrianglePeriodFamily.Canonical.basis,
    TrianglePeriodFamily.Canonical.coordinateEquiv_symm_apply, baseWidthLinear_apply]

@[simp] theorem baseWidthLinear_basis_two : baseWidthLinear (basis 2) = basis 2 := by
  simp [basis, TrianglePeriodFamily.Canonical.basis,
    TrianglePeriodFamily.Canonical.coordinateEquiv_symm_apply, baseWidthLinear_apply]

@[simp] theorem baseWidthLinear_basis_succ (i : Fin 2) :
    baseWidthLinear (basis i.succ) = basis i.succ := by
  fin_cases i
  · exact baseWidthLinear_basis_one
  · exact baseWidthLinear_basis_two

theorem toRegularCover_mfderiv_basis_zero (x : LogDomain) :
    mfderiv IL IL toRegularCover x (basis 0) = (Triangle.width : ℂ) • basis 0 := by
  exact (congrArg (fun L : EL →L[ℂ] EL => L (basis 0)) (toRegularCover_mfderiv x)).trans
    baseWidthLinear_basis_zero

theorem toRegularCover_mfderiv_basis_one (x : LogDomain) :
    mfderiv IL IL toRegularCover x (basis 1) = basis 1 := by
  exact (congrArg (fun L : EL →L[ℂ] EL => L (basis 1)) (toRegularCover_mfderiv x)).trans
    baseWidthLinear_basis_one

theorem toRegularCover_mfderiv_basis_two (x : LogDomain) :
    mfderiv IL IL toRegularCover x (basis 2) = basis 2 := by
  exact (congrArg (fun L : EL →L[ℂ] EL => L (basis 2)) (toRegularCover_mfderiv x)).trans
    baseWidthLinear_basis_two

theorem toRegularCover_mfderiv_basis_succ (x : LogDomain) (i : Fin 2) :
    mfderiv IL IL toRegularCover x (basis i.succ) = basis i.succ := by
  exact (congrArg (fun L : EL →L[ℂ] EL => L (basis i.succ))
    (toRegularCover_mfderiv x)).trans (baseWidthLinear_basis_succ i)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
