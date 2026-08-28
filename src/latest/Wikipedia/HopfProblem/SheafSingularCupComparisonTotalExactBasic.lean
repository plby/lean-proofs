import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalComplex

/-!
# Actual augmented columns of the low-degree total complex

The groups `S0` through `S3` augment the original vertical columns.
Their differentials commute with the original augmentations. Exactness
and injectivity are statements about these actual maps; they will be
proved from the Godement columns on actual stalks.
-/

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex

universe u

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [AddCommGroup R00] [AddCommGroup R10] [AddCommGroup R01]
  [AddCommGroup R20] [AddCommGroup R11] [AddCommGroup R02]
  [AddCommGroup R30] [AddCommGroup R21] [AddCommGroup R12] [AddCommGroup R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)
  (S0 S1 S2 S3 : Type u) [AddCommGroup S0] [AddCommGroup S1]
  [AddCommGroup S2] [AddCommGroup S3]

/-- Original exact vertical columns, with the original commuting horizontal row. -/
structure AugmentedColumns where
  i0 : S0 →+ R00
  i1 : S1 →+ R01
  i2 : S2 →+ R02
  i3 : S3 →+ R03
  d0 : S0 →+ S1
  d1 : S1 →+ S2
  d2 : S2 →+ S3
  comm0 : D.h00.comp i0 = i1.comp d0
  comm1 : D.h01.comp i1 = i2.comp d1
  comm2 : D.h02.comp i2 = i3.comp d2
  column00 : Function.Exact i0 D.v00
  column01 : Function.Exact i1 D.v01
  column02 : Function.Exact i2 D.v02
  column10 : Function.Exact D.v00 D.v10
  column20 : Function.Exact D.v10 D.v20
  column11 : Function.Exact D.v01 D.v11
  injective0 : Function.Injective i0
  injective1 : Function.Injective i1
  injective2 : Function.Injective i2
  injective3 : Function.Injective i3

namespace AugmentedColumns

variable {D S0 S1 S2 S3} (A : AugmentedColumns D S0 S1 S2 S3)

@[simp] theorem h00_i0 (x : S0) : D.h00 (A.i0 x) = A.i1 (A.d0 x) :=
  DFunLike.congr_fun A.comm0 x
@[simp] theorem h01_i1 (x : S1) : D.h01 (A.i1 x) = A.i2 (A.d1 x) :=
  DFunLike.congr_fun A.comm1 x
@[simp] theorem h02_i2 (x : S2) : D.h02 (A.i2 x) = A.i3 (A.d2 x) :=
  DFunLike.congr_fun A.comm2 x

@[simp] theorem v00_i0 (x : S0) : D.v00 (A.i0 x) = 0 :=
  A.column00.apply_apply_eq_zero x
@[simp] theorem v01_i1 (x : S1) : D.v01 (A.i1 x) = 0 :=
  A.column01.apply_apply_eq_zero x
@[simp] theorem v02_i2 (x : S2) : D.v02 (A.i2 x) = 0 :=
  A.column02.apply_apply_eq_zero x

end AugmentedColumns

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex
