import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleConnectingCycles

/-!
# The actual singular point class and its augmentation

The constant singular zero-simplex with coefficient one is an actual
degree-zero cycle. Its class has augmentation one, and actual singular
homology maps send it to the class of the image point. Consequently the
proved degree-zero markings of path-connected spaces commute with all
continuous maps between them.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual degree-zero singular cycle with coefficient one at a point. -/
def pointCycle (x : X) : Cycle (singularComplex X) 0 :=
  mkCycle (singularComplex X) 0 (simplexChain X 0 (ContinuousMap.const (Simplex 0) x))
    (by
      have h := (singularComplex X).shape 0 0 (by simp)
      exact congrArg
        (fun f => f.hom (simplexChain X 0 (ContinuousMap.const (Simplex 0) x))) h)

@[simp] theorem pointCycle_val (x : X) :
    (pointCycle x).1 = simplexChain X 0 (ContinuousMap.const (Simplex 0) x) := rfl

/-- The genuine singular degree-zero homology class of a point. -/
def pointClass (x : X) : SingularHomology X 0 :=
  cycleClass (singularComplex X) 0 (pointCycle x)

/-- The actual cycle map takes a point cycle to the cycle at its image. -/
@[simp] theorem mapCycles_pointCycle (f : C(X, Y)) (x : X) :
    mapCycles (singularChainMap f) 0 (pointCycle x) = pointCycle (f x) := by
  apply Subtype.ext
  rw [mapCycles_val, pointCycle_val, pointCycle_val]
  change inducedChain f 0 (simplexChain X 0 (ContinuousMap.const (Simplex 0) x)) = _
  rw [inducedChain_simplex]
  apply congrArg (simplexChain Y 0)
  apply ContinuousMap.ext
  intro t
  rfl

/-- Naturality of the actual integral point class. -/
@[simp] theorem singularHomologyMap_pointClass (f : C(X, Y)) (x : X) :
    singularHomologyMap f 0 (pointClass x) = pointClass (f x) := by
  change (HomologicalComplex.homologyMap (singularChainMap f) 0).hom
    (cycleClass (singularComplex X) 0 (pointCycle x)) = _
  rw [homologyMap_cycleClass, mapCycles_pointCycle]
  rfl

private def pointCycleLift (x : X) : ModuleCat.of ℤ ℤ ⟶ (singularComplex X).cycles 0 :=
  (singularComplex X).liftCycles
    ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) (simplexIndex X 0 (ContinuousMap.const (Simplex 0) x)))
    0 (by simp) (by simp)

private theorem pointClass_eq_pointCycleLift (x : X) :
    pointClass x = (singularComplex X).homologyπ 0 ((pointCycleLift x).hom 1) := by
  rw [pointClass, cycleClass_eq_homologyClassOfCycle, homologyClassOfCycle]
  apply congrArg ((singularComplex X).homologyπ 0).hom
  apply (ModuleCat.mono_iff_injective ((singularComplex X).iCycles 0)).mp inferInstance
  have h₁ := (singularComplex X).i_cyclesMk (pointCycle x).1 (0 - 1)
    (next_nat 0) (cycle_condition (singularComplex X) 0 (pointCycle x))
  have h₂ := congrArg (fun f => f.hom 1)
    ((singularComplex X).liftCycles_i
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) (simplexIndex X 0 (ContinuousMap.const (Simplex 0) x)))
      0 (by simp) (by simp))
  exact h₁.trans h₂.symm

/-- The actual augmentation sends the point class to one, in any space. -/
@[simp] theorem pointClass_augmentation (x : X) :
    ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom (pointClass x) = 1 := by
  rw [pointClass_eq_pointCycleLift]
  exact congrArg (fun f => f.hom 1)
    ((TopCat.toSSet.obj (TopCat.of X)).liftCycles_ιChainComplex_homologyπ_homology₀ε
      (ModuleCat.of ℤ ℤ) (simplexIndex X 0 (ContinuousMap.const (Simplex 0) x)))

/-- The connected degree-zero marking sends the actual point class to one. -/
@[simp] theorem connectedHomologyZeroEquiv_pointClass [PathConnectedSpace X] (x : X) :
    connectedHomologyZeroEquiv X (pointClass x) = 1 :=
  pointClass_augmentation x

/-- The inverse degree-zero marking sends one to the actual point class. -/
theorem connectedHomologyZeroEquiv_symm_one [PathConnectedSpace X] (x : X) :
    (connectedHomologyZeroEquiv X).symm 1 = pointClass x := by
  apply (connectedHomologyZeroEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, connectedHomologyZeroEquiv_pointClass]

/-- The actual point class generates degree-zero homology of a path-connected space. -/
theorem eq_zsmul_pointClass [PathConnectedSpace X] (x : X) (a : SingularHomology X 0) :
    a = connectedHomologyZeroEquiv X a • pointClass x := by
  apply (connectedHomologyZeroEquiv X).injective
  rw [map_zsmul, connectedHomologyZeroEquiv_pointClass, zsmul_eq_mul, mul_one]
  simp

/-- The actual map of any continuous map between path-connected spaces is
the identity in the proved augmentation markings. -/
theorem connectedHomologyZeroEquiv_natural [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (a : SingularHomology X 0) :
    connectedHomologyZeroEquiv Y (singularHomologyMap f 0 a) =
      connectedHomologyZeroEquiv X a := by
  let x : X := Classical.arbitrary X
  calc
    connectedHomologyZeroEquiv Y (singularHomologyMap f 0 a) =
        connectedHomologyZeroEquiv Y
          (singularHomologyMap f 0 (connectedHomologyZeroEquiv X a • pointClass x)) :=
      congrArg (fun b => connectedHomologyZeroEquiv Y (singularHomologyMap f 0 b))
        (eq_zsmul_pointClass x a)
    _ = connectedHomologyZeroEquiv X a := by
      rw [map_zsmul, map_zsmul, singularHomologyMap_pointClass,
        connectedHomologyZeroEquiv_pointClass, zsmul_eq_mul, mul_one]
      simp

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
