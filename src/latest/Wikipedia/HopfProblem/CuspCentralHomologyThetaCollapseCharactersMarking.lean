import Wikipedia.HopfProblem.CuspCentralHomologyEdgeCharacters
import Wikipedia.HopfProblem.CuspCentralHomologyPhaseTori
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionCircles
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleNormalization
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsCoordinateBasis
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusProductDecomposition
import Mathlib.Data.Fin.Rev

/-!
# The ordered actual first-homology marking of the compact phase torus

The two Pascal-indexed degree-one torus classes are identified with their
literal positive coordinate loops. Reordering those two entries gives the
actual coordinate marking, with the zeroth phase before the first phase.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology ToricSpace

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual-coordinate index corresponding to the reversed Pascal order. -/
def compactPhaseH1IndexEquiv : Fin 2 ≃ Fin (Nat.choose 2 1) :=
  Fin.revPerm.trans (finCongr (by decide))

/-- The explicit conversion from the two Pascal entries to ambient-coordinate order. -/
def compactPhaseH1OrderEquiv : binomialModule 2 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ({ toFun v i := v (compactPhaseH1IndexEquiv i)
     invFun v i := v (compactPhaseH1IndexEquiv.symm i)
     left_inv v := by ext i; exact congrArg v (compactPhaseH1IndexEquiv.apply_symm_apply i)
     right_inv v := by ext i; exact congrArg v (compactPhaseH1IndexEquiv.symm_apply_apply i)
     map_add' _ _ := rfl } : binomialModule 2 1 ≃+ (Fin 2 → ℤ)).toIntLinearEquiv

@[simp] theorem compactPhaseH1OrderEquiv_apply (v : binomialModule 2 1) (i : Fin 2) :
    compactPhaseH1OrderEquiv v i = v (compactPhaseH1IndexEquiv i) := rfl

/-- The actual first integral singular homology of the compact phases,
in their ordered coordinates. -/
def compactPhaseH1Equiv : SingularHomology CompactFibreTorus 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((homeomorphHomologyEquiv compactFibreTorusHomeomorph 1).trans
    (productTorusHomologyEquiv 2 1)).trans compactPhaseH1OrderEquiv

/-- The circle with the displayed integral phase vector, as an actual continuous map. -/
def compactPhaseCircleMap (v : Fin 2 → ℤ) : C(_root_.Circle, CompactFibreTorus) :=
  ⟨edgeCompactPhase v, edgeCompactPhase_continuous v⟩

@[simp] theorem compactPhaseCircleMap_apply (v : Fin 2 → ℤ) (z : _root_.Circle) (i : Fin 2) :
    compactPhaseCircleMap v z i = z ^ v i := rfl

theorem compactPhaseCircleMap_coordinates (v : Fin 2 → ℤ) :
    (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2)).comp
      ((compactPhaseCircleMap v).comp
        (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))) =
      coordinateCircleMap v := by
  apply ContinuousMap.ext
  intro z
  ext i
  change circleCoordinateHomeomorph (circleCoordinateHomeomorph.symm z ^ v i) = v i • z
  rw [circleCoordinateHomeomorph_zpow, Homeomorph.apply_symm_apply]

/-- The parameter's positive generator maps to the literal positive vector loop. -/
theorem compactPhaseCircleMap_positiveHomology (v : Fin 2 → ℤ) :
    homeomorphHomologyEquiv compactFibreTorusHomeomorph 1
      (singularHomologyMap (compactPhaseCircleMap v) 1 (unitCircleHomologyOneEquiv.symm 1)) =
      loopHomologyClass (coordinatePeriodLoop 2 v) := by
  change ((singularHomologyMap
    (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2)) 1).comp
      ((singularHomologyMap (compactPhaseCircleMap v) 1).comp
        (singularHomologyMap
          (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle)) 1)))
            (circleHomologyOneEquiv.symm 1) = _
  rw [← singularHomologyMap_comp, ← singularHomologyMap_comp,
    compactPhaseCircleMap_coordinates, circleHomologyOneEquiv_symm_one]
  exact coordinateCircleMap_positiveHomology v

/-- The two actual Pascal coordinate-subtorus classes are the positive loops,
with their explicitly reversed index order. -/
theorem compactPhase_coordinateTorusClass (i : Fin 2) :
    coordinateTorusClass 2 1 (compactPhaseH1IndexEquiv i) =
      loopHomologyClass (coordinatePeriodLoop 2 (Pi.single i 1)) := by
  rw [coordinateTorusClass, productTorusTopClass_one, coordinateTorusMap_eq_torusMatrixMap]
  change inducedHomology (torusMatrixMap (coordinateTorusMatrix 2 1 (compactPhaseH1IndexEquiv i)))
    (loopHomologyClass (coordinatePeriodLoop 1 (Pi.single 0 1))) = _
  rw [torusMatrixMap_coordinatePeriodHomology]
  congr 2
  fin_cases i <;> decide

/-- The genuine homology class of the positive circle in one compact-phase coordinate. -/
def compactPhaseCoordinateClass (i : Fin 2) : SingularHomology CompactFibreTorus 1 :=
  singularHomologyMap (compactPhaseCircleMap (Pi.single i 1)) 1
    (unitCircleHomologyOneEquiv.symm 1)

/-- The literal positive loop in the displayed compact-phase coordinate. -/
def compactPhaseCoordinateLoop (i : Fin 2) : Path (1 : CompactFibreTorus) 1 :=
  ((coordinatePeriodLoop 2 (Pi.single i 1)).map
    compactFibreTorusHomeomorph.symm.continuous).cast
      (by
        apply compactFibreTorusHomeomorph.injective
        rw [compactFibreTorusHomeomorph_one, Homeomorph.apply_symm_apply])
      (by
        apply compactFibreTorusHomeomorph.injective
        rw [compactFibreTorusHomeomorph_one, Homeomorph.apply_symm_apply])

theorem compactPhaseCoordinateLoop_apply (i j : Fin 2) (t : unitInterval) :
    compactPhaseCoordinateLoop i t j =
      _root_.Circle.exp (2 * Real.pi * ((t : ℝ) *
        (((Pi.single i 1 : Fin 2 → ℤ) j : ℤ) : ℝ))) := by
  change compactFibreTorusHomeomorph.symm (coordinatePeriodLoop 2 (Pi.single i 1) t) j = _
  rw [compactFibreTorusHomeomorph_symm_apply, coordinatePeriodLoop_apply,
    AddCircle.toCircle_apply_mk, div_one]

theorem compactPhaseCoordinateLoop_coordinates (i : Fin 2) :
    (compactPhaseCoordinateLoop i).map compactFibreTorusHomeomorph.continuous =
      (coordinatePeriodLoop 2 (Pi.single i 1)).cast
        compactFibreTorusHomeomorph_one compactFibreTorusHomeomorph_one := by
  apply Path.ext
  funext t
  exact compactFibreTorusHomeomorph.apply_symm_apply _

/-- The marked generator is the class of this actual positive coordinate loop. -/
theorem compactPhaseCoordinateClass_eq_loopHomologyClass (i : Fin 2) :
    compactPhaseCoordinateClass i = loopHomologyClass (compactPhaseCoordinateLoop i) := by
  apply (homeomorphHomologyEquiv compactFibreTorusHomeomorph 1).injective
  rw [compactPhaseCoordinateClass, compactPhaseCircleMap_positiveHomology]
  change loopHomologyClass (coordinatePeriodLoop 2 (Pi.single i 1)) =
    inducedHomology (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2))
      (loopHomologyClass (compactPhaseCoordinateLoop i))
  rw [inducedHomology_loopHomologyClass, compactPhaseCoordinateLoop_coordinates]
  rfl

@[simp] theorem compactPhaseH1Equiv_coordinateClass (i : Fin 2) :
    compactPhaseH1Equiv (compactPhaseCoordinateClass i) = Pi.single i 1 := by
  change compactPhaseH1OrderEquiv
    (productTorusHomologyEquiv 2 1
      (homeomorphHomologyEquiv compactFibreTorusHomeomorph 1
        (singularHomologyMap (compactPhaseCircleMap (Pi.single i 1)) 1
          (unitCircleHomologyOneEquiv.symm 1)))) = _
  rw [compactPhaseCircleMap_positiveHomology, ← compactPhase_coordinateTorusClass,
    productTorusHomologyEquiv_coordinateTorusClass]
  ext j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem compactPhaseH1Equiv_symm_single (i : Fin 2) :
    compactPhaseH1Equiv.symm (Pi.single i 1) = compactPhaseCoordinateClass i := by
  apply compactPhaseH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, compactPhaseH1Equiv_coordinateClass]

@[simp] theorem compactPhaseH1Equiv_coordinateLoop (i : Fin 2) :
    compactPhaseH1Equiv (loopHomologyClass (compactPhaseCoordinateLoop i)) = Pi.single i 1 := by
  rw [← compactPhaseCoordinateClass_eq_loopHomologyClass, compactPhaseH1Equiv_coordinateClass]

theorem compactPhaseH1Equiv_symm_apply (v : Fin 2 → ℤ) :
    compactPhaseH1Equiv.symm v =
      v 0 • compactPhaseCoordinateClass 0 + v 1 • compactPhaseCoordinateClass 1 := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_zsmul, map_zsmul, compactPhaseH1Equiv_symm_single,
    compactPhaseH1Equiv_symm_single]

/-- The actual integral combinations of the two ordered positive coordinate-loop classes. -/
def compactPhaseCoordinateHomology : (Fin 2 → ℤ) →ₗ[ℤ]
    SingularHomology CompactFibreTorus 1 := compactPhaseH1Equiv.symm.toLinearMap

theorem compactPhaseCoordinateHomology_apply (v : Fin 2 → ℤ) :
    compactPhaseCoordinateHomology v =
      v 0 • compactPhaseCoordinateClass 0 + v 1 • compactPhaseCoordinateClass 1 :=
  compactPhaseH1Equiv_symm_apply v

@[simp] theorem compactPhaseCoordinateHomology_single (i : Fin 2) :
    compactPhaseCoordinateHomology (Pi.single i 1) = compactPhaseCoordinateClass i :=
  compactPhaseH1Equiv_symm_single i

@[simp] theorem compactPhaseH1Equiv_coordinateHomology (v : Fin 2 → ℤ) :
    compactPhaseH1Equiv (compactPhaseCoordinateHomology v) = v :=
  compactPhaseH1Equiv.apply_symm_apply v

@[simp] theorem compactPhaseCoordinateHomology_marking
    (a : SingularHomology CompactFibreTorus 1) :
    compactPhaseCoordinateHomology (compactPhaseH1Equiv a) = a :=
  compactPhaseH1Equiv.symm_apply_apply a

end Wikipedia.HopfProblem.CuspCentralHomology
