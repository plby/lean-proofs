import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseCharactersMarking
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseCharactersCircleDegree

/-!
# The actual homology characters of the three theta-collapse edges

The determinant character is evaluated on the actual two positive coordinate
circles. The proved circle-power degree formula and linearity then compute
the induced first singular homology map on every actual phase class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology ToricSpace ToricComponent

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The literal determinant character as a continuous map. -/
def edgeCharacterMap (n : Fin 2 → ℤ) : C(CompactFibreTorus, _root_.Circle) :=
  ⟨edgeCharacter n, edgeCharacter_continuous n⟩

@[simp] theorem edgeCharacterMap_apply (n : Fin 2 → ℤ) (u : CompactFibreTorus) :
    edgeCharacterMap n u = u 0 ^ (-n 1) * u 1 ^ n 0 := rfl

/-- The composite of the actual character with an actual phase circle is the displayed power. -/
theorem edgeCharacterMap_comp_circle (n v : Fin 2 → ℤ) :
    (edgeCharacterMap n).comp (compactPhaseCircleMap v) =
      circlePowerMap (n 0 * v 1 - n 1 * v 0) := by
  apply ContinuousMap.ext
  intro z
  exact edgeCharacter_edgeCompactPhase n v z

/-- The actual circle-vector class has the determinant as its character degree. -/
theorem edgeCharacter_circleHomology (n v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (edgeCharacterMap n) 1
        (singularHomologyMap (compactPhaseCircleMap v) 1
          (unitCircleHomologyOneEquiv.symm 1))) =
      -n 1 * v 0 + n 0 * v 1 := by
  change unitCircleHomologyOneEquiv
    (((singularHomologyMap (edgeCharacterMap n) 1).comp
      (singularHomologyMap (compactPhaseCircleMap v) 1))
        (unitCircleHomologyOneEquiv.symm 1)) = _
  rw [← singularHomologyMap_comp, edgeCharacterMap_comp_circle,
    unitCircleHomologyOneEquiv_circlePowerMap, LinearEquiv.apply_symm_apply, mul_one]
  ring

@[simp] theorem edgeCharacter_coordinateClass_zero (n : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (edgeCharacterMap n) 1 (compactPhaseCoordinateClass 0)) = -n 1 := by
  simpa only [compactPhaseCoordinateClass, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    mul_one, mul_zero, add_zero] using edgeCharacter_circleHomology n (Pi.single 0 1)

@[simp] theorem edgeCharacter_coordinateClass_one (n : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (edgeCharacterMap n) 1 (compactPhaseCoordinateClass 1)) = n 0 := by
  simpa only [compactPhaseCoordinateClass, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    mul_one, mul_zero, zero_add] using edgeCharacter_circleHomology n (Pi.single 1 1)

/-- The induced map on the actual coordinate-loop combinations is the literal integer character. -/
theorem edgeCharacter_coordinateHomology (n v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (edgeCharacterMap n) 1 (compactPhaseCoordinateHomology v)) =
      -n 1 * v 0 + n 0 * v 1 := by
  rw [compactPhaseCoordinateHomology_apply]
  simp only [map_add, map_zsmul, edgeCharacter_coordinateClass_zero,
    edgeCharacter_coordinateClass_one, zsmul_eq_mul, Int.cast_id]
  ring

/-- Every actual compact-phase homology class satisfies the same character
formula in its marking. -/
theorem edgeCharacter_homologyOne (n : Fin 2 → ℤ)
    (a : SingularHomology CompactFibreTorus 1) :
    unitCircleHomologyOneEquiv (singularHomologyMap (edgeCharacterMap n) 1 a) =
      -n 1 * compactPhaseH1Equiv a 0 + n 0 * compactPhaseH1Equiv a 1 := by
  simpa only [compactPhaseCoordinateHomology_marking] using
    edgeCharacter_coordinateHomology n (compactPhaseH1Equiv a)

theorem hexagonCharacter_coordinateHomology_zero (v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (edgeCharacterMap (hexagonRay 0)) 1
        (compactPhaseCoordinateHomology v)) = v 1 := by
  simpa [hexagonRay] using edgeCharacter_coordinateHomology (hexagonRay 0) v

theorem hexagonCharacter_coordinateHomology_one (v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (edgeCharacterMap (hexagonRay 1)) 1
        (compactPhaseCoordinateHomology v)) = -v 0 := by
  simpa [hexagonRay] using edgeCharacter_coordinateHomology (hexagonRay 1) v

theorem hexagonCharacter_coordinateHomology_two (v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (edgeCharacterMap (hexagonRay 2)) 1
        (compactPhaseCoordinateHomology v)) = -v 0 - v 1 := by
  simpa [hexagonRay, sub_eq_add_neg] using edgeCharacter_coordinateHomology (hexagonRay 2) v

end Wikipedia.HopfProblem.CuspCentralHomology
