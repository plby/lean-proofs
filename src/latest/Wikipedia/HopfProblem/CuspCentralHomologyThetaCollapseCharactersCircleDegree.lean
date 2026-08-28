import Wikipedia.HopfProblem.CuspCentralHomologyPhaseTori
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionCircles
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleNormalization
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusDegreeOne
import Wikipedia.HopfProblem.EllipticFixedPeriods

/-!
# Integer powers on the actual circle's first homology

The positive circle generator is the projection of an actual positive
coordinate loop.  The proved period-torus marking computes its integer
multiples, and the phase-coordinate homeomorphism transports this
calculation to the literal power map of the complex unit circle.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

/-- The literal integer-power map of the complex unit circle. -/
def circlePowerMap (k : ℤ) : C(_root_.Circle, _root_.Circle) :=
  ⟨fun z => z ^ k, continuous_id.zpow k⟩

@[simp] theorem circlePowerMap_apply (k : ℤ) (z : _root_.Circle) :
    circlePowerMap k z = z ^ k := rfl

private def additiveCirclePowerMap (k : ℤ) :
    C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)) :=
  ⟨fun z => k • z, continuous_id.zsmul k⟩

private def firstCircleProjection : C(ProductTorus 4, AddCircle (1 : ℝ)) :=
  ⟨fun x => x 0, continuous_apply 0⟩

private theorem firstCircleProjection_positiveLoop :
    (coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) 1)).map
        firstCircleProjection.continuous = CirclePaths.positiveLoop := by
  apply Path.ext
  funext t
  change coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) 1) t 0 =
    CirclePaths.positiveLoop t
  simp only [coordinatePeriodLoop_apply, Pi.single_eq_same, Int.cast_one,
    mul_one, CirclePaths.positiveLoop_apply]

private theorem firstCircleProjection_scalarLoop (k : ℤ) :
    (coordinatePeriodLoop 4 (k • Pi.single (0 : Fin 4) 1)).map
        firstCircleProjection.continuous =
      (CirclePaths.positiveLoop.map (additiveCirclePowerMap k).continuous).cast
        (by simp [additiveCirclePowerMap, firstCircleProjection])
        (by simp [additiveCirclePowerMap, firstCircleProjection]) := by
  apply Path.ext
  funext t
  change coordinatePeriodLoop 4 (k • Pi.single (0 : Fin 4) 1) t 0 =
    k • CirclePaths.positiveLoop t
  rw [coordinatePeriodLoop_apply, CirclePaths.positiveLoop_apply]
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  change (((t : ℝ) * (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
    ((k • (t : ℝ) : ℝ) : AddCircle (1 : ℝ))
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

private theorem additiveCirclePowerMap_positiveClass (k : ℤ) :
    singularHomologyMap (additiveCirclePowerMap k) 1
        (loopHomologyClass CirclePaths.positiveLoop) =
      k • loopHomologyClass CirclePaths.positiveLoop := by
  have h := congrArg (inducedHomology firstCircleProjection)
    (map_zsmul (coordinateH1 4) k (Pi.single (0 : Fin 4) 1))
  rw [coordinateH1_four_apply (Elliptic.examplePeriod .four), coordinateH1_single,
    map_zsmul, inducedHomology_loopHomologyClass, inducedHomology_loopHomologyClass,
    firstCircleProjection_scalarLoop, firstCircleProjection_positiveLoop] at h
  rw [singularHomologyMap_one, inducedHomology_loopHomologyClass]
  exact h

private theorem additiveCirclePowerMap_homology (k : ℤ)
    (a : SingularHomology (AddCircle (1 : ℝ)) 1) :
    circleHomologyOneEquiv (singularHomologyMap (additiveCirclePowerMap k) 1 a) =
      k * circleHomologyOneEquiv a := by
  obtain ⟨m, rfl⟩ := circleHomologyOneEquiv.symm.surjective a
  rw [LinearEquiv.apply_symm_apply, circleHomologyOneEquiv_symm_int,
    map_zsmul, additiveCirclePowerMap_positiveClass, map_zsmul,
    map_zsmul, circleHomologyOneEquiv_positiveLoop]
  simp [mul_comm]

private theorem circlePowerMap_coordinate (k : ℤ) :
    (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))).comp
        (circlePowerMap k) =
      (additiveCirclePowerMap k).comp
        (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) := by
  apply ContinuousMap.ext
  intro z
  exact circleCoordinateHomeomorph_zpow z k

/-- The literal power map acts by its integer exponent on actual singular `H₁`,
with the positive unit-circle normalization. -/
theorem unitCircleHomologyOneEquiv_circlePowerMap (k : ℤ)
    (a : SingularHomology _root_.Circle 1) :
    unitCircleHomologyOneEquiv (singularHomologyMap (circlePowerMap k) 1 a) =
      k * unitCircleHomologyOneEquiv a := by
  change circleHomologyOneEquiv
      (singularHomologyMap
        (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) 1
          (singularHomologyMap (circlePowerMap k) 1 a)) =
    k * circleHomologyOneEquiv
      (singularHomologyMap
        (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) 1 a)
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, circlePowerMap_coordinate,
    singularHomologyMap_comp, LinearMap.comp_apply]
  exact additiveCirclePowerMap_homology k _

end Wikipedia.HopfProblem.CuspCentralHomology
