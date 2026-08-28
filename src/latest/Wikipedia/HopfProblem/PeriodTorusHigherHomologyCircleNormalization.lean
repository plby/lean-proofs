import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductUnit

/-!
# Positive-generator normalization of actual circle homology

The actual right-point unit of the cross product identifies its product
with the point's zero-class with the actual circle-to-circle-times-point
homeomorphism map. The proved connecting calculation then shows that
the literal positive quotient loop is marked by `+1`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris CircleTopology CirclePaths

/-- The point's actual zero-class is the right unit for the positive circle cross product. -/
theorem positiveCircleCross_pointClass :
    positiveCircleCross Unit 0 (pointClass ()) =
      homeomorphHomologyEquiv (Homeomorph.prodUnique Circle Unit).symm 1
        (loopHomologyClass positiveLoop) :=
  crossProductHomology_pointClass_right Circle Unit (loopHomologyClass positiveLoop) ()

/-- The actual signed connecting marking sends the literal positive circle loop to `+1`. -/
@[simp] theorem circleHomologyOneEquiv_positiveLoop :
    circleHomologyOneEquiv (loopHomologyClass positiveLoop) = 1 := by
  rw [circleHomologyOneEquiv_apply, ← positiveCircleCross_pointClass,
    circleBoundary_positiveCircleCross]
  exact connectedHomologyZeroEquiv_pointClass ()

/-- The inverse of the integral marking picks the actual positive-loop class. -/
@[simp] theorem circleHomologyOneEquiv_symm_one :
    circleHomologyOneEquiv.symm 1 = loopHomologyClass positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, circleHomologyOneEquiv_positiveLoop]

/-- All integral multiples are the corresponding actual positive-loop homology classes. -/
theorem circleHomologyOneEquiv_symm_int (k : ℤ) :
    circleHomologyOneEquiv.symm k = k • loopHomologyClass positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, map_zsmul, circleHomologyOneEquiv_positiveLoop]
  simp

/-- The degree-zero marking sends every actual point class to the integral unit. -/
@[simp] theorem circleHomologyZeroEquiv_pointClass (x : Circle) :
    circleHomologyZeroEquiv (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
