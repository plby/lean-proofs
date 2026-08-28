import Wikipedia.HopfProblem.CuspCentralCohomologySlopeForm
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricEdges

/-!
# The source's three-ray ordering

The actual first three hexagon rays are `w,δ,δ-w`.  The source's displayed
list is `w,δ-w,-δ`.  The permutation below is therefore `(0,2,1)`, with
the last normal reversed.  These are finite equalities of the actual
toric rays.  Since the native slope class is quadratic in its character,
the reversal leaves that class unchanged.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspCentralHomology

/-- The explicit permutation from the displayed source order to the
already fixed actual double-curve indices. -/
def paperCurveOrder : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

/-- The three primitive directions displayed in the specialization proof. -/
def paperCurveNormal : Fin 3 → (Fin 2 → ℤ) :=
  ![![1, 0], ![-1, 1], ![0, -1]]

/-- The actual toric rays agree with the displayed directions, up to
the specified reversal of the last primitive normal. -/
theorem paperCurveOrder_ray (j : Fin 3) :
    ToricComponent.hexagonRay (thetaEdgeIndex (paperCurveOrder j)) =
      (if j = 2 then (-1 : ℤ) else 1) • paperCurveNormal j := by
  fin_cases j <;> decide

/-- The character coefficients in the source's own displayed order. -/
theorem paperCurveNormal_character :
    (fun j : Fin 3 =>
      ![-paperCurveNormal j 1, paperCurveNormal j 0] : Fin 3 → (Fin 2 → ℤ)) =
      ![![0, 1], ![-1, -1], ![1, 0]] := by
  decide

/-- Reindexing the actual native slope classes gives exactly the
source's displayed normal formula; no abstract basis change is made. -/
theorem slopeClass_actualRay_paperOrder (j : Fin 3) :
    slopeClass (-ToricComponent.hexagonRay (thetaEdgeIndex (paperCurveOrder j)) 1)
        (ToricComponent.hexagonRay (thetaEdgeIndex (paperCurveOrder j)) 0) =
      slopeClass (-paperCurveNormal j 1) (paperCurveNormal j 0) := by
  apply coordinateTorusH2CohomologyCoordinates.injective
  rw [slopeClass_coordinates, slopeClass_coordinates]
  fin_cases j <;> decide

/-- The already fixed cylinder-orientation signs in the source's order. -/
theorem paperCurveOrder_orientationSign (j : Fin 3) :
    -thetaEdgeOrientationSign (paperCurveOrder j) = (![(-1 : ℤ), -1, 1] : Fin 3 → ℤ) j := by
  fin_cases j <;> decide

/-- The three displayed quadratic coefficient vectors, before their
separately fixed geometric orientation signs. -/
theorem paperCurveNormal_slopeCoefficients :
    (fun j : Fin 3 => slopeCoefficients (-paperCurveNormal j 1) (paperCurveNormal j 0)) =
      ![![0, 0, 1, 0, 0, 0], ![0, 1, 1, -1, -1, 0], ![0, 0, 0, -1, 0, 0]] := by
  decide

end Wikipedia.HopfProblem.CuspCentralCohomology
