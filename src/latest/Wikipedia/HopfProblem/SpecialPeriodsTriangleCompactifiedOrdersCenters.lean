import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlasAgreement
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticNeighborhoods

/-!
# Distinguished elliptic points of the compactified triangle quotient

The two elliptic orbit centers remain distinct after including the original
quotient in its one-point compactification, and neither is the added cusp.
Every translate of an elliptic fixed point projects to the corresponding
compactified center.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The order-three orbit center in the actual compactified quotient. -/
def triangleCompactifiedCenterOne : TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion triangleOrbitCenterOne

/-- The order-four orbit center in the actual compactified quotient. -/
def triangleCompactifiedCenterTwo : TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion triangleOrbitCenterTwo

theorem triangleCompactifiedCenterOne_ne_centerTwo :
    triangleCompactifiedCenterOne ≠ triangleCompactifiedCenterTwo := by
  intro h
  exact triangleOrbitCenterOne_ne_centerTwo (OnePoint.coe_injective h)

@[simp] theorem triangleCompactifiedCenterOne_ne_cusp :
    triangleCompactifiedCenterOne ≠ triangleCuspPoint :=
  triangleOpenInclusion_ne_cusp triangleOrbitCenterOne

@[simp] theorem triangleCompactifiedCenterTwo_ne_cusp :
    triangleCompactifiedCenterTwo ≠ triangleCuspPoint :=
  triangleOpenInclusion_ne_cusp triangleOrbitCenterTwo

namespace Triangle

/-- The compactified elliptic center indexed by its elliptic kind. -/
def ellipticCompactifiedCenter (j : Elliptic.Kind) : TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion (ellipticOrbitCenter j)

@[simp] theorem ellipticCompactifiedCenter_three :
    ellipticCompactifiedCenter .three = triangleCompactifiedCenterOne := rfl

@[simp] theorem ellipticCompactifiedCenter_four :
    ellipticCompactifiedCenter .four = triangleCompactifiedCenterTwo := rfl

theorem ellipticCompactifiedCenter_ne_other (j : Elliptic.Kind) :
    ellipticCompactifiedCenter j ≠ ellipticCompactifiedCenter (ellipticOtherKind j) := by
  intro h
  exact ellipticOrbitCenter_ne_other j (OnePoint.coe_injective h)

@[simp] theorem ellipticCompactifiedCenter_ne_cusp (j : Elliptic.Kind) :
    ellipticCompactifiedCenter j ≠ triangleCuspPoint :=
  triangleOpenInclusion_ne_cusp (ellipticOrbitCenter j)

@[simp] theorem triangleCompactifiedProjection_ellipticCenter (j : Elliptic.Kind) :
    triangleCompactifiedProjection (ellipticCenter j) = ellipticCompactifiedCenter j := rfl

@[simp] theorem triangleCompactifiedProjection_translated_ellipticCenter
    (j : Elliptic.Kind) (g : TriangleGroup) :
    triangleCompactifiedProjection (triangleGeometricRepresentation g (ellipticCenter j)) =
      ellipticCompactifiedCenter j := by
  change triangleOpenInclusion
    (triangleOrbitProjection (triangleGeometricRepresentation g (ellipticCenter j))) = _
  rw [triangleOrbitProjection_smul]
  rfl

end Triangle

end Wikipedia.HopfProblem.SpecialPeriods
