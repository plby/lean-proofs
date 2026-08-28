import Wikipedia.HopfProblem.QuaternionPowerNullhomotopy
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix

/-! # The proved exponent of the native sixth homotopy group of the three-sphere -/

namespace Wikipedia.HopfProblem.QuaternionPowerNullhomotopy

/-- The original exponent hypothesis is discharged by the unconditional
isomorphism `π₆(S³) ≃* Multiplicative (ZMod 12)`. -/
theorem sphereExponentTwelve : SphereExponentTwelve :=
  sphereExponentTwelve_of_mulEquiv
    (Wikipedia.HomotopyGroupsOfSpheres.pi6_sphere_three_mulEquiv _)

end Wikipedia.HopfProblem.QuaternionPowerNullhomotopy
