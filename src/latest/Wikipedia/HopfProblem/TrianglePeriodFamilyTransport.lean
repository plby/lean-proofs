import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportRegular

/-!
# Flat transport and actual singular-homology monodromy of the regular family

This package constructs transport between the literal fibres of the actual
regular triangle quotient family. A base path is uniquely lifted through
the proved regular covering, and its real torus coordinate is kept fixed.
The resulting horizontal path and endpoint homeomorphism are independent
of the quotient representative. Transport has the identity, composition,
inverse, and relative-homotopy laws.

The induced maps are Mathlib's actual integral singular-homology maps.
The fibre marking is proved to agree with the original complex period
columns, and the resulting monodromy is the actual special-linear
representation constructed from lifted endpoints and the dual triangle
representation. No local-system or transport law is assumed.

The inverse convention is explicit: an endpoint `g • b` gives the matrix
of the dual representation at `g⁻¹`. Specified inverse-generator lifts
give `A₁`, `A₂`, and `M₀`. The package also constructs actual loops realizing
every deck element; arbitrary chosen connecting paths are not asserted
to be geometric meridians. The endpoint formulas apply to any specified
meridians with the indicated lifts.

All covering hypotheses are discharged for `regularData P h₁ h₂`, where
`P` is the supplied admissible holomorphic period map with the two proved
generator transformation laws.
-/
