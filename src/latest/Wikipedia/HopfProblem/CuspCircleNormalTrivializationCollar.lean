import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarSides
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarEquivariance

/-!
# A native analytic collar of the actual compact normal-neighborhood boundary

`Collar.radialDiffeomorph` is the literal standard polar collar from
`S³ × (-1/2, 1/2)` to the Euclidean annulus `1/4 < ‖x‖ < 3/4`.
`Collar.actualCollarDiffeomorph` multiplies this with the standard two-sphere
and composes the actual native threefold chart, producing a real-analytic
collar of the original ambient frontier. Its zero slice is the same
standard boundary parametrization; negative and positive parameters
identify the actual interior and exterior of the compact disk image.
The original period-one circle action preserves the signed parameter.

No topology or ambient atlas is transported, and no global complement
or sphere-recognition assertion is made.
-/
