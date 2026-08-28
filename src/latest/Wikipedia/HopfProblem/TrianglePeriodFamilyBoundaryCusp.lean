import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspSourceProjection

/-!
# The actual cusp boundary map in the regular-family source kernel

The original logarithmic cusp boundary is compared with the fixed
clockwise outer circle by an actual homotopy, using the proved reciprocal
analytic cusp coordinate.  Lift uniqueness determines its genuine tail
and both slit frames.  The tail is proved to centralize the original cusp
generator, and therefore fixes genuine Wang classes.  Actual refined-cover
Mayer--Vietoris naturality gives the unconditional all-degree formula
`Cusp.boundary_sourceKernelProjection`.

In the fixed two-source coordinates, a Wang class `w` contributes
`(-g₁⁻¹_* w, -w)`.  This identifies the source-kernel projection of the
literal original map.  It does not assign a fibre-residual coefficient in
an arbitrary splitting of the regular-family homology extension.
-/
