import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportRegularMarking
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportMatrices

/-!
# Actual higher-homology local systems of the regular triangle family

Actual path transport between literal fibres induces the singular-homology
equivalences in every degree, with the identity, composition, inverse, and
relative-homotopy laws. The actual second and third singular homology are
canonically marked by the exterior square and cube of the positive period
lattice. These markings agree with the original complex period columns
and are constant along projections of upstairs paths.

For every base loop, the induced higher-homology maps are the exterior
powers of its actual lattice-monodromy matrix. The lifted-endpoint
convention is explicit: an endpoint `g • b` gives the action of `g⁻¹`,
and an endpoint `g⁻¹ • b` gives the action of `g`. Actual projected loops
realize every triangle element; they are not asserted to be geometric
meridians. In the ordered minor bases, their actual maps are the proved
six-by-six and four-by-four matrices of the source.

The regular-family results use the actual regular covering theorem, not
a covering or local-system hypothesis. The period map and its two
generator covariance laws are precisely the input data of the existing
regular-family construction.
-/
