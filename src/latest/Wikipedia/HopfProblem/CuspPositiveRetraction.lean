import Wikipedia.HopfProblem.CuspPositiveRetractionCusp
import Wikipedia.HopfProblem.CuspPositiveRetractionStrong
import Wikipedia.HopfProblem.CuspPositiveRetractionClosedQuotient

/-!
# Actual closed cusp-neighborhood deformation retractions

This module completes the existence assertion in Lemma 7.8 by an explicit
local minimum-coordinate collapse, compact finite patching in the actual
positive quotient, and covering-homotopy lifting. The resulting positive
deformation is a genuine lattice-equivariant strong deformation
retraction on all sufficiently small closed positive tubes.

Polar spreading, the exact frozen phase covariance, and the previously
constructed straightening then give an actual strong deformation
retraction of each sufficiently small closed neighborhood in the original
cusp quotient onto its literal central fibre. Upstairs it is equivariant
for the original twisted lattice action and the compact fibre torus.

These results establish the retraction existence used by Proposition 7.2
and Lemma 7.3. They do not assert a retraction of the entire open tube or
the additional prescribed honeycomb collapse description of a nonzero
fibre in Proposition 7.2 and Lemma 7.10.
-/
