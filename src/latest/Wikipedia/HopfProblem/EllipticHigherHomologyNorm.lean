import Wikipedia.HopfProblem.EllipticHigherHomologyNormDegreeOne
import Wikipedia.HopfProblem.EllipticHigherHomologyNormDegreeTwo
import Wikipedia.HopfProblem.EllipticHigherHomologyNormTop

/-!
# Exact integral norm operators for the elliptic fibre

This package computes the finite sums of powers of the actual restricted
fibre matrices and their exterior squares.  In the explicit invariant
integer coordinates, the degree-one norm is the primitive coinvariant
functional times `fibreNormIndex`, and the degree-two norm is the first
coordinate times that same index.  The index is one for the order-three
action and two for the order-four action.  In top degree it is the order.

The actual integer norm maps factor through the invariant submodules in
both forward- and inverse-monodromy conventions.  They descend from the
corresponding coinvariant quotients to injective maps into the invariant
lattices, with proved exact image indices and explicit integer-coordinate
formulas.  Every image computation includes integral preimages.

These are algebraic statements about finite norm operators, not assertions
that a norm has been identified with any topological covering or transfer.
-/
