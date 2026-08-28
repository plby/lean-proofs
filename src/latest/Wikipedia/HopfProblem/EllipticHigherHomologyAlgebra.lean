import Wikipedia.HopfProblem.EllipticHigherHomologyAlgebraInverse

/-!
# Integral algebra for the higher homology of the elliptic pieces

This package computes the actual integral kernels and cokernels of the
restricted fibre monodromy and its exterior square.  Both are explicitly
linearly equivalent to `ℤ`, for each of the order-three and order-four
actions.  The inverse-monodromy operators have the same submodules.

The degree-one invariant generator is `(0,0,1)`.  The coinvariant
coordinates are `(2,1,3)` and `(1,1,2)`.  The degree-two invariant
generators are `(3,-1,2)` and `(2,-1,1)`; the coinvariant coordinate is
the first entry.  Every image equality is proved by an integral preimage.

The main equivalences are `fibreKernelEquivInt`, `fibreCokernelEquivInt`,
`fibreSquareKernelEquivInt`, and `fibreSquareCokernelEquivInt`.  Their
inverse-convention versions insert `Inverse` before `Kernel` or `Cokernel`.
Each equivalence includes formulas for its forward and inverse maps.

This is lattice algebra only.  No Wang sequence or comparison with the
singular homology of a topological space is assumed or asserted here.
-/
