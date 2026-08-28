# Boundary fundamental-class identification: checked

Checkpoint 14856 proves that the ACTUAL homology connecting image of the
slab's relative fundamental class is the fundamental class for the
RETAINED boundary atlas in `FramedSlabData`. The full Lean build and
axiom audit pass without changing computational limits. The unconditional
no-exotic-six-spheres theorem is still unproved.

## Checked proof

1. `RelativeCoefficients.exists_lift_of_connecting_projection_zero` in
   `RelativeCoefficientTripleLift.lean` corrects an ambient representative
   by subtracting an actual subspace chain. This constructs a relative
   lift through the ORIGINAL identity map of nested pairs, with its exact
   image formula. Coefficients are arbitrary integral modules.
2. `RelativeCoefficients.connecting_localize_ne_zero` in
   `RelativeBoundaryLocalNonvanishing.lean` applies this lift at a boundary
   puncture. Ambient local vanishing makes the lifted supported class zero
   locally. The checked zero-neighborhood theorem and density of the
   complement contradict the nonzero interior local values.
3. `RegularSlabBoundaryFundamentalClass.lean` supplies these hypotheses
   for the actual slab. Nonzero local mod-two values and the original
   uniqueness theorem identify the connecting image with the fundamental
   class for the supplied boundary atlas. It allows the boundary subset
   to be specified by its original manifold predicate.
4. `FramedSlabBoundaryFundamentalClass.lean` uses `A.atlas`, its actual
   boundary predicate, and `A.boundaryAtlas`. It derives boundary
   compactness and proves `connecting_nativeRelativeFundamentalClass`.
   `nativeConnectingCap` and `nativeBoundaryCap_kernel` concern the
   original boundary fundamental class, not a class assigned to fit them.

For a boundary of dimension `r + 3`, the slab has dimension `r + 4` and
the relative-class parameter is `r + 1`. The six-dimensional case is
`r = 3`.

## Checked kernel theorem and its scope

`MiddleCapKernelOrthogonality.lean` combines the actual cap-kernel
criterion with original evaluation naturality. Native mod-two
functionals separate the target homology, proving that the right
annihilator of the inclusion kernel equals that kernel.

`FramedSlabBoundaryKernel.lean` specializes this to the retained boundary.
It proves `nativeBoundaryKernel_selfOrthogonal`,
`nativeBoundaryGeometricKernel_selfOrthogonal`, and
`nativeBoundaryQuadraticKernel_selfOrthogonal`. The geometric and polar
versions use the existing actual cap/geometric pairing comparison for a
supplied embedding, normal frame, and tubular retraction.

These results require BOTH the actual boundary and filling to be
two-connected. They do not construct the connectivity surgery, do not
identify an arbitrary prescribed frame with the induced filling frame,
and do not automatically handle a disconnected two-ended boundary.

## Remaining geometric work

Checkpoint 14933 constructs SMOOTH four-disks from actual integral
boundary-kernel classes in a two-connected seven-dimensional slab
(`SmoothIntegralKernelDisk.lean`). The original regular-fiber atlas is
retained, the outer collar is fixed, and every interior disk point stays
in the actual slab interior. Original spatial immersion gives injective
boundary derivatives. Global immersion and integral-to-mod-two coefficient
control remain unproved; these do not follow from the boundary result.

The original quadratic form must still be proved to VANISH on the
inclusion kernel. The checked immersed framed-disk vanishing theorem
requires actual disks and the correct original boundary framing.
Framing-preserving interior surgery, relative immersed-disk approximation,
and integral-to-mod-two kernel control remain obligations. In particular,
mod-two nullity must not be treated as integral or homotopy nullity.

Arf bordism invariance/detection, sixth-stem nontriviality and generation,
candidate collapse vanishing, and the final original-atlas diffeomorphism
and unconditional `SixSphereRigidity` are not proved by this checkpoint.

## Reference

The boundary fundamental-class property is the one required in
[Hatcher, Algebraic Topology, Chapter 3](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf),
Theorem 3.43 (printed page 254) and Exercise 31 (printed page 260).
The Lean proof above implements the local-vanishing argument using the
original relative complexes; the reference is not used as an axiom.
