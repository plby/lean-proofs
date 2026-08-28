# Half-image excision — native low-surgery component Arf checked

The checked coefficient theorem `MiddleKernelCoefficients.kernel_iff_has_half`
gives, for a mod-two boundary kernel class, an integral lift `x` and a class
`y` in the actual half with `j(x) = 2 • y`. The construction below now
settles this case for an actual embedded old-boundary sphere, without
assuming that the half-image obstruction vanishes. It proves the full
mod-two quadratic-kernel theorem on any two-connected native clopen boundary
component, retaining the restricted original frame. When its complement is
a topological six-sphere, the actual cap kernel also proves Arf vanishing.
A general relation spanning several boundary components remains open.

Checkpoint 16687 includes
the positive core tube, its actual regular exterior and combined collar,
the original native boundary-frame comparison, and exterior two-connectivity.
It also proves the exact integral half-image relation and even-longitude
decomposition, zero meridian parity for the original induced frame, and
zero pulled-back quadratic value for the actual even-longitude class,
embedded representatives, and transfer to the original sphere parity.

1. Represent `y` by a smooth embedded three-sphere in the positive interior.
   The existing `TimeCollar.exists_interior_core_representative` supplies
   this with the original surgery top-class marking when the ambient
   seven-manifold is compact. The actual `LowCollaredSevenState` has a
   `compact` field, so compactness is already available for those filling
   states; no new compactness hypothesis is needed there. Keep the cubical
   and surgery sphere class markings distinct; their integral unit comparison
   is available.
2. `exists_positive_core_fourNormalTube` now constructs the actual smooth
   four-normal tube wholly in positive time, with unrestricted normal
   coordinates, a smooth partial inverse, and the original integral marking.
   `SphereFourTube.exists_regular_time_modification` supplies a globally
   smooth regular time whose nonnegative half is exactly the old half minus
   the open unit tube. Its zero set is exactly the old boundary and unit
   tube boundary. The old time is unchanged on neighborhoods of old zeros.
   `exists_separated_time_bands` separates the old and new collar bands.
   `exists_collared_regular_time_modification` now constructs the combined
   time collar over `B ⊕ (S³ × S³)`, with exact old and new zero-point
   formulas. `SphereFourTubeOldZeroFrame` proves that the old zero inclusion
   is an open embedding and a local diffeomorphism for the native regular
   zero atlases, and that the full original outward induced frame is
   unchanged, even with independent tubular retractions.
3. `TimeCollarPositiveCoreComplement` now applies the native image
   avoidance theorems to the actual positive core. Its complement is
   nonempty, simply connected, and has vanishing native second homotopy.
   `SphereFourTubeRetraction` constructs the actual radial retraction,
   fixing the exterior. `SphereFourTubeHalfRetract` combines it with the
   new collar slide to give a homotopy right inverse onto the literal
   new half. `SphereFourTubeExteriorConnectivity` proves that this half
   is simply connected, has `π₂ = 0`, and has integral `H₂ = 0`.
   No equivalence with the original half is asserted.
4. `SphereFourTubeHalfCover` now constructs the actual open cover of the
   old half by its full core complement `U` and open unit tube `V`.
   `SphereFourTubeHalfCoverMaps` checks both exact overlap map identities
   using the actual normal normalization. `SphereFourTubeHalfImageRelation`
   applies `exact_at_pair` to `(j_U(x), -2 • core_V)` and constructs the
   boundary class with longitude projection exactly twice the marked
   generator. No injectivity of the tube-to-half map is used, including
   for torsion core images. `SphereFourTubeOldBoundaryRelation` proves
   the resulting integral relation for an arbitrary original boundary
   class, with its native old-zero inclusion unchanged.
5. `SphereFourTubeHalfImageCoordinates` now decomposes the lifted class
   using the actual product third-homology equivalence: its longitude
   coefficient is exactly two and its meridian coefficient is an integer.
   `SphereFourTubeMeridianParity` now proves zero induced-frame meridian
   parity using the actual immersive normal four-disk and the signed
   boundary-germ extension criterion. The original normal-plus-derivative
   operator extends over the disk, and the radial time derivative is
   exactly positive two. The original outward frame and native zero atlas
   are retained; no connectedness of the whole boundary is required.
6. `PullbackIntegralHomologyParity` now proves the actual quadratic
   identity for a continuous map from a two-connected source into a
   possibly disconnected compact framed six-manifold. It proves invariance
   under adding twice a class and zero parity for every integer multiple
   of a zero-parity class. `PullbackIntegralSphereMarking` compares the
   cubical and original surgery generators explicitly, using negation
   invariance to remove their possible sign difference.
   `SphereFourTubeBoundaryQuadraticValue` applies this to the actual
   product map into the native zero fiber with the original outward frame.
   It proves zero quadratic value for the even-longitude class, regardless
   of its integer meridian coefficient. Its
   `exists_old_boundary_zero_quadratic_relation` constructs such a class
   with exactly the old class's image in the actual new half.
   `SphereFourTubeBoundaryImmersion` now proves smoothness and immersion
   of the actual product-to-zero map in the native atlas.
   `SphereFourTubeEmbeddedRepresentatives` constructs genuinely embedded
   tube-side representatives with the original integral marking and zero
   original-frame parity. `SphereFourTubeOldSphereParity` proves exact
   preservation of the old raw frame operator and therefore its parity.
   `SphereFourTubeHalfImageSphereParity` applies the native annulus theorem
   to the separated representatives and transfers zero to the original
   sphere. `EmbeddedTimeHalfImageSphereParity` constructs the entire tube
   and collared exterior internally for any integral half-image class `y`.
   It proves zero original sphere parity whenever its half image is `2 • y`,
   whether `y` is zero, nonzero, or torsion.
7. For a disconnected old boundary, prove the corresponding boundary sum
   comparison; a relation involving several components is not automatically
   a single separated-sphere relation. Retain all component frames and the
   actual integral-to-mod-two reduction maps.

Steps 1–6 are now checked for actual embedded old-boundary spheres, with
the whole old boundary allowed to be disconnected. No torsion-free third
homology, primitive boundary image, or equality of the full mod-two kernel
with the reduced integral kernel is assumed.
`EmbeddedTimeTwoConnectedQuadraticKernel` combines the result with source
Hurewicz and the exact coefficient lifting theorem. It proves that the
original quadratic form vanishes on the full mod-two boundary-to-half
kernel when the whole native boundary is two-connected.

The candidate-specific homology reduction is now proved: if a native
clopen component's complement is a topological six-sphere, the component
carries all mod-two middle homology. The actual cap kernel is self-orthogonal
for its original geometric polar form, and the restricted original frame's
quadratic form vanishes on that kernel. Thus its genuine Arf invariant is
zero when the positive half and the chosen component are two-connected.

Checkpoint 16908 proves transport of original sphere parity, the actual
middle-homology quadratic form, and its geometric Arf invariant through
any supplied stabilized framed diffeomorphism. It retains both native
atlases and the actual ambient and normal-column comparisons. No extension
of the sphere-dependent source twist is assumed.

Checkpoint 16926 restricts the actual stabilized framed comparison to a
native clopen component and its literal image. It preserves the original
frame columns, transports two-connectivity, and identifies the complementary
subspaces with the actual inverse homeomorphism. The native low-surgery
sequence is now constructed internally: if the initial positive half is
path connected, the original component opposite a topological six-sphere
has zero original induced-frame Arf invariant. No initial half simple
connectivity, vanishing half second homology, or framed comparison is assumed.
The whole two-connected boundary case is also proved without any initial
half-connectivity hypothesis, using actual component selection.

Step 7 in full generality remains open. For the candidate-specific two-ended
argument, construct the actual component/half-connected presentation and
identify the original endpoint model and its frame before applying the
checked clopen low-surgery theorem. The restriction and Arf transport
through a supplied actual surgery comparison are no longer missing.
General Arf bordism invariance, stable detection, collapse nullity, and
`SixSphereRigidity` remain unproved.

## Actual filling-state application and boundary cap kernel — checkpoint 16822

`CollaredZeroQuadraticKernel` now applies the checked theorem to the
literal zero fiber and positive half of a `LowCollaredSevenState`, retaining
its actual embedding, full induced frame, retraction, and native atlas.
The full quadratic-kernel conclusion still requires the whole zero boundary
to be two-connected; individual sphere parity does not.

`TimeCollarBoundaryDuality` now proves actual boundary-relative cap duality
for a compact seven-manifold's collared half. It uses the genuine collar
deformation, literal interior/collar open cover, cofinal actual compact
cores, original pair pullbacks, and original support transitions. The
canonical comparison with the true compact-support direct limit is
independent of cutoff, and the resulting duality map is bijective.

`TimeCollarRelativeFundamentalClass` now constructs the actual relative
class by the original pair homology maps and proves independence of core.
`TimeCollarRelativeFundamentalCap` identifies the checked duality map with
cap by that class. Actual local nonvanishing and boundary-puncture homotopy
equivalences give `TimeCollarBoundaryFundamentalClass`: the connecting image
is the genuine fundamental class for any supplied six-dimensional atlas on
the literal boundary. No boundary connectedness is used.
`TimeCollarBoundaryCapKernel` proves self-orthogonality for the actual cap
pairing when boundary and half have zero second integral homology.

These cap results are now applied to the original native zero fiber with
the actual point map and inclusion retained, as described in the next
checkpoint. Cap-kernel self-orthogonality alone does not establish quadratic
vanishing; the original-frame geometric theorem supplies that separately.

## Native Arf and sphere-complement reduction — checkpoint 16866

`TimeCollarBoundaryPairing` and `CollaredZeroCapKernel` identify the actual
cap kernel with the original native zero-fiber geometric polar pairing.
`CollaredZeroArfVanishing` proves Arf zero for the actual induced frame
when the whole zero boundary and the positive half are two-connected.

`NativeBoundarySumHomology` constructs actual component homology maps and
the literal clopen-complement homeomorphism. `CollaredZeroComponentCapKernel`
proves the other component's cap/polar kernel self-orthogonal when the first
component is a topological six-sphere. `ClopenSphereParity` proves exact
raw sphere-operator and parity preservation under the original frame's
clopen restriction. `CollaredZeroClopenQuadraticKernel` then proves full
mod-two kernel vanishing for that restricted original quadratic form,
without connectedness of the whole zero boundary. Finally,
`CollaredZeroClopenArfVanishing` proves Arf zero on the component opposite
a topological six-sphere, assuming that component and the half are
two-connected. This reduction is no longer merely a proposed route.

Next prove preservation of sphere parity, the geometric quadratic form,
and Arf under the actual `StabilizedFramedDiffeomorph` data. Its fixed
ambient and normal isometries and added normal axes must all be retained.
The sphere-dependent source twist cannot be assumed to extend over a disk.
Apply the resulting comparison to the actual low-surgery path and endpoint
clopen component, then connect to the original Hopf and candidate models.
Sixth-stem generation/nontriviality and actual collapse detection remain open.

## Relevant checked sources

- `MiddleHomologyKernelObstruction.lean`
- `EmbeddedTimeIntegralKernelParity.lean`
- `EmbeddedTimeIntegralRelationParity.lean`
- `EmbeddedTimeBoundaryGermParity.lean`
- `SevenDimensionalAttachingTube.lean`
- `TimeCollarPositiveCoreTube.lean`
- `SphereFourTubeRegularTime.lean`
- `SphereFourTubeTimeBands.lean`
- `SphereFourTubeTimeCollar.lean`
- `SphereFourTubeOldZeroFrame.lean`
- `SphereFourTubeRetraction.lean`
- `TimeCollarPositiveCoreComplement.lean`
- `SphereFourTubeHalfRetract.lean`
- `SphereFourTubeExteriorConnectivity.lean`
- `SphereFourTubeHalfCoverMaps.lean`
- `SphereFourTubeHalfImageRelation.lean`
- `SphereFourTubeHalfImageCoordinates.lean`
- `SphereFourTubeOldBoundaryRelation.lean`
- `SphereFourTubeMeridianParity.lean`
- `SphereFourTubeBoundaryQuadraticValue.lean`
- `SphereFourTubeBoundaryImmersion.lean`
- `SphereFourTubeEmbeddedRepresentatives.lean`
- `SphereFourTubeOldSphereParity.lean`
- `SphereFourTubeHalfImageSphereParity.lean`
- `EmbeddedTimeHalfImageSphereParity.lean`
- `EmbeddedTimeTwoConnectedQuadraticKernel.lean`
- `CollaredZeroQuadraticKernel.lean`
- `TimeCollarBoundaryDuality.lean`
- `TimeCollarRelativeFundamentalClass.lean`
- `TimeCollarRelativeFundamentalCap.lean`
- `TimeCollarConnectingCap.lean`
- `TimeCollarFundamentalLocalization.lean`
- `TimeCollarBoundaryLocalHomology.lean`
- `TimeCollarBoundaryFundamentalClass.lean`
- `TimeCollarBoundaryCapKernel.lean`
- `TimeCollarBoundaryPairing.lean`
- `CollaredZeroCapKernel.lean`
- `CollaredZeroArfVanishing.lean`
- `NativeBoundarySumHomology.lean`
- `CollaredZeroComponentCapKernel.lean`
- `ClopenSphereParity.lean`
- `CollaredZeroClopenQuadraticKernel.lean`
- `CollaredZeroClopenArfVanishing.lean`
- `PullbackIntegralHomologyParity.lean`
- `PullbackIntegralSphereMarking.lean`
- `IntegralHomologyQuadraticParity.lean`
- `Wikipedia/HopfProblem/DegreeCollapseTimeCollarPositiveCore.lean`
- `Wikipedia/HopfProblem/DegreeCollapseIntegralSphereRepresentatives.lean`

The last two paths are relative to `src/latest`, not to this directory.
