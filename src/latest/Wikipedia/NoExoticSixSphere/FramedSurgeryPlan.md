# From zero geometric parity to an actual framed surgery trace

## Verified result: unconditional six-sphere rigidity

The requested theorem is proved in `Classification.lean` and exported by
`Wikipedia/NoExoticSixSphere.lean`:

```lean
theorem NoExoticSixSphere.noExoticSixSpheres : SixSphereRigidity.{u}
```

For every type, topology, and independently supplied smooth six-dimensional
atlas, a homeomorphism with the standard six-sphere implies existence of a
genuine smooth diffeomorphism with that sphere. The equivalent theorem
`NoExoticSixSphere.not_isExoticSixSphere` states nonexistence of exotic
six-spheres directly. Neither theorem has a classification or generation
hypothesis.

### Proof assembly

- `SphereValueAlignment` constructs a native sphere diffeomorphism
  homotopic to the identity that moves any specified regular value.
  `RegularSphereFiberTargetChange` retains the actual native fiber and
  every underlying point under this change.
- `RegularFiberAlignedSphereArfObstruction` and
  `StableSixSphereArfSeparationAligned` remove the common-regular-value
  premise from the checked original Arf obstruction.
- `QuaternionicHopfSphereFiberSeparation` applies the original Hopf-product
  Arf invariant one to its actual S16-to-S10 collapse. No replacement
  framed representative is assigned an invariant by assumption.
- `SixSphereCandidateHopfExclusion` retains the original candidate fiber
  under compactification and three suspensions of its S13-to-S7 collapse.
  The resulting same-stage comparison excludes equality with the original
  Hopf-product stable map class.
- `Classification` uses the existing unconditional
  `Wikipedia.HopfProblem.DegreeCollapse.SixthStemMapDichotomy` at the actual
  S16-to-S10 stage. The candidate's third suspension is therefore null.
  The existing original-atlas framed recognition theorem supplies the
  diffeomorphism, proving the requested result at every universe level.

### Verification

The full entry-point and `Wikipedia.NoExoticSixSphere.Audit` build passed
with 13441 jobs and all 17571 dependency axiom audits.
The audit also checks the main theorem against `SixSphereRigidity.{audit_u}`
and against the explicit arbitrary-manifold diffeomorphism statement.

Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`
are permitted by the audit; no additional axioms or admissions were found.
The source scan covers 2827 task files,
8862 local root-import files, and
8865 distinct scanned paths. It found no forbidden proof
shortcuts or option overrides. Lake options are unchanged from HEAD,
including the pre-existing `maxSynthPendingDepth = 3`. No heartbeats,
recursion limits, memory limits, or other computational limits were raised.

The verified log is `audit-17571.log` in the task's check directory.
The final machine-readable report records `main_theorem_proved: true`.

The original goal is complete. The older progress records below describe
earlier, incomplete checkpoints and are retained as history.

## Previous progress records

## Earlier checked milestone — 17547 dependency audits

The unconditional theorem `SixSphereRigidity` remains unproved.
The original attaching torsion comparison and the stable third-stem
group calculation are now proved. The sixth-stem/Arf detection theorem
and unconditional smooth classification remain substantial gaps.

### Checked at checkpoint 17547: two-ended boundary Arf vanishing and genuine stable-class separation

- `CollaredZeroClopenRestrictionIdentification` identifies the restricted
  native zero manifold with the whole original zero manifold when all
  zero points are retained, or with a specified equal clopen zero subset.
  The constructed comparisons retain the embedding and every normal
  column without adding axes.
- `CircleCylinderComponentZeroCases` proves that the actual component
  zero subset is either the full original zero set or exactly the original
  left seam. These are equalities of native open subsets, not just an
  abstract boundary decomposition.
- `CollaredZeroClopenRestrictionArfVanishing` applies whole-boundary
  vanishing in the single-end case and clopen-boundary vanishing in the
  two-end case, returning the result through the actual framed comparisons.
- `CircleCylinderEndpointArfVanishing` proves that a genuine regular
  collared cylinder whose left fiber is two-connected and whose right
  fiber is homeomorphic to the standard six-sphere has zero original left
  geometric Arf invariant. The connected-component case split and the
  actual positive-half fold remove any whole-double connectivity input.
  The right endpoint need not be supplied with a diffeomorphism to the
  sphere or a specified framing.
- `RegularFiberHomotopyArf` constructs that cylinder from an ordinary
  homotopy between the two smooth maps, using the existing relative
  smoothing and endpoint-preserving regularization theorem. Both original
  endpoint maps remain literally unchanged.
- `RegularFiberStableSphereArfObstruction` constructs smooth finite-stage
  representatives of both suspended maps. The original left Arf invariant
  and the right fiber homeomorphism survive. Nonzero original Arf therefore
  obstructs homotopy to the six-sphere-fiber map after every finite number
  of suspensions, when both original maps have the same regular value.
- `StableSixSphereMapEquality` unpacks equality of two actual direct-limit
  classes into a homotopy at a common finite stage. For equal initial
  stages this is a homotopy after the same number of literal suspensions;
  only equal natural-number dimensions are reindexed.
- `StableSixSphereArfSeparation` applies this witness to separate genuine
  stable classes: a nonzero original regular-fiber Arf invariant excludes
  equality with a same-stage map having a topological six-sphere fiber at
  the same specified regular value.

The full entry-point build and axiom audit pass: 17547 dependency audits,
13260 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 20 audited declarations across eight modules.

**Next mathematical work:** align the actual Hopf and candidate collapse
representatives at a common stage and specified regular value, retaining
the original Hopf Arf invariant and the candidate's native fiber. The new
stable-class separation theorem then applies. The common-value and
common-stage hypotheses must be constructed for those original maps, not
silently inferred from an equality of abstract group elements.

Generation of the entire sixth stable stem by the checked order-two class
remains unproved. After the candidate-specific exclusion and generation
are proved, the resulting actual stable identity must be fed into the
existing first-suspension/nullity and native smooth-recognition theorems.
The new results are not an unconditional classification of six-spheres.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17527: original endpoint Arf transport and the actual framed component restriction

- `AffineStabilizedFramedDiffeomorph` retains the genuine fixed ambient
  translation as well as the full normal-column and isometry data.
  `SphereFramedDerivativeAffineComposition` proves that the translation
  disappears from the original framed derivative of an arbitrary smooth
  sphere map, using the existing germ-level chain rule.
- `AffineStabilizedSphereFrameComparison` and
  `AffineStabilizedSphereParity` prove the complete original raw-operator
  comparison and the original twisted-extension/parity equivalence.
  `AffineStabilizedQuadraticTransport` applies the actual induced
  middle-homology map to obtain quadratic and Arf transport. No Arf
  invariance hypothesis is part of the comparison data.
- `DiffeomorphSumClopen` identifies the two original summands with
  native clopen target pieces and identifies the left piece's complement.
  `CircleCylinderClopenEndpoints` applies this to the actual endpoint-sum
  diffeomorphism without changing either endpoint atlas or the zero atlas.
- `CircleCylinderClopenEndpointFrames` retains every original point and
  induced normal column under restriction.
  `CircleCylinderEndpointAffineComparison` constructs the genuine
  two-axis affine framed comparisons with both original endpoint frames.
- `CircleCylinderClopenEndpointConnectivity` derives compactness,
  smoothness, simple connectivity, and vanishing second homotopy of the
  image pieces from the appropriate original endpoint data.
  `CircleCylinderEndpointArfTransport` proves that each original,
  unnormalized endpoint Arf invariant equals the invariant of its actual
  induced clopen seam frame, for independent tubular choices and basepoints.
- `TimeCollarClopenRestriction` proves that clopen membership is constant
  along each collar interval and constructs the literal restricted collar.
  Its boundary is exactly the original boundary points whose zero points
  belong to the subset; the whole boundary need not be connected.
- `LowCollaredStateClopenRestriction` constructs the actual restricted
  framed state and its native zero-atlas diffeomorphism.
  `CollaredZeroClopenRestrictionFrame` identifies the intrinsic gradient,
  outward normal, ordered normal columns, and complete induced six-frame.
  `CollaredZeroClopenRestrictionComparison` packages the genuine zero-axis
  framed comparison and its inverse, without a connected-boundary input.
- `CircleCylinderComponentState` selects the actual connected component
  and proves that its positive half is path connected when the reference
  point has nonnegative time, using the previously checked literal fold.
  `CircleCylinderComponentEndpoints` proves that the component through a
  left seam point contains the entire preconnected left endpoint and either
  all or none of the preconnected right endpoint. Its actual restricted
  boundary is accordingly the full endpoint sum or just the left summand.

The full entry-point build and axiom audit pass: 17527 dependency audits,
13252 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 101 audited declarations, including the new
comparison structure's fields, across seventeen modules.

**Next mathematical work:** apply the established whole-boundary or
clopen-boundary Arf-vanishing theorem to the two component cases. The
original endpoint Arf transport and the full framed component restriction
are now proved, but their native clopen identifications still need to be
assembled in that application. In the two-ended case the relevant
complement must be identified with the original six-sphere endpoint.

The candidate-specific two-ended Arf exclusion is not yet proved. A
genuine regular collared cylinder must also be constructed from the
required stable equality, with the original representatives and regular
values aligned. Generation of the entire sixth stable stem and the
candidate's actual first-suspension nullity remain unproved. These new
transport and restriction results do not assert general framed-bordism
Arf equality or smooth six-sphere classification.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17426: both original endpoint six-frames as signed two-axis stabilizations

- `OrthogonalFramePrepend` proves the complete ordered Gram--Schmidt
  operator identity when an orthogonal column is prepended. A positive
  scale disappears on normalization; the leading position and the
  original tail order are retained.
- `CircleCylinderNormalSourceCoordinates` factors the actual circle
  normal-coordinate map into its literal dimension-change isometry and
  the two original head-coordinate splittings.
- `CircleCylinderSpatialCoordinates` identifies the genuine spatial
  isometry and signed radial unit axes. The original endpoint embeddings
  retain their nonzero constant translations.
- `CircleCylinderOrderedEndpointFrame` and
  `CircleCylinderNormalizedEndpointFrame` identify both full circle-double
  endpoint normal operators before and after ordered normalization.
- `CircleCylinderOriginalEndpointColumns` proves that the retained
  endpoint columns are exactly the original regular-fiber frames, with
  their native atlases and literal dimension-change isometry. Their
  normalization is the original ordered normalization.
- `CircleCylinderTwoAxisCoordinates` constructs actual ambient and
  source isometries for the two-axis stabilization. The leading radial
  column is moved after the original columns with its pole sign intact;
  the appended time column has the outward negative sign on both ends.
- `CircleCylinderBoundaryColumns` proves the full induced boundary
  normal-operator formulas for every tubular retraction, using the
  previously proved intrinsic negative time-normal.
- `CircleCylinderStateSixFrame` applies those identities to the actual
  collared state under its native endpoint-sum diffeomorphism. Both
  complete induced six-frames are signed two-axis stabilizations of the
  original endpoint frames. The fixed source isometry is independent
  of the tubular reference point and equals the original time-normal
  coordinate composition. The point maps remain affine, not linear.

The full entry-point build and axiom audit pass: 17426 dependency audits,
13235 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 59 audited declarations across nine modules.

**Next mathematical work:** construct the native clopen endpoint
restrictions and use the checked full-frame identities in the actual
parity and Arf comparison. The constant translations in the endpoint
embeddings must be handled by the derivative comparison. The framed
restriction to the appropriate connected component is still needed to
apply the established positive-half connectivity and boundary Arf results.

The two-ended Arf comparison remains unfinished. Generation of the entire
sixth stable stem, the required detection or candidate-specific exclusion,
and the candidate's actual first-suspension nullity are still unproved.
The new full-frame identities do not by themselves prove endpoint Arf
equality or smooth six-sphere classification.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17367: the original endpoint normal blocks and signed seam normal

- `CircleCylinderRadialNormal` proves that the actual circle equation
  has canonical orthogonal right inverse `t ↦ (t/2)c` at each unit point.
  The radial vector, scale, and signs of the two actual poles are retained.
- `CircleCylinderEndpointEquations` composes the original endpoint germs
  with the genuine product radial retraction. The full ambient equations
  agree near each endpoint with the ordered product of the circle equation
  and that original endpoint's defining equations. Their actual
  differentials have the corresponding full block formulas.
- `CircleCylinderEndpointFrameBlocks` applies the proved canonical
  right-inverse product identity. Both complete normal operators split
  as the signed radial circle column and the original endpoint frame,
  in the independently constructed native atlases. The actual Euclidean
  frame retains those identities under its fixed coordinate maps.
- `CircleCylinderAmbientTime` identifies the original seam time with a
  linear functional on the actual Euclidean embedding. Its metric-dual
  vector is the genuine unit second-circle-coordinate direction.
- `CircleCylinderSeamGradient` uses the full endpoint frame blocks to
  prove that this vector belongs to the native tangent image at every
  seam point. It is the intrinsic gradient for every tubular retraction;
  the outward normal of the nonnegative half is its negative. This is
  asserted at time zero, not incorrectly on the whole circle collar.
- `GramSchmidtOrthogonalCons` proves that prepending a vector orthogonal
  to every original column leaves the remaining ordered Gram--Schmidt
  columns unchanged. Its normalization lemmas retain the leading column
  and original tail order; arbitrary column permutations are not assumed
  to commute with normalization.

The full entry-point build and axiom audit pass: 17367 dependency audits,
13226 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 38 audited declarations across six modules.

**Next mathematical work:** combine ordered normalization of the actual
radial-plus-endpoint frame with the proved negative time-normal column.
The complete induced seam six-frame must be identified with the original
endpoint frame plus two axes, retaining the explicit dimension changes,
column order, and signs. The endpoint embeddings' constant translations
must then be handled in the actual parity/Arf comparison.

The full two-ended Arf comparison and the required framed clopen-component
restriction are still unfinished. Sixth-stem generation, required Arf
detection or candidate-specific exclusion, and the candidate's actual
first-suspension nullity remain unproved. The new normal-block and gradient
identities do not by themselves assert endpoint Arf equality.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17329: a native two-ended framed collared seven-manifold

- `VectorAugmentedSurjection` proves that a surjective vector-valued
  transverse differential, vanishing on the parametrized tangent space,
  can augment a map that is surjective along that tangent space. No
  extra vanishing of the map on transverse vectors is assumed.
- `ProductSphereAmbient` and `ProductSphereRadialExtension` retain the
  original product-sphere atlas, literal Hilbert-product inclusion and
  actual two-factor radial retraction. The retraction fixes the inclusion;
  the native differential is injective, and the extended differential
  restricts to the original manifold differential.
- `ProductSphereNormEquations` proves that both actual sphere equations
  have independent radial differentials and kill the included tangent
  space. `ProductSphereLevelEquations` combines them with the original
  regular-map equations to prove full ambient regularity, in ordered
  Hilbert normal coordinates.
- `CircleCylinderNormalEquations` specializes those equations to the
  actual doubled map. `CircleCylinderNormalFrame` proves that its literal
  inclusion is a closed embedding and constructs the full smooth normal
  frame as the canonical orthogonal right inverse of those equations.
- `CircleCylinderEuclideanEmbedding`, `CircleCylinderEuclideanEquations`
  and `CircleCylinderEuclideanNormalFrame` retain that construction under
  the fixed Euclidean block isometry and ordered normal coordinates.
  The full Euclidean normal frame has its exact original-equation formula.
- `CircleCylinderLowCollaredState` packages the genuine compact double,
  native atlas, closed embedding, full frame, regular time and explicit
  collar into a `LowCollaredSevenState (Endpoints d)`. Its native zero
  fiber is diffeomorphic to the original endpoint sum by the literal
  inclusions. Neither endpoint is assumed empty and no connectivity or
  Arf-comparison hypothesis is added.
- `OrthogonalRightInverseSourceIsometry` and
  `CircleCylinderFrameCoordinates` prove the exact full normal-operator
  identity under the fixed ambient isometry. The state's frame remains
  tied to the original Hilbert-product equations.

The full entry-point build and axiom audit pass: 17329 dependency audits,
13220 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 71 audited declarations across thirteen modules.

**Next mathematical work:** compare the two induced seam six-frames with
the original endpoint frames. At the original endpoint germs the ambient
equations should split into the circle equation and the original endpoint
equations; the actual outward-time normal must also be identified. The
endpoint ambient inclusions have a constant translation, so a false linear
stabilized-embedding identity must not be substituted.

The componentwise positive-half path-connectedness theorem is proved,
but the framed state still needs its appropriate clopen-component
restriction before applying the boundary Arf argument. The two-ended Arf
comparison, sixth-stem generation, required detection or candidate-specific
exclusion, and the candidate's actual first-suspension nullity remain
unproved. This framed state does not itself prove endpoint Arf equality.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17258: an explicit time collar for the actual two-ended circle double

- `CircleCylinderCollarBranches` constructs the literal circle branches
  `(±sqrt(1-s²), s)`. They have unit norm, are continuous, and retain seam
  time exactly. Their opposite nonzero first coordinates distinguish
  the two sheets; the proved inverse laws recover any point in the band.
- `CircleCylinderCollarWindow` derives one common positive width less
  than one from the original open endpoint neighborhoods. Both clock
  branches stay in those neighborhoods on the whole closed interval.
  The actual doubled map is therefore exactly its corresponding original
  endpoint map along each branch.
- `CircleCylinderClosedCollarMap` pairs each branch with its original
  endpoint fiber. The actual continuous map is injective and covers the
  entire closed time band. At time zero it is exactly the previously
  constructed endpoint-sum inclusion.
- `CircleCylinderClosedCollar` proves compactness of the endpoint sum
  and uses the compact-to-Hausdorff continuous bijection to construct the
  actual closed-band homeomorphism and continuity of its inverse.
- `CircleCylinderTimeCollar` restricts that homeomorphism to the literal
  open time band, producing `timeCollar : TimeCollar (time d) (Endpoints d)`.
  Its coordinate time is the original seam time; its zero points are
  proved equal to the literal left and right endpoint inclusions.

The full entry-point build and axiom audit pass: 17258 dependency audits,
13207 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 58 audited declarations across five modules.

**Next mathematical work:** construct the actual closed Euclidean embedding
and full normal frame of the compact double, then compare its induced seam
frames with the original endpoint frames. Both the explicit collar and
componentwise positive-half path connectedness are now proved. The latter
must still be connected to the restricted framed collared state.

The two-ended Arf comparison, generation of the entire sixth stem, required
Arf detection or candidate-specific exclusion, and the candidate's actual
first-suspension nullity remain unproved. Compactification Arf transport,
the finite-suspension nonvanishing obstruction, and exact order two of the
original sixth-stem square remain proved; the collar does not close those
remaining detection and generation gaps.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17200: positive-half connectivity for the actual circle double

- `CircleCylinderFold` constructs the literal continuous circle fold
  `(c₀, c₁) ↦ (c₀, |c₁|)`. It preserves the circle norm and the original
  clock, hence the actual doubled map. It induces a continuous retraction
  of the native compact fiber onto its nonnegative-time half and fixes
  every point already in that half, including both endpoint images.
- `CircleCylinderPositiveComponent` proves that this fold preserves the
  connected component of any nonnegative-time basepoint. Its restriction
  is a genuine surjective continuous retraction onto the positive half
  of that component. The original regular-fiber atlas makes the component
  clopen and path connected, so its positive half is path connected.
  Neither full-double connectivity nor endpoint connectivity is assumed.

The full entry-point build and axiom audit pass: 17200 dependency audits,
13202 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 30 audited declarations across two modules.

**Next mathematical work:** construct the circle double's explicit time
collar, actual closed Euclidean embedding and full normal frame, then
compare its two induced seam frames with the original endpoint frames.
The componentwise positive-half connectivity requirement is now proved,
but must still be connected to the restricted framed collared state.
The two-ended Arf comparison itself remains unfinished.

The compact native double and native endpoint-seam diffeomorphism remain
proved, as do compactification Arf transport, the finite-suspension
nonvanishing obstruction, and exact order two of the original sixth-stem
square. Generation of the entire sixth stem, the required Arf detection
or candidate-specific exclusion, and the candidate's actual
first-suspension nullity remain unproved.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17170: a compact two-ended circle double with the native endpoint seam

- `CircleCylinderClock` constructs the actual smooth clock on the
  standard circle. Its values are zero and one at the two coordinate
  poles, and its actual manifold differential is surjective elsewhere.
  The proof uses the circle's original tangent space and rotation tangent.
- `CircleCylinderRegularMap` composes the original regular collared
  cylinder with that clock. The endpoint germs prove regularity at the
  two critical clock points; away from them the clock submersion gives
  regularity. Both original endpoint maps are retained literally, and
  neither endpoint fiber is assumed empty.
- `CircleCylinderNativeFiber` constructs the compact native regular
  fiber, of dimension seven when the endpoint dimension is six. Both
  original endpoint fibers have smooth injective literal inclusions
  with disjoint images, retaining their original regular-fiber atlases.
- `CircleCylinderSeam` defines the global smooth time as the second
  circle coordinate and identifies its entire zero set with those two
  endpoint images. The clock stays in the original closed time interval.
  `CircleCylinderSeamDifferential` proves that the circle tangent is
  killed by the original cylinder derivative at the seam and that the
  seam differential is surjective there.
- `RegularFiberTimeSubmersion` lifts genuine kernel tangent vectors
  through the native regular-fiber inclusion. `CircleCylinderRegularTime`
  applies it to prove that the actual seam time is regular on the
  compact doubled fiber, without a new regularity assumption.
- `CircleCylinderEndpointImmersion` and `CircleCylinderEndpointSum`
  prove that the literal endpoint disjoint union is a smooth injective
  immersion onto the full seam. `CircleCylinderZeroDiffeomorph` gives
  the native zero atlas and an actual diffeomorphism from the original
  endpoint sum. Its underlying map is exactly the retained inclusions.

The full entry-point build and axiom audit pass: 17170 dependency audits,
13200 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 78 audited declarations across ten modules.

**Next mathematical work:** construct the circle double's explicit
time collar, actual closed Euclidean embedding and full normal frame,
and compare its two induced seam frames with the original endpoint
frames. The intended componentwise argument must also prove the
required positive-half connectedness; it is not assumed here.
Only then can this double supply the missing two-ended Arf comparison
needed for detection of the candidate collapse.

The compactification Arf comparison, nonvanishing obstruction after
every finite suspension, and exact order two of the original smash
and composition squares remain proved. Generation of the entire sixth
stem, the required zero-Arf detection or candidate-specific exclusion,
and the candidate's actual first-suspension nullity remain unproved.
The new double alone does not assert general disconnected-boundary
Arf invariance or provide the final filling.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17092: compactification Arf transport and nontriviality of the original sixth-stem square

- `DiffeomorphSphereComposition` retains smoothness, injectivity, and
  injective manifold differential for sphere representatives under
  the actual native diffeomorphism.
- `CompactifiedCollapseSphereFrame` combines the prescribed normal
  identity with the actual nonlinear tangent chain rule. It identifies
  the full original raw sphere operator after the fixed normal-coordinate
  change, under the variable augmented ambient equivalence.
- `CompactifiedCollapseSphereParity` uses the proved whole-disk ambient
  equivalence, the fixed normal-coordinate change, and actual normal
  stabilization to transport the original twisted extension criterion.
  Consequently the original geometric sphere parities agree. No
  extension of the moving source twist is assumed.
- `DiffeomorphQuadraticTransport` uses the actual homology map of a
  native diffeomorphism. Embedded sphere representatives and their
  original parity comparison make that map a quadratic isometry.
  `CompactifiedCollapseArfTransport` applies it to the actual compactified
  collapse fiber and removes the target projection chart, recovering
  the original defining-equation Arf invariant with independent tubular
  retractions and basepoints.
- `FramedCollapseStableArfObstruction` chooses the genuine germ-preserving
  smooth representative and derives the new fiber's connectivity from
  its native diffeomorphism. Nonzero prescribed Arf now obstructs every
  finite suspension nullhomotopy of the original framed collapse map.
- `QuaternionicHopfStableNontriviality` applies that result to the
  original Hopf-product frame with its proved Arf invariant one.
  `SixthStemSmashSquare.nativeClass` and `.stableClass` are nontrivial
  and have exact order two. `SixthStemSquareNontriviality` transfers
  nontriviality through the proved smash/composition comparison and
  gives exact order two for `StableThirdComposition.stableSquare` and
  every original native `squareClass k`.

The full entry-point build and axiom audit pass: 17092 dependency audits,
13190 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 28 audited declarations across eight modules.

**Next mathematical work:** prove generation of the entire actual sixth
stem and complete Arf detection, or an equivalent genuine vanishing theorem
for the original candidate collapse. Nontriviality of the original square
and the compactification Arf comparison are now proved. An order-two
element does not prove that the entire sixth stem has order two, and
the checked nonvanishing direction does not prove that zero Arf implies
stable nullhomotopy.

The candidate's actual first-suspension nullity remains unproved. Once
the required nullity is supplied, the checked filling and recognition
construction retains its independently supplied atlas. General
disconnected-boundary Arf invariance has not been asserted.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17064: the actual compactified collapse normal-frame identity

- `CompactifiedCollapseCoordinateGerm` recovers the original finite
  collapse coordinates from the smooth representative's actual germ
  at the compactified core. It uses the original source and target
  projections, and retains the same identity after radial extension.
- `SphereLevelEquationsRadialZero` proves that the actual uncut radial
  extension has zero radial derivative, using only local smoothness.
  `StereographicEquationDifferential` combines this with the actual
  norm equation: the full derivative in augmented coordinates has
  first component twice the radial coordinate.
- `CompactifiedCollapseEquationDifferential` identifies the remaining
  derivative block with the original Euclidean collapse derivative.
  This follows from the actual coordinate germ and chain rule; equality
  of the zero sets alone is not used to identify derivatives.
- `StereographicNormalOperator` identifies the canonical orthogonal
  right inverse of this block derivative using the proved conformality
  and radial orthogonality. `CompactifiedCollapseNormalOperator`
  specializes it to the original prescribed normal frame, with the
  exact tube-radius factor and one-half radial factor.
- `StereographicNormalFrameCoordinates` constructs the fixed normal
  coordinate equivalence that removes those factors. It proves the
  resulting identity with ordinary one-column stabilization under
  the actual variable augmented ambient equivalence.
- `CompactifiedCollapseFiberIdentification` gives the actual native
  fiber diffeomorphism, retaining the source's independently supplied
  atlas. `CompactifiedCollapseFrameComparison.compactifiedFrame_ambient`
  proves that the actual target-chart normal frame, along this
  diffeomorphism and after the fixed normal-coordinate change, is
  exactly the stabilized prescribed frame in augmented coordinates.

The full entry-point build and axiom audit pass: 17064 dependency audits,
13182 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 28 audited declarations across nine modules.

**Next mathematical work:** combine the proved normal-frame identity
with the nonlinear sphere-frame chain rule to identify the full raw
sphere operator. The already proved disk extension of the variable
ambient coordinates then supplies the twisted extension comparison.
Transport the original sphere parity, quadratic form, and geometric
Arf invariant through the actual native fiber diffeomorphism.
The normal-frame identity is proved; the compactification Arf comparison
is not yet proved.

Finite-suspension Arf invariance and its stable non-nullhomotopy
obstruction remain proved. Applying that obstruction to the particular
original Hopf-product class still requires the compactification Arf
comparison. Sixth-stem generation, complete Arf detection, and the
candidate's actual first-suspension nullity remain open. Zero Arf does
not yet imply stable nullhomotopy. General disconnected-boundary Arf
invariance has not been asserted.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 17036: global compactification differentials and disk-extending frame coordinates

- `StereographicReflectionCoordinates` constructs a reflection family
  over the entire original Euclidean space. Its nonzero normal is
  `2 * pole - lift x`, using the actual stereographic convention and
  original pole-complement basis. It sends the pole to the actual
  compactification point.
- `StereographicConformalDifferential` computes the original inverse
  stereographic derivative at every point. It is the reflected original
  inclusion multiplied by the positive factor `4 / (norm squared + 4)`.
  The actual derivative preserves inner products up to the square of
  that factor and is orthogonal to the actual radial sphere vector.
- `StereographicAugmentedDifferential` adjoins that radial vector to
  the actual derivative, producing a globally defined linear equivalence.
  Both it and its inverse vary continuously in operator norm. The final
  coordinates retain ordinary last-axis stabilization order.
- `NormalFrameVariableAmbientCoordinates` proves that an ambient
  equivalence family extending continuously over the actual disk,
  together with its inverse, preserves the original twisted extension
  criterion. The original sphere-dependent source twist is retained;
  its extension is neither assumed nor substituted.
- `StereographicDiskFrameCoordinates` evaluates the actual augmented
  differential on the original smooth ambient extension of a sphere
  map. This gives the required whole-disk family with exact boundary
  values and proves the corresponding extension equivalence.
- `SphereFramedDerivativeComposition` proves the nonlinear chain rule
  for the original quaternionic sphere-frame derivative. It uses the
  actual cutoff extensions' agreement near the sphere, without claiming
  that nonlinear maps commute with those extensions globally.

The full entry-point build and axiom audit pass: 17036 dependency audits,
13173 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 41 audited declarations across six modules.

**Next mathematical work:** identify the actual full defining-equation
normal operator of the compactified collapse with the prescribed old
normal frame under this augmented differential. Then combine that normal
identity with the nonlinear chain rule and the proved disk-coordinate
extension equivalence to transport the original geometric Arf invariant.
The actual normal-frame identity, and hence the complete compactification
Arf comparison, are not yet proved.

Finite-suspension Arf invariance and its stable non-nullhomotopy
obstruction remain proved. Applying that obstruction to the particular
original Hopf-product class still requires the compactification
comparison. Sixth-stem generation, complete Arf detection, and the
candidate's actual first-suspension nullity remain open. Zero Arf does
not yet imply stable nullhomotopy. General disconnected-boundary Arf
invariance has not been asserted.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16995: actual finite-suspension Arf invariance and the stable non-nullhomotopy obstruction

- `RegularFiberNormalIsometry` exposes the actual isometry underlying
  the original dimension-cast regular-fiber normal coordinates and
  proves that its continuous linear equivalence is the original one.
- `SphereSuspensionFrameCoordinates` supplies fixed ambient and normal
  isometries and the exact block-column identity. The calculation is
  separated from the native manifold constructions so that default
  recursion limits suffice.
- `SphereSuspensionFramedComparison` constructs the actual stabilized
  framed diffeomorphism between the two native regular fibers. It adds
  one axis and identifies both the actual embeddings and all normal
  columns. The smooth suspension's germ agreement is retained.
- `SphereSuspensionArfTransport` transports the quadratic form through
  that comparison and then removes both target-chart changes. It proves
  equality of the original defining-equation Arf invariants, with
  independent tubular retractions and basepoints.
- `IteratedSphereSuspensionArf` constructs a smooth representative of
  every specified finite suspension. Its native fiber map is the actual
  iterated equatorial inclusion. Simple connectivity and vanishing
  second homotopy are transported to the new fiber, and the original
  Arf invariant is retained. The base and successor constructions are
  checked separately under the default heartbeat limit.
- `RegularFiberStableArfObstruction` proves that nonzero original Arf
  of a two-connected regular six-fiber rules out nullhomotopy after
  every finite number of actual sphere suspensions, for positive target
  dimension. A nullhomotopy of any such suspension forces the original
  defining-equation Arf invariant to vanish.

The full entry-point build and axiom audit pass: 16995 dependency audits,
13167 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 20 audited declarations across six modules.

**Next mathematical work:** compare the original prescribed collapse
normal frame with the actual regular-fiber defining-equation frame
through ambient compactification. The finite-suspension comparison is
now proved. The compactification comparison is still needed to apply
the new stable obstruction to the original framed Hopf-product class.

Sixth-stem generation, nontriviality of that particular original class,
complete Arf detection, and the candidate's actual first-suspension
nullity remain open. The new result proves the nonvanishing direction
only; zero Arf does not yet imply stable nullhomotopy. The two-ended
candidate argument still needs its actual component/half-connected
presentation. General disconnected-boundary Arf invariance has not
been asserted.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16975: actual target-chart frame invariance and the smooth suspension normal operator

- `CenteredChartDifferentialChange` and `SphereEquationDifferentialChange`
  compute the actual target-chart differential change and its effect on
  the full radial equations, retaining the unchanged norm equation.
- `SphereEquationChartChange` identifies the actual orthogonal right
  inverses in two genuine target charts. `RegularFiberTargetChartFrame`
  constructs the corresponding normal frame on the original native fiber
  atlas and embedding, proves its actual ambient formula, and proves that
  its geometric Arf invariant is unchanged. No orientation or isometry
  hypothesis is imposed on the target chart change.
- `SphereCylinderRadialCoordinates`, `SphereSuspensionTargetChart`, and
  `SphereSuspensionAmbientCoordinates` construct the genuine product
  target chart and compute the original suspension's radial extension.
  Its derivative has the new height column and the old radial block.
- `SphereSuspensionEquationDerivative` adds the actual sphere norm
  equation and proves the full defining-equation block formula.
  `SphereSuspensionSmoothEquationDerivative` transfers that formula to
  the globally smooth representative using its actual agreement near
  the equatorial fiber. Equality of the fiber alone is not substituted
  for equality of the derivative.
- `SphereSuspensionNormalOperator` proves the exact orthogonal right
  inverse formula for the smooth representative: identity in the new
  height direction, and the original orthogonal right inverse in the
  tail. This identifies the actual normal operator in the constructed
  target chart, rather than assigning a model frame to the suspension.

The full entry-point build and axiom audit pass: 16975 dependency audits,
13161 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 49 audited declarations across ten modules.
The combined build also verifies the corrected, noncolliding radial
lemma names; the earlier isolated builds did not detect those collisions.

**Next mathematical work:** package the proved normal-operator formula
with the actual native fiber diffeomorphism and fixed coordinate
isometries into a stabilized framed comparison. Then prove Arf invariance
through finite suspensions. The separate comparison from the original
prescribed collapse frame through ambient compactification is still
required. Apply those results to the original Hopf-product stable class.

Sixth-stem generation, stable nontriviality and complete Arf detection,
and the candidate's actual first-suspension nullity remain open. The
ordinary-nullhomotopy obstruction does not infer nullhomotopy from zero
Arf or stable detection from unstable non-nullhomotopy. The two-ended
candidate argument still needs its actual component/half-connected
presentation; general disconnected-boundary Arf invariance has not
been asserted.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16926: native low-surgery Arf vanishing and the regular-fiber nullhomotopy obstruction

- `ClopenStabilizedFraming` restricts the actual stabilized framed
  diffeomorphism to a chosen native clopen component and its literal image.
  It keeps the original ambient and normal isometries and frame columns.
  Its complementary homeomorphism is the restriction of the actual inverse.
- `ClopenFramedConnectivity` transports the component's simple
  connectivity, second homology, and second homotopy to its image. A
  two-connected component and six-sphere complement supply vanishing
  second homology of the whole boundary without making it connected.
- `CollaredZeroClopenArfTransport` carries final component Arf vanishing
  back along the actual full zero-frame comparison. The original component
  and its restricted induced frame are retained.
- `CollaredZeroClopenLowSurgeryArf` constructs the finite surgery path
  and framed comparison internally. For a path-connected initial positive
  half, a two-connected clopen boundary component opposite a topological
  six-sphere has zero original geometric Arf invariant. Initial half simple
  connectivity or vanishing half second homology is not assumed. Initial
  positive-half path connectedness remains an explicit hypothesis here.
- `CollaredZeroLowSurgeryArf` proves original induced-frame Arf vanishing
  for a two-connected whole zero boundary. Actual component selection and
  low surgeries remove all initial half-connectivity hypotheses in this
  connected-boundary case.
- `RegularEndpointArfVanishing` applies reflection and the canonical
  framed endpoint comparison to a genuine regular cylinder ending in an
  empty fiber. The original two-connected endpoint regular fiber, native
  atlas, and defining-equation frame have geometric Arf invariant zero.
- `RegularFiberNullhomotopyArf` constructs that cylinder from an ordinary
  nullhomotopy, with the left map literally unchanged. Nonzero geometric
  Arf of the original two-connected regular six-fiber therefore obstructs
  ordinary nullhomotopy of the original smooth sphere map.

The full entry-point build and axiom audit pass: 16926 dependency audits,
13151 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 18 audited declarations across seven modules.

**Next mathematical work:** compare the original prescribed collapse
frame with the regular-fiber defining-equation frame through actual
compactification and finite suspension. Apply the new obstruction to the
original Hopf-product stable class. For the two-ended candidate argument,
construct the required actual component/half-connected presentation and
identify its original endpoint model and frame before applying the proved
clopen low-surgery result.

Sixth-stem generation, stable nontriviality and complete Arf detection,
and the candidate's actual first-suspension nullity remain open. The new
ordinary-nullhomotopy obstruction proves one direction only: it does not
infer nullhomotopy from zero Arf, nor stable detection from an unstable
non-nullhomotopy statement. General disconnected-boundary Arf invariance
has not been asserted.

The unconditional target `SixSphereRigidity` remains UNPROVED.


### Earlier checkpoint 16908: stabilized framed transport of the original geometric Arf invariant

- `NormalFrameStabilizationCoordinates` constructs fixed source shuffles
  for adding normal axes before the original tangent columns. It proves
  the exact operator identities through the actual sphere-dependent twist.
- `TwistedNormalStabilization` identifies the stabilized twisted operator
  with ordinary block stabilization under constant disk coordinates. It
  proves equivalence of exact disk extension in both directions, without
  assuming that the moving source twist extends over the disk.
- `NormalFrameAmbientCoordinates` proves that a fixed ambient equivalence
  preserves the original twisted extension condition. Together with the
  existing normal-source comparison, this allows both coordinate changes
  in an actual stabilized framed diffeomorphism.
- `SphereFramedDerivativeLinearMap` proves that the original cutoff
  extension and quaternionic framed derivative commute with fixed
  continuous linear maps.
- `StabilizedSphereFrameComparison` differentiates the given embedding
  identity and uses the actual normal-column identity. It identifies the
  original raw sphere operators, retaining both supplied native atlases.
- `StabilizedSphereParity` proves equality of the original geometric
  sphere parities under the supplied stabilized framed diffeomorphism.
  This sphere-level result does not require the whole manifold connected.
- `StabilizedQuadraticTransport` uses actual embedded representatives to
  prove a quadratic isometry on native mod-two middle homology. Its map
  is the homology map of the given diffeomorphism, not an abstract chosen
  isomorphism. Actual finiteness and polar nondegeneracy then prove
  equality of the original geometric Arf invariants. The endpoint
  manifolds are compact and two-connected; their basepoints and tubular
  retractions may be chosen independently.

The full entry-point build and axiom audit pass: 16908 dependency audits,
13144 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 42 audited declarations across seven modules.

**Next mathematical work:** restrict the actual stabilized surgery-path
comparisons to the relevant native clopen endpoint components. Identify
their restricted original frames with the original endpoint model, and
apply the proved sphere-complement Arf-vanishing theorem to the candidate's
actual bordism. The general stabilized framed transport theorem is now
proved; these component identifications and its endpoint application remain.

General disconnected-boundary Arf invariance, sixth-stem generation and
nontriviality/detection, and the candidate's actual first-suspension nullity
remain open. Stabilized framed diffeomorphism invariance does not itself
prove bordism detection or construct a nullbordism for the candidate.

The unconditional target `SixSphereRigidity` remains UNPROVED.


### Earlier checkpoint 16866: native boundary Arf vanishing and the sphere-complement reduction

- `TimeCollarBoundaryPairing` compares the actual cap kernel with any
  independently charted boundary presentation. Only the auxiliary literal
  boundary subtype receives transported charts; the supplied atlas is kept.
- `CollaredZeroCapKernel` identifies that presentation with the actual
  low-surgery zero fiber, fixing ambient points and the original inclusion.
  On a two-connected zero fiber its cap pairing is the original geometric
  quadratic form's polar pairing, with the actual induced normal frame.
- `CollaredZeroArfVanishing` applies the proved quadratic-kernel vanishing
  and polar self-orthogonality to the original mod-two kernel submodule.
  It proves zero geometric Arf invariant when the zero boundary and
  positive half are two-connected.
- `NativeBoundarySumHomology` gives actual integral component coordinates
  and native mod-two inclusion-sum surjectivity. If the first component's
  middle group is zero, the other component carries every middle class.
  Its clopen-complement homeomorphism has the literal component inclusions.
- `CollaredZeroComponentCapKernel` transfers self-orthogonality to the
  other component's original cap and geometric polar forms. A topological
  six-sphere component supplies the required vanishing homology groups
  directly from its homeomorphism, without changing an atlas.
- `ClopenSphereParity` proves that restricting the original embedding
  and full frame to a native clopen subset leaves the raw sphere operator
  and its original parity unchanged.
- `CollaredZeroClopenQuadraticKernel` proves quadratic vanishing on the
  full mod-two inclusion kernel of a two-connected clopen component.
  The whole boundary may be disconnected. The original coefficient lift
  and even-half-image theorem include nonzero or torsion half-image classes.
- `CollaredZeroClopenArfVanishing` combines those results: a two-connected
  native clopen component has zero geometric Arf invariant for its actual
  restricted induced frame when its complement is a topological six-sphere
  and the positive half is two-connected.

The full entry-point build and axiom audit pass: 16866 dependency audits,
13137 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 44 audited declarations across eight modules.

**Next mathematical work:** transport the geometric parity and Arf
invariant through the constructed stabilized framed comparisons on actual
low-surgery paths, including their ambient and normal-coordinate changes.
Identify the relevant native clopen component and its restricted frame
with the original endpoint model in the candidate's actual bordism.
The sphere-complement reduction is now proved for actual clopen components;
it still must be applied with those endpoint and frame identifications.

General disconnected-boundary Arf invariance, sixth-stem generation and
nontriviality/detection, and the candidate's actual first-suspension nullity
remain open. These boundary vanishing results do not imply stable detection
or a nullbordism for the candidate by themselves.

The unconditional target `SixSphereRigidity` remains UNPROVED.


### Earlier checkpoint 16822: the genuine collared-half boundary class and cap kernel

- `TimeCollarCoreHomology` and `TimeCollarCoreHomologyNaturality` construct
  the actual relative homology equivalences and prove compatibility under
  support restriction, using original pair maps throughout.
- `TimeCollarRelativeFundamentalClass` transports genuine supported
  fundamental classes to the half's boundary pair and proves independence
  of the chosen compact core. `TimeCollarRelativeFundamentalCap` identifies
  the checked duality map with cap product by this actual class.
- `TimeCollarConnectingCap` proves the original connecting-cap square and
  the cohomology-restriction criterion for its capped inclusion kernel.
- `TimeCollarFundamentalLocalization` proves that this relative class
  has nonzero localization at every positive interior point. The actual
  interior-to-half local map is injective because its composite into the
  ambient manifold is the genuine open-neighborhood equivalence.
- `TimeCollarBoundaryLocalHomology` restricts the actual collar push to
  each boundary-point complement. The original puncture inclusion is a
  homotopy equivalence, so the half's local homology at boundary points
  vanishes, in every degree and for all nonzero finite coefficients.
- `TimeCollarBoundaryFundamentalClass` identifies the connecting class
  with the genuine fundamental class for any supplied six-dimensional
  atlas on the literal boundary. This uses local nonvanishing and uniqueness,
  not a normalization hypothesis; boundary connectedness is not assumed.
- `TimeCollarBoundaryCapKernel` proves self-orthogonality of the full
  boundary-to-half middle kernel for the actual cap pairing, assuming
  vanishing second integral homology on the boundary and half. It does
  not assert vanishing of a geometric quadratic form.

The full entry-point build and axiom audit pass: 16822 dependency audits,
13129 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 59 audited declarations across nine modules.

**Next mathematical work:** apply the literal-boundary cap theorem to the
native regular zero atlas of the actual low-surgery states, keeping the
point-identifying homeomorphism and original inclusions explicit. Compare
the cap pairing with the original geometric polar forms, including the
necessary component maps. The full quadratic-kernel theorem is checked for
two-connected native boundaries, not for arbitrary disconnected sums.

The disconnected-boundary quadratic comparison, Arf bordism invariance and
detection, sixth-stem generation and nontriviality, and the candidate's
actual first-suspension nullity remain open. The proposed reduction using
the homotopy-sphere endpoint's zero third homology is not yet proved.

The unconditional target `SixSphereRigidity` remains UNPROVED.


### Earlier checkpoint 16763: actual boundary-relative cap duality for the collared half

- `CollaredZeroQuadraticKernel` applies the checked sphere-parity and
  full two-connected-boundary quadratic-kernel theorems to the literal
  zero fiber and positive half of a `LowCollaredSevenState`. The original
  state embedding, full induced frame, and chosen retraction are retained;
  the state's existing collar and compactness fields supply the data.
- `TimeCollarInteriorCapDuality` follows the actual compact-support cap
  map on the original positive open submanifold by its literal inclusion
  into the half. The constructed collar homotopy equivalence proves that
  inclusion bijective on finite-coefficient homology.
- `TimeCollarCompactCores` constructs the literal boundary and collar
  regions, their actual open cover with the strict interior, and positive
  time-threshold compact cores. These cores are cofinal among all compact
  supports and have the proved inclusion order.
- `TimeCollarBoundaryRetraction` constructs a genuine collar deformation
  by lowering the original time coordinate. It stays in the actual half
  collar, fixes every zero-boundary point, and gives a homotopy equivalence
  whose forward map is the literal boundary inclusion.
- `TimeCollarRelativeCohomology` proves that the original identity pair
  pullback compares boundary-relative and collar-relative cohomology.
  Excision uses the actual interior/collar open cover.
- `TimeCollarCoreCohomology` compares that excised pair with the original
  positive open submanifold by the homeomorphism fixing ambient points.
  Its core-complement map is exact. The resulting forward cohomology map
  is the actual interior-to-half pair pullback.
- `TimeCollarCoreNaturality` proves compatibility with the original
  support transitions and their bijectivity. `TimeCollarBoundaryDuality`
  passes to the genuine compact-support direct limit, proves independence
  of the cutoff, and composes with the actual interior cap map. The resulting
  boundary-relative duality map is bijective in every complementary degree.

The full entry-point build and axiom audit pass: 16763 dependency audits,
13120 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 76 audited declarations across eight modules.

**Next mathematical work:** construct the actual relative fundamental
class for this half, prove that the checked duality map is cap with that
class, and identify its connecting image with the native zero-boundary
fundamental class. Only then apply the cap-kernel criterion and compare
with the original geometric polar pairing. The previous regular-slab
fundamental-class theorem is not a theorem about arbitrary low-surgery
halves. The analogous original pair-map arguments can be applied here,
but have not yet been assembled.

The needed disconnected-boundary comparison, Arf bordism invariance/detection,
sixth-stem generation and nontriviality, and the candidate's actual
first-suspension nullity remain open. The full mod-two quadratic kernel
is proved for two-connected native boundaries, not silently extended to
disconnected ones. A candidate-specific reduction using the homotopy-sphere
endpoint's zero third homology is still only a proposed route.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16687: the full quadratic kernel for a two-connected native boundary

- `SphereFourTubeBoundaryImmersion` proves that the actual tube-boundary
  map is smooth, injective, and immersive into the native regular zero
  atlas. The six-dimensional source model is related to the original
  product smooth structure by the checked identity diffeomorphism.
- `SphereFourTubeEmbeddedRepresentatives` applies native Whitney
  cancellation in that source to obtain embedded sphere representatives
  with the exact original integral marking. Their postcompositions into
  the actual zero boundary remain smooth embeddings and immersions.
  Even-longitude representatives have zero original induced-frame parity;
  the auxiliary source frame is not substituted for the target frame.
- `SphereFourTubeOldSphereParity` proves that the old zero inclusion
  retains the actual raw sphere-frame operator. The twisted-extension
  criterion therefore preserves the original sphere parity, even with
  independent ambient retractions and basepoint choices.
- `SphereFourTubeHalfImageSphereParity` combines the actual integral
  half-image relation with these separated embedded representatives and
  the native annulus theorem. It proves zero original sphere parity for
  a double-core image, comparing the cubical and surgery markings explicitly.
- `EmbeddedTimeHalfImageSphereParity` constructs the positive core tube
  and its two-connected regular collared exterior internally. Every
  embedded old-boundary sphere with an even integral half image has zero
  original parity. The half-image class may be nonzero or torsion; no
  auxiliary exterior or zero half-image obstruction is assumed. Both
  original marking conventions are covered.
- `EmbeddedTimeTwoConnectedQuadraticKernel` applies Hurewicz and embedded
  representatives in the original native boundary, then the exact
  coefficient kernel-lifting theorem. The original quadratic form vanishes
  on the **full mod-two boundary-to-half kernel when the whole native
  boundary is two-connected**. This includes nonzero half-image obstruction;
  it is not restricted to the reduced integral kernel. A disconnected
  boundary is not silently assumed two-connected.

The full entry-point build and axiom audit pass: 16687 dependency audits,
13112 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 21 audited declarations across six modules.

**Next mathematical work:** connect the checked kernel theorem to the
actual framed filling and bordism states. Individual sphere parity is
already handled without connectedness of the whole zero boundary, but a
general relation spanning several boundary components still needs a
quadratic sum comparison. For the candidate-specific argument, first check
whether the homotopy-sphere endpoint's zero third homology reduces the
needed kernel to the other component, before constructing a general
multi-boundary comparison. Native frame and cap-pairing identifications
must remain explicit.

The disconnected-boundary quadratic-kernel argument, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No vanishing of
the half-image obstruction or equality of the full mod-two kernel with
the reduced integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16666: zero quadratic value of the actual even-longitude boundary class

- `IntegralSpherePinchNaturality` proves that postcomposition commutes
  exactly with the actual hemisphere pinch, and constructs representatives
  of two integral source classes with the required common base value.
- `PullbackIntegralHomologyParity` pulls the geometric parity and pairing
  back along a specified continuous map from a two-connected source to
  a compact framed native six-manifold. The target need not be connected.
  Actual source representatives and postcomposed sphere maps give the
  quadratic identity, alternating self-pairing, and invariance under adding
  twice any integral source class. Integer multiples of a zero-parity class
  have zero parity, including negative multiples.
- `PullbackIntegralSphereMarking` explicitly compares the genuine cubical
  sphere generator to the independently marked surgery generator. They
  agree up to sign; proved negation invariance removes that sign in parity.
- `SphereFourTubeBoundaryQuadraticValue` constructs the actual product map
  into the native regular zero fiber and checks its exact half inclusion
  and meridian restriction. The original full outward frame gives zero
  marked-meridian parity. Thus every integral product class whose longitude
  projection is twice the original generator has zero pulled-back parity.
  The result also applies to actual postcomposed sphere representatives.
- `exists_old_boundary_zero_quadratic_relation` combines this calculation
  with the actual Mayer–Vietoris half-image relation. An arbitrary original
  boundary class mapping to twice the marked core has the same new-half
  image as an actual tube-boundary class of zero pulled-back parity. This
  includes torsion core images and disconnected old boundaries. It does
  **not** yet identify the quadratic value of that old boundary class.

The full entry-point build and axiom audit pass: 16666 dependency audits,
13106 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 23 audited declarations across four modules.

**Next mathematical work:** transfer the proved tube-boundary value back
to the original boundary class. The checked native annulus theorem compares
separated embedded sphere representatives with equal integral half images;
the tube-side continuous representative must be replaced with an actual
embedded representative in that component, retaining its class and parity.
A class involving several old-boundary components additionally requires a
genuine quadratic sum comparison, not a single-sphere relation.

The full torsion-sensitive mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No vanishing of
the half-image obstruction or equality of the full mod-two kernel with
the reduced integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16643: zero parity of the actual normal meridian

- `SphereFourTubeMeridianDisk` proves that the actual normal disk
  `v ↦ Φ(s, v)` is smooth, injective, and immersive. Its radial modified-time
  derivative at every unit normal is exactly positive two.
- `SphereFourTubeNativeMeridian` constructs the actual meridian in the
  native regular zero atlas, proves it is a smooth embedding and immersion,
  and identifies its inclusion into the new half with the original
  meridian section of the unit tube boundary.
- `SphereFourTubeMeridianOperator` constructs the original ambient
  normal-plus-derivative operator on the entire four-dimensional disk.
  Its exact restriction is the boundary operator and extends over the
  closed disk. No frame nullhomotopy is assumed.
- `SphereFourTubeMeridianParity` applies the checked signed boundary-germ
  criterion with the actual positive radial derivative and operator
  extension. It proves zero parity for the original full outward induced
  frame on the actual meridian, in the native regular zero atlas. It does
  not require the entire boundary to be connected.

The full entry-point build and axiom audit pass: 16643 dependency audits,
13102 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 15 audited declarations across four modules.

**Next mathematical work:** prove the even-longitude quadratic value and
the genuine comparison with arbitrary old-boundary classes, including sums
across components. One possible route is to pull geometric parity back
along the actual tube-boundary map from `S³ × S³`: Hurewicz representatives
are needed in that two-connected source, not in the whole disconnected
native zero boundary. This pullback calculation is not yet proved. Keep the
cubical and surgery sphere generator markings distinct and compare them
explicitly.

The full torsion-sensitive mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No vanishing of
the half-image obstruction or equality of the full mod-two kernel with
the reduced integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16628: the torsion-sensitive integral half-image relation

- `SphereFourTubeHalfCover` constructs the actual open cover of the old
  nonnegative half by its full core complement and the open unit tube.
  The original core is a section of the tube's actual first projection.
- `SphereFourTubeHalfCoverMaps` constructs the overlap's normal-direction
  map to `S³ × S³` and the radial map into the new half. Both comparison
  identities are exact equalities of continuous maps: overlap retraction
  is the unit boundary map, and overlap core projection is the longitude
  projection. The retraction also retains old-boundary points of time zero.
- `SphereFourTubeHalfImageRelation` applies the actual Mayer–Vietoris
  exact sequence to the kernel pair `(a, -2 • core)`. It constructs a
  unit-boundary class mapping to the retracted class and proves its
  longitude projection is exactly twice the original marked generator.
  No injectivity of the core-to-half homology map is used, so the result
  also applies when the core image is torsion.
- `SphereFourTubeHalfImageCoordinates` uses the actual product homology
  equivalence and original sphere markings to obtain coefficient exactly
  two on the longitude and an unrestricted integral meridian coefficient.
- `SphereFourTubeOldBoundaryRelation` specializes this to an arbitrary
  integral class of the original zero boundary. The old boundary enters
  the core complement by its original points, and radial retraction agrees
  exactly with the previously constructed native old-zero inclusion into
  the new half. A disconnected old boundary is allowed in this homology
  statement; its quadratic sum comparison is not inferred.

The full entry-point build and axiom audit pass: 16628 dependency audits,
13098 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 36 audited declarations across five modules.

**Next mathematical work:** prove zero induced-frame parity for the actual
normal meridian. The disk `v ↦ Φ(s, v)` is a genuine immersion throughout
its four-dimensional domain. Its original normal-plus-derivative operator
should provide the required extension, and its radial modified-time
derivative is positive. Apply the checked signed boundary-germ criterion
to the native regular zero atlas; do not assume the frame is nullhomotopic.
Then prove the even-longitude quadratic value and the genuine comparison
with arbitrary old-boundary classes, including sums across components.

The full torsion-sensitive mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No vanishing of
the half-image obstruction or equality of the full mod-two kernel with
the reduced integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16592: two-connectivity of the actual collared tube exterior

- `SphereFourTubeCore` identifies the literal core with the zero-radius
  tube, proves it compact and closed, and identifies nonzero normal
  coordinates in its actual complement.
- `SphereFourTubeRetraction` constructs a continuous radial retraction
  from the core complement to the closed tube exterior. It fixes every
  exterior point. Continuity across the coordinate target is proved using
  the compact unit tube; no inverse coordinates outside that target are
  assumed continuous.
- `TimeCollarPositiveCoreComplement` applies native compact-image
  avoidance to the actual positive core. Its complement is nonempty,
  simply connected, and has vanishing native second homotopy group.
  The dimension bounds include the cylinder direction, and the old
  half's two-connectivity is transferred through its actual collar.
- `SphereFourTubeHalfRetract` constructs the radial map from that positive
  core complement to the literal new half. The new collar supplies a map
  in the opposite direction. Their composite is exactly the collar-slide
  endpoint, giving an actual homotopy right inverse.
- `HomotopyRetractConnectivity` transfers paths and sphere contractions
  through that specified homotopy right inverse, without asserting that
  the two spaces are homotopy equivalent.
- `SphereFourTubeExteriorConnectivity` proves simple connectivity,
  native `π₂ = 0`, and integral `H₂ = 0` for the actual modified half.
  `exists_two_connected_collared_exterior` constructs its smooth regular
  time and combined collar, retaining the exact half identity and both
  old and new boundary-point formulas. The earlier native frame comparison
  still applies. No torsion-free homology or primitive-image hypothesis
  is used.

The full entry-point build and axiom audit pass: 16592 dependency audits,
13093 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 43 audited declarations across six modules.

**Next mathematical work:** the exact Mayer–Vietoris half-image comparison.
Use the actual open cover of the old half by its full core complement and
the open unit tube. Their overlap is the punctured open tube, on which
radial retraction lands exactly on the unit boundary. A kernel pair should
give a boundary class with longitude projection exactly twice the marked
generator, even when the original core image is torsion. This comparison
is not yet proved; neither is the induced-frame meridian parity or the
disconnected-boundary quadratic sum comparison.

The full torsion-sensitive mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No vanishing of
the half-image obstruction or equality of the full mod-two kernel with
the reduced integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16549: the actual exterior collar and original native boundary frame

- `TimeBandSumCoordinates` joins coordinates on a disjoint open cover
  while retaining the actual time coordinate and both summand labels.
- `SphereFourTubeRadialBand` constructs the actual tube-boundary collar
  with normal radius `sqrt (1 + time)`. Both inverse identities and
  continuity are checked; the permitted time band excludes radius zero.
- `SphereFourTubeOldBand` identifies the old time band with its unchanged
  original collar and proves that it and the radial band form a disjoint
  open cover of the modified time band.
- `SphereFourTubeTimeCollar` constructs the combined collar over
  `B ⊕ (S³ × S³)`. Every old zero point is fixed exactly, and each new
  zero point is its specified unit normal tube point. Together with the
  regular defining function, this gives the actual collared tube exterior.
- `RegularTimeZeroGerm` proves that an inclusion of regular zero sets is
  smooth and locally a diffeomorphism for the independently constructed
  native regular-fiber atlases. Equal ambient time germs give equal full
  induced normal frames, even with independent tubular retractions.
- `SphereFourTubeOldZeroFrame` applies these results to the actual tube
  modification. The old boundary inclusion is a native local
  diffeomorphism and an open embedding with the exact old zero-set range.
  The original full outward induced frame is unchanged there.

The full entry-point build and axiom audit pass: 16549 dependency audits,
13084 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 25 audited declarations across six modules.

**Next mathematical work:** prove two-connectivity of the actual exterior
and its exact Mayer–Vietoris half-image comparison. The existing native
high-codimension image-complement theorems provide the avoidance step;
they still need to be applied to the positive core and combined with an
actual tube-exterior retraction. The meridian's induced-frame parity,
even-longitude quadratic value, and disconnected-boundary sum comparison
also remain unproved. See `HalfImageExcisionPlan.md`.

The full torsion-sensitive mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No vanishing of
the half-image obstruction or equality of the full mod-two kernel with
the reduced integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16524: actual regular tube exterior for integral half-images

- `CompactSphereSmoothOpenTube` and `SevenDimensionalSmoothOpenTube`
  construct an actual smooth four-normal tube inside a prescribed open
  neighborhood. Its normal coordinates have unrestricted source and a
  genuine smooth partial inverse, with the original sphere fixed at the core.
  `TimeCollarPositiveCoreTube` applies this to an actual integral class in
  the two-connected half, preserving the original integral marking and
  keeping the entire tube at positive time.
- `SphereFourTubeRegions` proves compactness and openness for the actual
  radial tube regions, with exact membership tests through the inverse.
  `SmoothManifoldLocalExtension` and `SphereFourTubeCutoff` construct
  globally smooth radial extensions and bounded cutoffs on the original
  manifold; no unweighted inverse-coordinate extension is assumed smooth.
- `SphereFourTubeTimeModification` constructs a globally smooth new time.
  It is exactly squared normal radius minus one on the inner tube and the
  old time outside the larger compact tube. Its transition is positive.
- `SphereFourTubeTimeLevels` identifies the exact new zero set as the old
  zero set plus the unit tube boundary. The new nonnegative half is exactly
  the original half minus the open unit tube. Near every old zero, the two
  time functions agree on an actual neighborhood.
- `SphereFourTubeRegularTime` proves regularity at every new zero. The
  actual radial derivative on the new tube boundary is two; the original
  derivative is retained at the old boundary. `SphereFourTubeTimeBands`
  gives a common positive band width separating the old collar from the
  new tube collar and excluding the compact transition region.

The full entry-point build and axiom audit pass: 16524 dependency audits,
13078 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 29 audited declarations across ten modules.

**Next mathematical work:** assemble the actual time collar of the exterior
over the disjoint union of the old boundary and `S³ × S³`, retaining the
old boundary frame. Then prove exterior two-connectivity and the exact
Mayer–Vietoris half-image comparison. The tube boundary's meridian parity,
its even-longitude quadratic value, and the disconnected-boundary sum
comparison are not yet proved. See `HalfImageExcisionPlan.md` for the
remaining proposed construction; it is not an established kernel theorem.

The full torsion-sensitive mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No vanishing of
the half-image obstruction or equality of the full mod-two kernel with
the reduced integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16495: native boundary parity for separated integral relations

- `EmbeddedTimeAnnulusCollarGerms` constructs both annulus boundary germs
  from the original inward-gradient collar: unit inversion at the inner
  sphere and half scaling at the outer sphere. Both original sphere maps
  are unchanged, both embedded derivatives are injective, and the actual
  radial time derivatives have the required opposite signs.
- `EmbeddedTimePositiveAnnulusCollars` supplies separated cut radii,
  smoothness and positive time on both whole collars, and globally smooth
  ambient extensions agreeing there exactly. No prescribed collar width
  or smooth extension through the inversion's singular origin is assumed.
- `EmbeddedTimeIntegralRelationAnnulus` constructs a native smooth
  positive-time annulus from equality of the actual integral images in
  the two-connected half. Its original boundary maps, boundary immersions,
  and radial time signs are all proved. Unique within-derivatives on the
  actual closed annulus preserve ordinary derivatives through smoothing;
  equality outside the annulus is not inferred.
- `EmbeddedTimeIntegralRelationParity` proves
  `EmbeddedTime.sphereParity_eq_of_separated_integral_relation`.
  Separated embedded boundary three-spheres with equal integral images
  have equal parity for the ORIGINAL outward induced frame. The native
  annulus and its proper generic perturbation are constructed. The full
  boundary need not be connected or presented as two cylinder endpoints.

The full entry-point build and axiom audit pass: 16495 dependency audits,
13068 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 18 audited declarations across four modules.

**Next mathematical work:** extend the actual boundary quadratic argument
to the full mod-two kernel. The new theorem concerns integral relations
between separated embedded spheres; it does not prove every disconnected-
boundary quadratic relation or remove the coefficient obstruction.
A mod-two kernel class can lift to an integral class whose image is twice
a nonzero target class. Its half-image obstruction must be handled, not
assumed zero. A possible next geometric route is recorded separately in
`HalfImageExcisionPlan.md`; that route remains unproved.

Arf bordism invariance/detection, sixth-stem generation and nontriviality,
and the candidate's actual first-suspension nullity also remain open.
No identification of the full mod-two kernel with reductions of the
integral kernel is assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16477: integral-relation annuli with prescribed collars

- `VariableAnnulusCollarSmoothing` installs two ambient collar extensions
  at arbitrary nested radii. Relative smoothing preserves narrower collars
  exactly and keeps every interior point in the specified open target set.
- `TimeCollarInteriorHomotopy` transfers an actual homotopy in the
  nonnegative half into positive time, using the original collar slides
  to restore both prescribed interior endpoint maps exactly.
- `RadialAnnulusGluing` glues a rescaled actual cylinder to two prescribed
  radial collars. The formulas agree exactly at the seams, so the map is
  continuous and retains every collar value and the interior target condition.
- `SphereCollarInversion` checks actual unit inversion: it fixes the
  boundary sphere pointwise, reverses its radial derivative, and has
  injective differential away from zero. A composed smooth ambient
  extension can be extended through zero without changing any annulus value.
- `TimeCollarRadialAnnulus` moves both boundary spheres along the given
  positive collars, transfers their half homotopy into positive time, and
  glues the collars back unchanged. Explicit scalar types avoid expensive
  norm-instance inference; no heartbeat or other limit was increased.
- `IntegralRelationCollaredAnnulus` uses the checked integral Hurewicz
  theorem for the actual two-connected half to construct the required
  initial homotopy from equality of the integral images. With prescribed
  positive collars and their smooth ambient extensions, it constructs a
  smooth positive-time annulus that retains both narrower collars exactly.

The full entry-point build and axiom audit pass: 16477 dependency audits,
13064 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 16 audited declarations across six modules.

**Next mathematical work:** instantiate the prescribed collars with the
native inward-gradient sphere collars. At the inner end use unit inversion;
at the outer end use half scaling. Prove the quantitative collar bounds,
the actual boundary immersion and radial time signs, and retain those
derivatives through smoothing. Then apply the checked annulus parity
comparison. The native geometric assembly and hence the cross-component
integral parity relation are not yet complete.

The torsion-sensitive full mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No identification
of the full mod-two kernel with reductions of integral-kernel classes is
assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16461: actual boundary parity from smooth positive-time annuli

- `BoundaryGermParity` proves the boundary-operator extension criterion
  using smoothness only at the boundary sphere. It does not assume that
  an annulus map extends smoothly through the missing central disk.
- `EmbeddedSignedTimeGraph` and `EmbeddedTimeBoundaryGermParity` identify
  the actual positive- and negative-time graph derivatives and their
  boundary frames. The negative-time case retains the explicit reflected
  normal coordinate; both comparisons use the original outward frame.
- `FourDiskOperatorSourceCoordinates` and
  `EmbeddedTimeBoundaryGermCoordinates` retain the actual operator under
  a fixed invertible source change, including the outer radius-two sphere.
- `EmbeddedTimeAnnulusParity` proves equality of the original boundary
  sphere parities from a proper generic annulus, using the compact
  double-point curve and its even singular count.
- `CompactAnnulusBoundaryImmersion` constructs jointly injective,
  immersive collars from separated embedded boundary spheres. Then
  `EmbeddedTimeSmoothAnnulusParity` constructs the relative generic
  perturbation of a given smooth positive-time annulus, preserving both
  actual boundary derivatives. Positive time excludes boundary ends of
  the double-point closure. Genericity and properness are conclusions,
  not extra assumptions on the original smooth annulus.

The full entry-point build and axiom audit pass: 16461 dependency audits,
13056 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 28 audited declarations across eight modules.

**Next mathematical work:** construct the required smooth positive-time
annulus from equality of the actual integral classes in the two-connected
half, preserving the native gradient collars at both ends. The parity
comparison is proved for such an annulus; its existence from the homology
relation is not yet proved. Cross-component cancellation therefore remains
unfinished.

The torsion-sensitive full mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. No identification
of the full mod-two kernel with reductions of integral-kernel classes is
assumed.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16433: actual induced-boundary parity for integral-kernel spheres

- `TimeCollarDiskExtension` transfers an actual disk extension from
  the nonnegative half into the positive interior, with the prescribed
  interior sphere EXACTLY restored. It uses the original collar homotopy
  and disk homotopy extension, not smoothness of the topological collar.
- `RadialDiskGluing` scales an actual inner disk and glues the prescribed
  outer annulus without changing any annulus value. The sphere-cylinder
  quotient proves continuity at the center; exact seam agreement proves
  continuity at the gluing radius. Interior avoidance is retained.
- `TimeCollarRadialDisk` homotopes the original boundary sphere through
  the actual nonnegative annulus to its inner sphere. It transfers that
  inner sphere's extension to positive time and glues the annulus back.
  Every interior point of the resulting continuous disk has positive
  time, with the original boundary and entire collar unchanged.
- `VariableDiskCollarSmoothing` supplies relative smoothing for any
  positive collar radius. Its actual smooth ambient extension is installed
  before a larger protected radius. This avoids assuming that a geometric
  collar already has a prescribed width or changing its radial derivative.
- `EmbeddedTimeCollaredDisk` assembles those constructions with the
  checked inward gradient collar. A half extension gives a native smooth
  disk with its exact original boundary, positive interior time, strictly
  negative radial boundary time derivative, and an embedded immersive
  outer annulus. Ordinary derivatives are compared using unique within-
  derivatives on the actual closed ball, including its boundary.
  Two-connectedness of the half turns actual integral-kernel vanishing
  into the required initial continuous disk by the checked Hurewicz theorem.
- `EmbeddedTimeIntegralKernelParity` proves
  `EmbeddedTime.sphereParity_zero_of_half_disk_extension` and
  `EmbeddedTime.sphereParity_zero_of_integral_kernel`. The proper generic
  disk is CONSTRUCTED, not assumed: relative perturbation fixes its collar,
  the retained collar gives full off-diagonal double-point regularity,
  and positive time excludes all boundary ends of the actual double-point
  closure. The compact curve parity theorem and exact induced-frame
  comparison give zero sphere parity for the ORIGINAL outward boundary
  frame in the native regular-zero atlas.

The full entry-point build and axiom audit pass: 16433 dependency audits,
13048 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 17 audited declarations across six modules.

**Next mathematical work:** construct the corresponding annuli and prove
cross-component boundary parity relations for the actual filling. The
new theorem concerns an embedded three-sphere whose individual integral
class is killed in the half. It does NOT establish every relation between
classes on different boundary components, nor does it identify the full
mod-two kernel with reductions of integral-kernel classes.

The torsion-sensitive mod-2 quadratic-kernel theorem, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. The new integral-
kernel sphere parity theorem does not establish the collapse vanishing.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16416: actual embedded positive-time sphere collars

- `InwardSphereCollar` constructs a globally smooth Euclidean collar
  from the radial extensions of a sphere map and a transverse vector.
  Its exact boundary differential is the original extension derivative
  minus the defining-function derivative times the transverse vector.
  A covector separating that vector from the original tangent proves
  injectivity; the outward radial derivative is exactly minus twice
  the transverse vector.
- `EmbeddedTimeSphereCollar` uses the ACTUAL inward unit time-gradient
  and original tubular retraction. The collar fixes the prescribed
  sphere in the native regular-zero atlas. Its entire boundary
  differential lies in the original manifold tangent image, so the
  retraction preserves that differential after embedding. The native
  radial time derivative is exactly minus twice the gradient norm,
  hence strictly negative by regularity.
- `RadialBoundarySign` proves the uniform sign step. Compactness
  gives an annulus with negative radial derivative, and the actual
  one-variable mean value theorem along every radial segment proves
  positivity strictly inside the outer sphere.
- `EmbeddedTimeSphereCollarAnnulus` constructs one uniform annulus
  on which the original manifold-valued collar is smooth, injective,
  and immersive after embedding, and every interior point has positive
  time. An actual globally smooth Euclidean map agrees with the embedded
  collar on the whole closed annulus. This is the ambient-extension
  input for relative disk smoothing, not a supplied smoothness assumption
  on the earlier topological time collar.

The full entry-point build and axiom audit pass: 16416 dependency audits,
13042 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 26 audited declarations across four modules.

**Next mathematical work:** extend the inner end of this exact collar
over a continuous disk in the positive interior for each applicable
integral homology-kernel class, glue and smooth relative to the collar,
and perform the proper generic perturbation with double-point control.
The checked collar alone does NOT supply that filling disk. Annulus
fillings and transfer to separately parametrized literal boundaries
must also retain the actual maps and full induced frames.

The full torsion-sensitive mod-2 quadratic-kernel theorem remains open
beyond the checked zero-coefficient-obstruction subgroup. Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. The new collar
construction does not establish the required collapse vanishing.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16390: actual induced-boundary parity from proper generic disks

- `OutwardGraphFrame` proves that an added height-normal column can
  move to a vector on which the time covector is negative, while all
  original normal and derivative columns are retained. The explicit
  complement coefficient remains positive, proving injectivity at
  every intermediate parameter.
- `OutwardGraphFrameHomotopy` constructs the continuous two-stage
  homotopy: first graph the time covector on the derivative columns,
  then move the added height-normal to the specified transverse vector.
  The endpoint is the EXACT combined boundary operator, not an assigned
  parity class. The transverse vector need not extend over the disk.
- `OutwardGraphStabilization` identifies the initial endpoint with
  one ordinary added axis, an explicit source permutation, and the five
  original graph axes. The actual coordinate operations preserve disk
  extendability in BOTH directions in the codimension-three range.
- `OutwardGraphExtension` and `OutwardGraphNormalCoordinates` combine
  those results with arbitrary fixed native normal-model coordinates,
  including a possible reflection. `OutwardGraphParityCriterion`
  identifies the resulting extension obstruction with the ORIGINAL
  geometric sphere parity of a framed hypersurface.
- `EmbeddedTimeCovector` derives the geometric inputs from the actual
  intrinsic gradient: its smooth covector annihilates the actual normal
  frame, represents the native time derivative, obeys the disk-map chain
  rule, and is strictly negative on the actual outward normal.
- `EmbeddedTimeInwardFrame` handles the sign needed by a disk entering
  the nonnegative-time half. Negative time is used for graph height,
  and the intermediate transverse vector is inward. An EXPLICIT last-
  column reflection retains the original OUTWARD boundary frame in its
  native normal model. No framing is silently replaced by its opposite.
- `EmbeddedNegativeTimeGraph` constructs the genuine graph of the
  disk map and negative time. Smoothness, its complete derivative,
  and the positive radial-height condition are derived from the original
  disk and time, not supplied as unrelated operator data.
- `EmbeddedTimeBoundaryParity` proves
  `EmbeddedTime.sphereParity_zero_iff_diskOperator_extends`: it shows
  that the ACTUAL induced outward frame on the native regular-time-zero
  atlas has zero sphere parity exactly when the original disk's normal-
  plus-derivative boundary operator extends. No sphere-map cylinder
  presentation of the ambient seven-manifold is required.
- `EmbeddedTimeGenericDiskParity` applies the constructed punctured-
  disk operator extension and compact double-point-curve parity theorem.
  A proper generic disk with the prescribed boundary and inward collar
  gives zero parity for that ACTUAL induced outward boundary frame.
  The parity-ball system and even singularity count are constructed from
  the generic-jet, collar-immersion, and proper double-point hypotheses.

The full entry-point build and axiom audit pass: 16390 dependency audits,
13038 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 59 audited declarations across eleven modules.
Native tangent-map wrappers and explicit coordinate identities resolve
the dependent-instance elaboration issues without raising any limit.

**Next mathematical work:** construct the required proper collared disks
and annuli from the actual filling homology-kernel classes. The parity
argument now applies to a general framed regular-time-zero hypersurface;
it no longer needs a sphere-map cylinder once the required disk exists.
Existence for all kernel classes is NOT proved by the new criterion.
Transfer to any separately parametrized literal boundary must preserve
the checked native diffeomorphism and complete induced frame.

The full torsion-sensitive mod-2 quadratic-kernel theorem remains open
beyond the checked zero-coefficient-obstruction subgroup. Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. The new generic-
disk parity theorem does not supply the required collapse vanishing.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16331: one-sided framed connectivity with disconnected boundary

- `LowCollaredHalf` and `LowCollaredFilling` construct the ACTUAL
  positive half, its native half-space atlas, full normal frame, and
  literal framed filling directly from a low collared seven-state.
  They require NO connectedness or homology condition on the boundary,
  ambient state, or half. The boundary uses its actual regular-zero
  atlas and the inclusion preserves the original ambient tangent image.
- `LowCollaredFillingBoundaryFrame` constructs the complete induced
  six-frame of that literal filling boundary, including the negative
  unit intrinsic time-gradient. Its outward sign, unit length, tangent
  and normal membership, smoothness, and exact column formula are
  proved without any connectivity hypothesis.
- `LowCollaredFillingFramedComparison` identifies the native zero
  frame with this literal filling-boundary frame by a zero-axis actual
  stabilized framed diffeomorphism. It composes with EVERY finite
  low-surgery path and uses the comparison's exact boundary map in the
  constructed filling. No promoted ambient simply connected state,
  connected seam, or externally supplied frame comparison is required.
- `SquareDouble` constructs the zero set of `t(p) - u²`, with its
  actual projection onto the original nonnegative half and continuous
  square-root section. The double is compact when the ambient state is
  compact. Its two signed sections show it is path connected whenever
  the original half is path connected and meets the zero seam. The
  square-root section is NOT claimed smooth at the seam.
- `SquareDoubleSmooth` proves the equation regular at zero: on the
  seam it uses the original regular time differential, and off the
  seam it uses the nonzero new scalar derivative. It constructs the
  actual boundaryless regular-fiber seven-atlas on the double.
- `SquareDoubleFundamentalGroup` lifts EVERY original loop through
  the actual section. The native compact Morse theorem supplies finite
  generation on the double, and the surjective projection-induced map
  supplies it on the ORIGINAL half. The boundary may be disconnected;
  no simple connectivity of the ambient state or overlap is assumed.
- `LowCollaredFillingConnectivity` now constructs a finite one-sided
  circle/two-sphere surgery path and a genuinely two-connected framed
  filling whenever the initial positive half is path connected and
  the boundary has zero integral H2. Finite generation is PROVED, not
  assumed. The actual final half is simply connected with zero H2 and
  zero native pi2, and the complete original induced boundary frame
  is retained in the constructed comparison.

The full entry-point build and axiom audit pass: 16331 dependency audits,
13027 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 80 audited declarations across eight modules.
The differential calculation uses explicit native real tangent-map
wrappers and equality of the differentiated functions; no instance-search
or recursion limit was raised.

**Next mathematical work:** apply the one-sided construction to the
required genuine two-ended geometry, or extend the existing geometric
parity argument to these actual framed fillings. Initial POSITIVE-HALF
path connectedness remains a hypothesis; boundary connectedness and
fundamental-group finite generation no longer are. A general two-ended
regular slab has not yet been constructed by the new theorem.

The full torsion-sensitive mod-2 quadratic-kernel theorem remains open
beyond the checked zero-coefficient-obstruction subgroup. Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. Neither the
smooth-double finite-generation proof nor the new framed filling theorem
supplies the required collapse vanishing.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16251: coordinate-invariant endpoint Arf and the genuine framed filling comparison

- `NormalFrameSourceCoordinates` proves that every fixed invertible
  change confined to the original normal block intertwines the ACTUAL
  sphere-dependent source twist. It gives equivalent disk extensions
  in both directions. The twist itself is not extended over a disk,
  and no orientation or path condition is imposed on the fixed change.
- `NormalFrameCoordinateParity` constructs genuine smooth frames with
  changed normal-model coordinates and proves invariance of the original
  geometric sphere parity. It also proves normalization invariance,
  including normalization AFTER the coordinate change. It does not
  assert that these two operations commute.
- `GeometricArfNormalCoordinates` uses actual embedded representatives
  to obtain equality of the ORIGINAL middle-homology quadratic forms
  and their geometric Arf invariants. Tubular retractions and basepoints
  may be chosen independently. This is frame-change invariance on the
  same embedding, not arbitrary framed-bordism invariance.
- `ReflectedEndpointFrame` gives the reflected endpoint columns their
  actual canonical normal model. The dimension-only identification
  preserves the ordered columns and commutes with normalization; its
  exact operator identity is checked. The resulting object is a genuine
  smooth normal frame of the ORIGINAL endpoint embedding and atlas.
- `ReflectedEndpointComparison` constructs an actual one-axis
  `StabilizedFramedDiffeomorph` to the initial collared state's complete
  induced six-frame. Its native diffeomorphism and constant signed
  normal-coordinate isometry are explicit. The outward reflection is
  retained. `ReflectedEndpointArf` identifies this canonical source
  frame's quadratic form and Arf invariant with those of the original
  regular sphere-fiber defining-equation frame.
- `ReflectedEndpointFilling` composes that actual comparison through
  every connectivity surgery and the literal filling-boundary map.
  It starts from the genuine canonical endpoint frame, adds exactly
  one axis plus the subsequent comparison's axes, and uses EXACTLY
  the constructed filling's boundary parametrization. No external
  framed comparison is assumed.

The full entry-point build and axiom audit pass: 16251 dependency audits,
13019 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 45 audited declarations across seven new modules
and the dimension-identification helper. Dependent native-atlas instances
are made explicit; the source-twist proof factors continuous-linear-map
composition instead of increasing recursion depth. No debugging trace
remains in the task sources.

**Next mathematical work:** bridge the constructed framed fillings to
the required two-ended geometry, or extend the geometric-parity proof
to the constructed fillings. The current connectivity construction
requires a CONNECTED boundary; it does not supply a general TWO-ENDED
two-connected regular slab. Native half-space geometry can be developed
without imposing ambient simple connectivity, which is not justified
for a double with disconnected seam.

The full torsion-sensitive mod-2 quadratic-kernel theorem remains open
beyond the checked zero-coefficient-obstruction subgroup. Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. The new endpoint
Arf identity does not discharge those gaps. Nonlinear compactification
also cannot be treated as a constant ambient isometry where a comparison
to a prescribed Euclidean collapse frame is required.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16206: original endpoint frames through the full filling construction

- `AmbientLinearTimeGradient` proves that an actual ambient linear
  time coordinate has its representing vector as intrinsic gradient
  whenever that vector lies in the original tangent image. It uses
  the native chain rule and works for every tubular retraction.
- `ReflectedSeamGradient` applies this to the reflected cylinder.
  The whole seam-collar frame has zero time component, proving that
  the positive unit time axis is tangent. The actual intrinsic
  gradient is that axis, and the induced outward normal at zero is
  its NEGATIVE. The sign is proved, not chosen afterward.
- `GramSchmidtIsometry` proves naturality of the recursive and
  normalized Gram--Schmidt columns under ambient linear isometries,
  and hence of the actual rectangular normalized operator. It does
  NOT assert naturality under arbitrary source-column changes.
- `ReflectedSeam.endpointColumns_eq_originalFrame` identifies the
  endpoint columns with the ORIGINAL regular sphere-fiber frame
  precomposed by an explicit fixed normal-coordinate equivalence.
  These columns are injective and span the actual endpoint normal
  space. This coordinate change occurs BEFORE normalization.
- `ReflectedSeam.zeroColumns_seam` identifies the complete induced
  seam columns with one ordinary coordinate-block stabilization of
  those normalized endpoint columns, precomposed by the explicit
  last-column reflection. `referenceState_sixFrame` proves the
  corresponding formula for the ACTUAL initial collared-state frame
  and its native endpoint-to-zero diffeomorphism, in the actual
  six-dimensional normal model. Its embedding appends zero time.
- `ReflectedSeam.endpointFilling` parametrizes the actual constructed
  filling by the ORIGINAL endpoint regular-fiber atlas. The checked
  `endpoint_boundary_frame` formula composes the initial comparison
  with every connectivity-surgery stabilization and the literal
  filling-boundary comparison. The existence theorem constructs the
  comparison data and proves the actual filling simply connected
  with zero pi2; no initial frame comparison or surgery path is assumed.
- `TwoConnectedCollapseFilling` now uses this stronger endpoint
  construction. The actual finite-nullhomotopy filling theorem keeps
  its original statement and passes the regression build. The finite
  collapse nullhomotopy remains an INPUT, not a proved vanishing result.

The full entry-point build and axiom audit pass: 16206 dependency audits,
13012 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 31 audited declarations across six new modules
and the shared framed-diffeomorphism helper. A default recursion-depth
failure in the final dependent comparison was resolved by factoring the
block identity and explicitly unfolding local aliases, without raising
any limit. No debugging trace remains in the task sources.

**Next mathematical work:** use the retained coordinate changes and
normalization in the needed geometric-parity/Arf comparison. An arbitrary
source-column change cannot simply be moved through Gram--Schmidt.
Where a comparison to the original Euclidean collapse frame is needed,
the nonlinear compactification must be handled by the appropriate
framed homotopy or naturality result, not by a constant ambient isometry.

The constructed filling still has a CONNECTED two-connected boundary;
it is not the general TWO-ENDED two-connected regular slab used by the
existing parity argument. That geometric bridge, or a genuine extension
of the argument to the constructed framed fillings, remains necessary.
The full torsion-sensitive mod-2 quadratic-kernel theorem remains open
beyond the checked zero-coefficient-obstruction subgroup. Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity are still unproved.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16175: actual filling-boundary frames and compatible two-connected fillings

- `FramedEmbeddingReparametrization` pulls an actual embedding and its
  complete ambient normal frame along a specified native diffeomorphism.
  The native chain rule and the diffeomorphism's invertible differential
  prove equality of the actual tangent images and normal projections.
  No replacement atlas or assumed normal-space equality is used.
- `CollaredFillingBoundary.embedding` is the literal restriction of
  the constructed filling's inclusion to its actual boundary, in the
  existing native boundary atlas. Its outward normal is smooth, has
  norm one, belongs to the filling's actual tangent image and the
  boundary's actual normal space, and has strictly negative time
  derivative through the constructed tubular extension.
- `CollaredFillingBoundary.normalFrame` is a genuine full smooth
  orthonormal range frame of that boundary embedding. Its ambient
  operator is exactly the filling's orthonormalized seven-frame with
  this outward normal appended, in the actual codimension coordinates.
  Thus the construction identifies the induced boundary frame, not
  merely a diffeomorphic abstract six-manifold.
- `CollaredFillingBoundary.promotionComparison` carries the
  final low-surgery state's induced zero frame to the promoted
  filling's literal boundary. It adds NO axes, uses the identity
  ambient and normal isometries, and preserves the actual underlying
  point. The complete outward column is retained.
- `fillingOfComparison` constructs the actual `FramedSevenFilling`
  using precisely the comparison's native boundary diffeomorphism.
  Its seven-frame is unchanged. The checked boundary-column equation
  identifies all its induced columns with the stabilized original
  zero-boundary frame under the constructed constant isometries.
- `CollaredFillingConnectivity.exists_twoConnected_framed_state` now
  composes the entire connectivity-surgery comparison with this
  promotion comparison. `exists_twoConnected_framed_filling` retains
  those data together with the actual filling's simple connectivity
  and zero native pi2. The older unframed boundary-diffeomorphism and
  two-connected filling APIs are derived from this stronger result.
  Their statements are unchanged and the regression build passes.

The full entry-point build and axiom audit pass: 16175 dependency audits,
13006 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 31 audited declarations across three new modules
and the strengthened filling-connectivity module. All native atlas and
model instances are made explicit where needed; no limits were raised.

**Next mathematical work:** compare the initial reflected-cylinder
induced six-frame with its original endpoint-fiber frame, with the
outward sign retained, then use the appropriate existing framed
comparisons to the prescribed collapse data. The constructed filling
still has a CONNECTED two-connected boundary and is not the general
TWO-ENDED two-connected regular slab used by the existing parity proof.
That genuine geometric bridge or a generalization remains necessary.

The full torsion-sensitive mod-2 quadratic-kernel theorem remains open
beyond the checked zero-coefficient-obstruction subgroup. Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. Collapse nullity
already implies the required diffeomorphism in the original atlas, but
the vanishing input has not been discharged.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16144: full framed comparison through the connectivity-surgery paths

- The induced zero frame is now proved independent of the auxiliary
  ambient point used to choose its tubular retraction and normal-model
  dimension coordinates. Equality of source time functions also gives
  equality of the actual induced columns at the same original point.
- `CollaredSeamSixFrame.perform_sixFrame` applies the complete single-
  surgery six-frame theorem to the ACTUAL collared-state fields and its
  native zero diffeomorphism. The source time equality is discharged by
  the actual time data; no frame comparison is supplied as an input.
- `CollaredZeroReversalFrame` identifies the reversed state's outward
  normal with the negative original normal. The full six-frame changes
  by the explicit last-column reflection, conjugated into its actual
  normal-coordinate model. `CollaredZeroComponentFrame` proves exact
  frame agreement under the inherited component zero diffeomorphism,
  including independently chosen tubular retractions and the actual
  orthonormalization of the restricted original seven-frame.
- `FramedBlockAssociativity` proves the exact Euclidean block identities
  for composing the ambient zero inclusions and all frame columns.
  `StabilizedFramedDiffeomorph` packages a NATIVE smooth diffeomorphism,
  a number of added axes, and constant ambient and normal isometries
  satisfying the actual embedding and frame equations. Its composition
  constructs one endpoint comparison with the sum of the added axes.
  Comparisons with no added axes can be inverted without stabilization.
- `CollaredZeroFramedComparison` constructs these data for surgery,
  signed reversal, and component restriction. `CollaredZeroFramedPath`
  composes them along every finite actual low-surgery path, including
  the reversal used before a path on the other half. The result is an
  endpoint framed diffeomorphism, not only a list of step hypotheses.
- `CollaredFramedConnectivity.exists_twoConnected_state` constructs a
  final native low-collared state whose two halves are simply connected
  and have zero second integral homology, with zero native positive-half
  pi2 and a complete stabilized framed comparison from the ORIGINAL
  induced zero boundary. It includes the actual component selection,
  both fundamental-group paths, both H2 paths, and their signed time
  reversals. Its boundary need only be simply connected with zero H2;
  neither spherical boundary nor middle-homology vanishing is assumed.
- The existing `CollaredFillingConnectivity.exists_twoConnected_state`
  now derives its native diffeomorphism from this stronger constructed
  framed comparison, followed by the native promotion diffeomorphism.
  Its filling API and the finite-collapse-nullity filling theorem retain
  their previous statements and pass the regression build.
  The proved boundary H1 vanishing is shared by the connectivity
  construction and the native promotion step.

The full entry-point build and axiom audit pass: 16144 dependency audits,
13003 build jobs, and no additional axioms, admissions, or computational-
limit changes. This adds 57 audited declarations, including the new
comparison structure's constructor and fields, across eight new modules
and the strengthened existing modules. Explicitly named local atlas
instances avoid import collisions. A default recursion-depth failure in
the state comparison was resolved by factoring the inverse-column
packaging into a generic constructor, without changing the limit.

**Next mathematical work:** compare the initial reflected-cylinder
induced six-frame with the prescribed original collapse frame, including
coorientation. Identify the induced state-zero framing with the boundary
framing of the promoted actual filling. The general filling result still
uses a CONNECTED two-connected boundary and returns `FramedSevenFilling`;
it does not itself supply the general TWO-ENDED two-connected regular
slab required by the existing slab-parity argument. That geometric
comparison or a genuine generalization is still needed.

The full torsion-sensitive mod-2 quadratic-kernel theorem remains open
beyond the checked zero-coefficient-obstruction subgroup. Arf bordism
invariance/detection, sixth-stem generation and nontriviality, and the
candidate's actual first-suspension nullity remain open. The already
checked collapse-nullity-to-original-atlas-diffeomorphism theorem gives
the final recognition step, but does not discharge these vanishing inputs.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16087: induced six-boundary frames and their exact single-surgery comparison

- `EmbeddedTimeGradient` constructs the intrinsic ambient time-gradient
  by differentiating a genuine tubular extension and projecting to the
  actual tangent image. It is smooth, represents the original native
  time differential, is nonzero at regular points, and is independent
  of the tubular retraction. Its uniqueness is proved from those native
  differential pairings.
- `RegularTimeZeroEmbedding` constructs the actual restriction of the
  original embedding to the native regular-fiber atlas. The inclusion
  differential is injective, its image lies in the original tangent
  image, and the time-gradient is orthogonal to it.
- `RegularTimeZeroColumns` appends the NEGATIVE unit time-gradient to
  the original orthonormal normal columns. The resulting columns are
  smooth, orthonormal, and span the full actual zero-fiber normal space.
  The extension differential on the new column is minus the gradient
  norm, proving the outward sign for the nonnegative time half.
- `RegularTimeZeroNormalFrame` reindexes these columns into the actual
  zero embedding's normal model and constructs a genuine smooth range
  frame. The frame is independent of the chosen tubular retraction.
  `CollaredZeroNormalFrame` specializes this construction to the actual
  native zero atlas of a collared seven-state, constructing the tubular
  retraction from the state's existing embedding and normal frame.
- `EmbeddedTimeNaturality.gradient_natural` compares gradients under
  actual native local-diffeomorphism parametrizations whose embeddings
  and time functions agree through an ambient linear isometry. It
  differentiates those identities; no gradient or tubular compatibility
  is assumed. Negating time is also proved to negate the gradient.
- `LowSurgerySeamGradient` applies that theorem on the actual retained
  open time neighborhood. The new gradient, and the actual outward
  column under the native zero-fiber diffeomorphism, are precisely the
  old vectors with zero ambient coordinates appended.
- `OrthogonalFrameAppendStabilization` proves the exact isometric
  column extensions and the permutation moving the time-normal before
  the new coordinate axes. `LowSurgerySeamSixFrame.zeroColumns_zero`
  compares the FULL induced six-boundary columns for a single native
  surgery, not merely the seven-dimensional state frame.
  `LowSurgerySeamSixFrame.normalFrame_zero` proves this comparison in
  both actual zero embeddings' own normal models, with an explicit
  constant isometric column change. The original negative height sign
  remains part of this change.

The full entry-point build and axiom audit pass: 16087 dependency audits,
12995 build jobs, and no additional axioms, admissions, or computational-
limit changes. This checkpoint adds 76 audited declarations in nine new
modules. Native derivative wrappers and explicit Euclidean coordinate
types avoid deep implicit conversions. A default recursion-limit failure
in the final frame comparison was resolved by smaller algebraic lemmas
and componentwise congruence, not by increasing the limit.

**Next mathematical work:** lift the single-surgery six-frame theorem to
the actual collared-state operations, including reversal and component
restriction, and compose the comparisons along the finite surgery paths.
Compare the initial reflected-cylinder induced six-frame with the
prescribed original collapse frame, including its coorientation. The
general two-connected output is still `FramedSevenFilling`, not the
two-ended `RegularCollaredCylinder` or `FramedSlabData` required by the
existing slab-parity argument; that geometric comparison or a genuine
generalization is still needed.

The full mod-2 quadratic-kernel theorem, including the unresolved middle
torsion/coefficient obstruction, remains open beyond the checked
zero-coefficient-obstruction subgroup. Arf bordism invariance/detection,
sixth-stem generation and nontriviality, and the candidate's actual
first-suspension nullity also remain open. The already checked
collapse-nullity-to-original-atlas-diffeomorphism theorem supplies the
last recognition step, but none of these vanishing inputs.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 16011: two-connected fillings and exact native seam-frame formulas

- `OrthogonalFrameAppendReflection` constructs the actual Euclidean
  last-column reflection and proves that negating an appended column is
  precisely precomposition by this fixed isometry.
- `LowSurgerySeamFrame` identifies the actual new-end normal frame on the
  whole retained time neighborhood with the old orthonormal frame plus
  the added coordinate axes. Its constant column change includes the
  native normal-model coordinates, the NEGATIVE height sign, and the
  exact end-column permutation. The ambient embedding is literally the
  old embedding with zero coordinates appended. Both formulas hold at
  the native zero-fiber diffeomorphism as well.
- `CollaredSeamFrame` proves these formulas for the ACTUAL embedding and
  normal-frame fields of the constructed low-surgery states. The output
  frame is orthonormal. Time reversal retains the same seven-dimensional
  normal frame, and restriction to the actual boundary component retains
  every ambient frame column. All comparisons use the original native
  zero-atlas diffeomorphisms, not an arbitrary homeomorphism.
- `CollaredFillingConnectivity.exists_twoConnected_state` constructs the
  needed low-surgery paths for a supplied compact framed collared state
  whose boundary is simply connected and has zero H2. Boundary H1
  vanishing is derived through the actual first Hurewicz isomorphism.
  The actual component is selected; circle surgeries clear both half
  fundamental groups, and two-sphere surgeries clear both H2 groups.
  The positive half's native pi2 is then zero by the actual second
  Hurewicz theorem. No initial half-connectivity hypothesis is assumed.
- `CollaredFillingConnectivity.exists_twoConnected_filling` supplies the
  resulting genuine compact normally framed manifold with boundary,
  closed smooth immersive Euclidean inclusion, and an entire-boundary
  diffeomorphism from the original zero atlas. Neither spherical boundary
  nor vanishing, finiteness, or torsion-freeness of H3 is assumed.
- `FramedCollapseData.exists_twoConnected_filling_of_finite_null` starts
  from the actual framed collapse of a simply connected smooth six-
  manifold with zero H2. A finite ordinary nullhomotopy constructs the
  initial cylinder; reflection and the actual low surgeries then construct
  a two-connected normally framed filling of the ORIGINAL smooth atlas.
  The finite nullhomotopy remains a hypothesis, not a proved consequence
  of the candidate's zero Arf invariant.

The full entry-point build and axiom audit pass: 16011 dependency audits,
12986 build jobs, and no additional axioms, admissions, or computational-
limit changes. This checkpoint adds sixteen audited declarations in five
new modules. One direct coordinate reduction hit the default recursion
limit; explicit coercion rewrites and congruence replaced that reduction.
The limit was not changed. Explicit intermediate instances also keep the
Hurewicz argument within the unchanged synthesis settings.

**Next mathematical work:** compare the actual INDUCED six-dimensional
boundary framing across the entire low-surgery construction and the
initial cylinder identification. The checked formulas concern the
seven-dimensional state normal frames at their seam; they are not yet
the complete prescribed six-frame comparison. Remove the required middle
torsion and prove full quadratic-kernel vanishing beyond the already
proved zero-coefficient-obstruction subgroup. The current filling result
has a connected, two-connected boundary; it does not by itself construct
the two-connected general TWO-ENDED regular slab used in the separate
bordism comparison. The output is `FramedSevenFilling`, not a reconstructed
`RegularCollaredCylinder` or `FramedSlabData`; using the existing slab-parity
theorems requires an additional geometric comparison or generalization.

Arf bordism invariance/detection, sixth-stem generation and nontriviality,
and candidate first-suspension nullity remain open. Checkpoint 15995
already proves that the last nullity statement implies the exact requested
original-atlas diffeomorphism. The unconditional target `SixSphereRigidity`
remains UNPROVED.

### Earlier checkpoint 15995: original-atlas recognition from actual collapse nullity

- `FramedCollapseRecognition` connects the existing native framed-filling
  recognition to an arbitrary candidate's independently supplied smooth
  atlas. A finite ordinary nullhomotopy of its ACTUAL framed collapse
  constructs a genuine regular collared cylinder and an original-atlas
  endpoint diffeomorphism. The existing seven-dimensional surgery chain
  supplies connectivity reduction, homology reduction and smooth sphere
  recognition for that supplied filling. Their composition is an actual
  diffeomorphism from the original candidate to the standard six-sphere.
- The imported theorem
  `ReflectedCylinder.nonempty_endpoint_sphere_diffeomorph_of_framed_filling`
  is in `DegreeCollapseNativeFramedFillingRecognition.lean`. Its initial
  cylinder remains a genuine input. No initial filling is inferred merely
  from the candidate's homeomorphism or its vanishing Arf invariant.
- `SixSphereStableRecognition` applies this connection to the candidate's
  constructed S13-to-S7 collapse. Identity of its actual stable class now
  implies the required diffeomorphism. Equivalently, nullity of the FIRST
  ordinary suspension suffices, using the previously proved finite-stage
  detection theorem. No stabilization injectivity at the S7 stage or
  nullity of the unsuspended collapse is assumed.
- `sixSphereRigidity_of_collapse_suspension_nullhomotopic` assembles the
  exact universe-polymorphic target from that vanishing input for every
  candidate. This theorem is explicitly CONDITIONAL: the uniform first-
  suspension nullity hypothesis has NOT been proved.

The earlier eight-dimensional trace work is also fully checked:

- `FramedAttachingDimension` derives the correct tangent dimension from
  the actual attaching tube differential, without a dimension hypothesis.
  The collar and handle superlevel atlas constructors work in arbitrary
  transverse dimension; the six-dimensional interfaces are retained.
- Nineteen existing trace modules now work in the actual manifold
  dimension without global compactness. The unchanged cylinder uses the
  original atlas; the handle and rounded collar use their actual regular
  superlevel atlases. All coordinate changes are proved smooth on the
  actual overlaps, and the ambient subtype topology is retained.
- `RoundedTraceDifferential` proves the actual global inclusion immersive.
  `RoundedTraceNormalFrame` proves the glued smooth orthonormal frame spans
  its full normal space, including boundary points, and agrees exactly
  with each prescribed piece frame.
- `EuclideanEmbedding.exists_framedTrace_of_dimension_seven` constructs
  the actual smooth eight-dimensional trace and full normal frame from
  the original seven-manifold embedding, its frame and a smooth embedded
  immersive three-sphere. Global compactness is not assumed. The trace
  itself does not yet identify all induced ends in this generalized API.

The full entry-point build and axiom audit pass: 15995 dependency audits,
12980 build jobs, and no additional axioms, admissions, or computational-
limit changes. Relative to checkpoint 15986, this adds nine audited
declarations, including two generic atlas constructors, in four new
modules and the generalized existing modules.
Four retained six-dimensional boundary modules needed explicit transverse-
dimension annotations after the regression build exposed ambiguous arguments.
The newly imported native surgery dependencies are included in the source
scan and in the dependency-axiom checks of the recognition theorem.

**Next mathematical work:** prove that the first ordinary suspension of
each candidate's constructed S13-to-S7 collapse is nullhomotopic. The
candidate's original geometric Arf invariant is already proved zero, but
the bridge from that invariant to its actual stable class remains open.
The planned route still needs full quadratic-kernel vanishing beyond the
zero-coefficient-obstruction subgroup, the required framed-bordism/Arf
comparison, and sixth-stem generation and detection. The supplied-filling
recognition now closes the post-nullhomotopy diffeomorphism step; it does
not discharge any of those vanishing inputs. Its boundary-atlas recognition
must also not be mistaken for all prescribed-frame comparisons needed in
the separate general framed-bordism argument. The imported final recognition
uses a spherical boundary; its torsion reductions do not automatically apply
to general two-ended bordisms with nonzero middle boundary homology.

The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15986: closed framed attachment and supported rounding in dimension eight

- `UniformHeightAvoidance` proves a uniform short-height separation from
  the ENTIRE old ambient space for a compact family disjoint from it.
  `AttachingCylinderIntersection` applies this to the inner handle and
  proves the exact cylinder-handle intersection without global compactness.
- `ManifoldHeightCylinder` and `SmoothManifoldHeightCylinder` now support
  arbitrary manifold dimension. The original cylinder, all closed slabs,
  and every height slice are closed embedded without assuming the original
  manifold compact. The native derivative and full actual normal range
  are computed with the original embedding and original atlas.
- `ClosedNoncompactAttachment` proves the attachment quotient is the
  actual ambient union when the old subspace and attaching map are closed.
  `UnroundedSurgeryTrace` constructs that closed union in arbitrary
  dimension. Compactness is asserted only when the original manifold
  actually is compact; it is not needed for the quotient homeomorphism.
- `UnroundedTraceFrame` descends the matching original and handle columns
  through the actual CLOSED quotient map. They are continuous and
  orthonormal, with the full derivative-normal range on both pieces.
  `UnroundedTraceOriginalSlices` proves that original slices are closed
  embedded and that positive-height slices miss the handle and retain the
  exact original trace columns. These columns are not yet the full induced
  boundary frame, which also needs the outward boundary direction.
- `EuclideanEmbedding.exists_unroundedTrace_of_dimension_seven` constructs
  all of these data from the original seven-manifold embedding, its given
  normal frame, and a smooth embedded immersive three-sphere. No pre-existing
  attaching product, trace, or global compactness is supplied as a hypothesis.
- The tube, radial collar, common smooth collar sheet, and exact concave
  corner-domain proofs now work with FOUR transverse directions and retain
  the original atlas. The sheet's native derivative is injective and its
  prescribed original columns span the actual normal space.
- `RoundedHandleCorner` now proves supported rounding and regularity for
  arbitrary transverse dimension. The actual rounding parameters are
  constructed inside the available height and radial margins.
  `RoundedSurgeryTrace` proves the added region is compact, the whole union
  is closed, and its exact collar domain is the regular smooth superlevel.
  Positive-height points are unchanged, without assuming global compactness.
- `EuclideanEmbedding.exists_roundedAttachment_of_dimension_seven`
  assembles the actual supported rounding, smooth embedded collar sheet,
  and its regularity from the same original geometric inputs. This is a
  constructed rounded ambient SET, not yet a globally charted or globally
  framed eight-dimensional boundary manifold.

The full entry-point build and axiom audit pass: 15986 dependency audits,
10044 build jobs, and no additional axioms, admissions, or computational-limit
changes. This checkpoint adds 13 audited declarations in five new modules
and the generalized existing modules. Twelve existing modules were generalized;
one retained six-dimensional boundary proof received an explicit dimension
annotation after the regression build exposed an ambiguous implicit argument.

**Next geometric work:** construct the global eight-dimensional smooth
boundary atlas, prove the full global normal frame across the rounded
overlaps, and identify the induced end framings in the original atlas.
The existing atlas and end-framing chain is still six-dimensional. Its
model-space dimensions and compactness assumptions must be handled explicitly.
The surgery's homology effect, relative end preservation, and filling torsion
control are not supplied by the set-level rounding or piecewise framing.

**Still missing overall:** full quadratic-kernel vanishing beyond the proved
zero-obstruction subgroup; actual framing-preserving connectivity surgeries
and the required two-connected framed filling; Arf bordism invariance and
detection; sixth-stem generation and nontriviality; the candidate collapse's
required first-suspension nullity; and the final original-atlas diffeomorphism.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15973: full original framing on the eight-dimensional attaching collar

- `CompactRadialSphereTube` and `PrescribedCompactCollarFrame` construct
  the original manifold's actual normal frame, with the five graph axes,
  over the radial compact-tube collar. The family is orthonormal and smooth
  on the genuine tube domain away from the radial origin. It retains the
  prescribed sphere and zero-section values exactly.
- `CompactCurvedCollarDerivative` proves that the actual corrected product
  and the curved collar model have the SAME ordinary derivative on the
  outer closed-disk collar, including the sphere boundary. The argument
  uses unique within-differentiability; it does not assume that equality
  on the closed disk extends to an ambient open neighborhood. The original
  frame is therefore normal to the actual corrected product.
- `GlobalCompactCollarFrame` smoothly extends the prescribed frame while
  retaining a protected annular product. `CompatibleCompactCollarFrame`
  installs that frame on a whole thinner collar and proves it spans the
  actual derivative-normal space everywhere on the retained closed product.
  The corrected product MAP is unchanged. Old frame values on the INNER
  disk core are not claimed to survive this relative replacement.
- The height-frame, closed-disk derivative, product projection,
  interpolation, and relative full-frame replacement proofs now support
  the dimensions needed for D4 x D4. Projection calculations use the
  Euclidean coordinate model, not an inner product on the product max norm.
- `FramedAttachingProduct` now uses the actual manifold dimension and
  transverse dimension n - 3. Its six-dimensional specialization is retained
  and checked. Its seven-dimensional specialization has the required
  eight-dimensional product, original-atlas tube, whole-collar map and
  frame agreement, and interior avoidance.
- `EuclideanEmbedding.nonempty_framedAttachingProduct_of_dimension_seven`
  constructs ALL these data from the original seven-manifold embedding,
  its supplied smooth normal frame, and a smooth embedded immersive
  three-sphere. No pre-existing disk, collar frame, compact ambient manifold,
  or surgery trace is assumed. Both the six- and seven-dimensional attaching
  constructions pass the focused regression build.

The full entry-point build and axiom audit pass: 15973 dependency audits,
10039 build jobs, and no additional axioms, admissions, or computational-limit
changes. This checkpoint adds 19 audited declarations in six new modules
and generalizes seven existing modules.

**Next geometric work:** construct and round the actual eight-dimensional
framed surgery trace, retaining the original atlas and required ends. The
existing trace chain is specialized to compact six-manifolds; neither its
dimensions nor its compactness assumptions can simply be reused here. The
fully framed attaching data is now supplied, but no filling torsion removal
or automatic coefficient-obstruction vanishing has been assumed.

**Still missing overall:** full quadratic-kernel vanishing beyond the proved
zero-obstruction subgroup; actual framing-preserving connectivity surgeries
and the required two-connected framed filling; Arf bordism invariance and
detection; sixth-stem generation and nontriviality; the candidate collapse's
required first-suspension nullity; and the final original-atlas diffeomorphism.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15954: curved eight-dimensional attaching product with exact collar and avoidance

- `SpanningDiskRadialProductFrame` proves that the radial boundary columns
  lie in the complement of the ACTUAL disk derivative and prescribed partial
  normal frame throughout the retained collar. Relative frame replacement
  rebuilds a framed embedded product with the SAME disk and partial frame,
  unchanged transverse boundary columns, and exactly radial transverse values
  on a whole annulus. The construction allows four transverse directions.
- `SpanningDiskAffineCollar` computes the actual radial product in the
  original ordered coordinates. Its nonzero height proves interior collar
  avoidance for every transverse vector. `SpanningDiskProductAvoidance`
  handles the remaining compact subdisk by continuity, obtaining one positive
  radius for the ENTIRE interior, bounded by the original product radius.
- The strengthened `SevenDimensionalAttachingTube` constructs this radial
  product and the original-manifold tube with one common positive radius.
  The affine product's whole interior avoids the old ambient space, and its
  prescribed normal frame and transverse frame retain exact radial values.
- `CompactSphereTubeDifference` proves the actual local curved-minus-affine
  difference has zero value and native derivative on the sphere core.
  The radial pullback and supported correction proofs now allow four
  transverse coordinates, including smoothness and zero derivative at the
  disk center. No smooth radial retraction at zero is assumed.
- `CompactCurvedDiskProduct` constructs the ACTUAL corrected attaching map.
  It fixes the disk core and derivative, preserves avoidance, and agrees
  EXACTLY with the original-manifold tube on the whole boundary face and
  outer collar, with the retained height and zero graph coordinates.
- `FramedCompactCurvedDiskProduct` proves that this map is embedded on a
  positive-radius closed product and constructs a full smooth orthonormal
  normal frame, retaining the prescribed disk-core frame exactly. The
  compact-core embedding, product restriction, and full-frame constructions
  are now valid for D4 x D4.
- `EuclideanEmbedding.exists_curvedProduct_of_dimension_seven` assembles all
  of these objects from the ORIGINAL seven-manifold, its given normal frame,
  and an embedded immersive three-sphere. All maps, frames, radii and tube
  data belong to the same construction. The ambient manifold need NOT be
  compact: the retraction is constructed near the compact sphere image.

The full entry-point build and axiom audit pass: 15954 dependency audits,
10033 build jobs, and no additional axioms, admissions, or computational-limit
changes. This checkpoint adds 21 audited declarations in seven new modules
and strengthens or generalizes eleven existing modules.

**Next geometric work:** make the full normal frame of the corrected product
agree with the ORIGINAL manifold framing on the whole attaching collar.
The map already agrees there and the full frame already agrees on the disk
core, but these do NOT establish whole-collar frame agreement. Then construct
and round the actual eight-dimensional framed surgery trace, keeping the
required original ends fixed. No filling torsion removal or automatic
coefficient-obstruction vanishing has been assumed.

**Still missing overall:** full quadratic-kernel vanishing beyond the proved
zero-obstruction subgroup; actual framing-preserving connectivity surgeries
and the required two-connected framed filling; Arf bordism invariance and
detection; sixth-stem generation and nontriviality; the candidate collapse's
required first-suspension nullity; and the final original-atlas diffeomorphism.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15933: framed eight-dimensional product and original seven-manifold tube

- `DiskThickening`, `EmbeddedDiskThickening`, and `ThickeningNormalFrame`
  now handle an arbitrary finite transverse dimension. The actual affine
  map has the computed native core derivative; compact injectivity gives
  an embedded positive-radius closed product; normal projection and smooth
  normalization extend the full normal frame with EXACT original core values.
- `DiskThickening.FramedProduct` carries the transverse dimension, defaulting
  to three for the retained six-dimensional interface. Its existence proof
  constructs the actual embedded framed product in every allowed dimension.
  `SevenDimensionalFramedProduct` applies it to the SAME actual spanning disk,
  partial frame and four-dimensional complement from checkpoint 15915.
  The result is a framed embedded D4 x D4 product, not just disk-frame data.
- The actual internal sphere normal space and ambient sphere tube now allow
  arbitrary manifold and transverse dimensions. The tube derivative's range
  is proved to equal the ORIGINAL tangent image by its internal orthogonal
  decomposition. The inverse retraction differential proves surjectivity
  directly, without inserting a separate dimension equality.
- `CompactRetractionDifferential` differentiates the actual retraction's
  identity on its OPEN base neighborhood. `CompactSphereTube` applies these
  tangent inverse identities to the original sphere and its full internal
  normal frame, proving local diffeomorphisms in the ORIGINAL atlas.
- `EmbeddedCompactSphereTube.exists_compactSphereTube` CONSTRUCTS the
  retraction near the compact sphere image and a uniform embedded tube.
  The ambient manifold is NOT assumed compact, and a global retraction is
  not assumed. The tube stays in the actual local retraction domain.
- `EuclideanEmbedding.exists_product_and_tube_of_dimension_seven` constructs
  the framed D4 x D4 product and an embedded sphere tube in the original
  seven-manifold using the SAME boundary four-frame. The tube fixes the
  original sphere and its embedded native core derivative is exactly the
  original sphere derivative together with those same four columns. The
  product's original core normal frame and radial core collar are retained.

The full entry-point build and axiom audit pass: 15933 dependency audits,
10026 build jobs, and no additional axioms, admissions, or computational-limit
changes. This checkpoint adds 18 audited declarations in five new modules
and generalizes nine existing modules. Native tangent-space rewrite issues
were resolved with typed operator equalities, not with changed limits.

**Next geometric work:** make the complementary disk frame exactly radial
on a whole collar, bend the product's affine attaching face to the actual
local tube, prove interior avoidance, retain a full normal frame agreeing
with the original manifold frame on that whole collar, and construct/round
the actual surgery trace.
The current product and tube agree at the sphere core and its derivative;
whole-collar map/frame agreement is NOT asserted yet. Filling torsion has
not been removed, and no coefficient-obstruction vanishing is assumed.

**Still missing overall:** full quadratic-kernel vanishing beyond the proved
zero-obstruction subgroup; actual framing-preserving connectivity surgeries
and the required two-connected framed filling; Arf bordism invariance and
detection; sixth-stem generation and nontriviality; the candidate collapse's
required first-suspension nullity; and the final original-atlas diffeomorphism.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15915: seven-dimensional framed disk and original boundary complement

- `FourComplementFrameExtension` uses the checked native connectivity of
  the actual Stiefel space to extend every three-sphere partial frame when
  at least four complementary directions remain. Projection transport over
  the disk constructs the needed coordinates; no trivialization or extension
  is supplied as a hypothesis.
- `FourComplementDiskNormalFrame` applies this to the orthogonal complement
  of the ACTUAL immersed four-disk derivative. Relative smoothing retains
  the exact original boundary values and normal ranges.
- `SevenDimensionalSpanningDiskFrame` extends the original normal columns
  and five stabilized axes, then straightens them on a whole radial collar.
  The disk map and frame both retain their prescribed collar values. This
  dimension-seven construction needs no parity-vanishing hypothesis.
- `SmoothDiskNormalComplement.exists_smoothDiskNormalComplement_of_dimension`
  computes and frames the remaining normal space in any dimension. The
  original three-dimensional interface is retained; the new construction
  uses four complementary directions.
- `SpanningDiskBoundaryComplementEquality` proves that the full boundary
  complement is EXACTLY the stabilized original internal normal space.
  Actual collar derivatives give inclusion and actual injectivity gives
  equality of ranks. `SpanningDiskBoundaryComplementFrame` projects its
  vectors to the old coordinates without any loss of norm or range.
- `EuclideanEmbedding.exists_framedSphereDisk_of_dimension_seven` starts
  with the original seven-manifold embedding, a given smooth normal frame,
  and a smooth embedded immersive three-sphere. It constructs the actual
  stabilized spanning disk, its collared partial normal frame, four smooth
  complementary normal directions, and their smooth orthonormal boundary
  frame of the sphere's normal space INSIDE the original manifold. All
  witnesses belong to the same constructed disk. The original manifold
  atlas is retained. The normal columns are the orthonormalization of the
  given frame, with exact agreement on the entire retained collar.

The full entry-point build and axiom audit pass: 15915 dependency audits,
10021 build jobs, and no additional axioms, admissions, or computational-limit
changes. This checkpoint adds 14 audited declarations across six new modules
and one generalized existing module.

**Next geometric work:** construct a framed embedded D4 x D4 thickening,
the original-atlas attaching tube, matching collars, and the actual surgery
trace. The disk/frame construction does NOT yet produce these objects or
remove filling torsion. No torsion-free filling, primitive integral image,
or automatic vanishing of the coefficient obstruction has been assumed.

**Still missing overall:** full quadratic-kernel vanishing beyond the proved
zero-obstruction subgroup; actual framing-preserving connectivity surgeries
and the required two-connected framed filling; Arf bordism invariance and
detection; sixth-stem generation and nontriviality; the candidate collapse's
required first-suspension nullity; and the final original-atlas diffeomorphism.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15901: original endpoint quadratic comparison and the two-ended zero-obstruction kernel

- `CollaredBoundaryOperatorCoordinates` transports both normal and derivative
  source coordinates and the original ordered target coordinates. The actual
  five-axis stabilization preserves disk extendability in BOTH directions,
  using the checked native codimension-three block theorem.
- `BoundaryOperatorParityCriterion` identifies the actual positive-height
  collar boundary operator with the ORIGINAL source-twisted raw sphere
  frame by a homotopy through injective operators. Its extendability is
  equivalent to zero ORIGINAL sphere parity. No interior immersion or
  pre-existing disk extension is assumed.
- `AnnulusBoundaryCollarDisk` uses the ORIGINAL polynomial clock, endpoint
  cut values, and spatial sphere maps. Translate time to zero, put height
  last, and apply the literal radius-two dilation at the outer boundary.
  Both ambient collar disks are globally smooth with the correct original
  boundary values. Their actual derivative formulas retain the outer factor
  of two. Both radial heights are positive: the outer clock derivative and
  the outer cut coefficient are both negative.
- `RegularCylinderBoundaryParityCriterion` applies the exact ordered normal
  coordinates to the ORIGINAL cylinder equation frame. This proves that
  extension of the original raw cylinder boundary operator is equivalent to
  zero original endpoint sphere parity, including the source rescaling.
- `CollaredCylinderEndpointParity.sphereParity_eq_of_collaredCylinder`
  constructs the generic annulus from the ACTUAL collared cylinder and uses
  its checked raw two-ended homotopy to identify the two ORIGINAL endpoint
  sphere parities. This geometric comparison does not assume either parity
  vanishes or either endpoint image is zero in slab homology.
- `CrossEndpointSphereParity` uses native Hurewicz theory in an actually
  two-connected slab to construct the required cylinder from equal integral
  images. Original smooth embedded representatives extend the comparison to
  arbitrary continuous sphere maps. `CrossEndpointIntegralParity` then proves
  equality of the original integral homology parities, and of the ORIGINAL
  quadratic values on their mod-two reductions, for arbitrary integral
  endpoint classes with equal images. The common image may be nonzero.
- `FramedSlabZeroObstructionQuadraticKernel` identifies the actual native
  integral boundary inclusion with the sum of the ORIGINAL endpoint maps.
  The two original quadratic values sum to zero on reductions of its full
  integral kernel, including cross-end cancellation. The PROVED native
  coefficient-obstruction criterion supplies such an integral kernel lift
  for every full two-ended kernel class whose obstruction is zero. Thus
  quadratic vanishing now holds on the entire zero-obstruction subgroup,
  not merely on the separate endpoint kernels.

The full entry-point build and axiom audit pass: 15901 dependency audits,
10015 build jobs, and no additional axioms, admissions, or computational-limit
changes. This checkpoint adds 36 audited declarations in eight new modules.
The recursion-depth issue in a coordinate comparison was resolved by reducing
only the named map composition; no recursion or heartbeat limit was changed.

**Next geometric work:** resolve the full boundary kernel's NONZERO native
coefficient-obstruction case and construct the required framing-preserving
connectivity surgery. No torsion-free filling, primitive integral image, or
automatic vanishing of the coefficient obstruction has been assumed. The
two-connected endpoint and filling hypotheses still must be constructed
where required by the final classification argument.

**Still missing overall:** full quadratic-kernel vanishing beyond the proved
zero-obstruction subgroup; the required two-connected framed filling;
Arf bordism invariance and detection; sixth-stem generation and nontriviality;
the candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The unconditional target `SixSphereRigidity`
remains UNPROVED.

### Earlier checkpoint 15865: two-ended homotopy with the original raw frame

- `SphereAnnulusClamp`, `FourAnnulusParityBallPush`, and
  `FourAnnulusPuncturedRetraction` construct a retraction from four-space
  minus the origin and the actual singularities onto the original punctured
  annulus. The retraction fixes both original boundary spheres and proves
  injectivity of the actual inclusion on singular homology. No smoothness
  inside the missing inner disk is assumed.
- `FourAnnulusPunctureCover` and `AnnulusBoundaryDifferenceLift` use the
  original open-hole cover and native Mayer--Vietoris exactness. The literal
  inner and outer spheres are radially homotopic in four-space minus the
  origin, so their difference lifts to the actual overlap. No vanishing of
  this ambient space's third homology is assumed.
- `FourAnnulusSinglePunctureCover`, `FourAnnulusSinglePunctureHomology`,
  `FourAnnulusBoundarySingleHomology`, and `FourAnnulusOverlapCoordinates`
  identify the actual overlap coordinates. For each original singularity,
  the outer sphere induces an integral homology isomorphism while the inner
  sphere extends its unit disk and induces zero positive-degree homology.
- `FourAnnulusPuncturedBallHomotopy` retains the original charted links while
  expanding their radius from one half to one, avoiding the origin and all
  singularities. `FourAnnulusBoundaryCoefficients` proves that each resulting
  integral coefficient is either one or minus one.
- `FourAnnulusBoundaryRelation.outer_sub_inner_eq_sum_linkingSpheres`
  proves the signed relation in the ORIGINAL punctured annulus: outer
  boundary minus inner boundary equals the sum of the actual linking
  spheres with those unit coefficients. The boundary relation is derived,
  not supplied as a hypothesis.
- `FourAnnulusBoundaryParity` evaluates this relation by the checked frame
  homology invariant. Parity-one links and an even singularity count give
  EQUALITY of the two endpoint obstructions, not vanishing of either one.
  Completeness of the invariant yields an actual endpoint-frame homotopy.
- `ManifoldFourAnnulusBoundaryHomotopy` reflects homotopy through dimension
  transport and normalization of the combined operator.
  `ManifoldFourAnnulusRawFrame` separately undoes normalization of the normal
  block, using an injective interpolation that fixes the derivative columns.
  The resulting endpoint homotopy has the exact prescribed RAW normal columns
  and the actual embedded annulus derivative columns.
- `RegularCylinderFiberAnnulusBoundaryHomotopy` uses the frame constructed
  from the original regular-fiber equations and proves its exact raw operator
  value. `GenericRegularSlabBoundaryHomotopy.exists_original_boundary_operator_homotopy`
  constructs this homotopy from the original collared cylinder, deriving
  even parity internally. It retains the original atlas, both endpoint maps,
  both collar derivatives, strict-time interior values, and protected collars
  disjoint from the actual holes.

The full entry-point build, disk regression, and axiom audit pass:
15865 dependency audits, 10007 build jobs, and no additional axioms,
admissions, or computational-limit changes. This checkpoint adds 133 audited
declarations across seventeen new modules and the existing Mayer--Vietoris
helper. The earlier disk callers also rebuild with the generalized local geometry.

**Next geometric work:** transport the raw homotopy into the original endpoint
collar coordinates, account for the radius-two derivative scaling and both
height signs, and identify its two obstruction values with the ORIGINAL
endpoint quadratic forms. The raw operator homotopy does not yet establish
quadratic equality across endpoints.

**Still missing overall:** full quadratic-kernel vanishing, including
cross-end integral cancellation and nonzero coefficient obstruction;
construction of the required two-connected framed filling; Arf bordism
invariance and detection; sixth-stem generation and nontriviality;
the candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The unconditional target `SixSphereRigidity`
remains UNPROVED.

### Earlier checkpoint 15732: original punctured-annulus frames and parity-one links

- `FourDiskParityBall.ParityBall` now accepts a specified source region,
  defaulting to the original open unit disk. The existing disk API and all
  its callers rebuild successfully. The retained local geometry is reused
  for the annulus without assuming smoothness on its missing inner disk.
- `FourAnnulusChartedParityBall` constructs arbitrarily small parity-one
  balls from the ORIGINAL annulus chart residuals. `FourAnnulusParityBallSystem`
  constructs a finite pairwise-disjoint system indexed by the ACTUAL intrinsic
  singular set, with every closed hole inside the active middle annulus.
- `SphereAnnulusFrontier` identifies the exact interior and both literal
  boundary spheres. `FourAnnulusPuncturedDomain` constructs the compact
  punctured annulus with injective native derivative everywhere. Its frontier
  consists of BOTH original endpoint spheres and the actual linking spheres.
  The original maps `q` and `2q`, all charted linking maps, and the entire
  protected end collars remain in this same punctured domain.
- `ParityBallLocalGlobalOperator` uses only smoothness on the actual ball
  image. The prescribed normal frame and original target chart give target
  coordinates and inverse coordinates on the FULL model disk, including its
  singular center. Extension of the actual global link is therefore equivalent
  to extension of the retained parity-one chart link; this is proved, not
  assumed from boundary values alone.
- `ManifoldFourAnnulusOperator` constructs the continuous global monomorphism
  and normalized frame on the original punctured annulus. Its columns are the
  prescribed normal frame and the ACTUAL embedded derivative. Both endpoint
  restrictions retain their literal source vectors and the outer scaling.
- `ManifoldFourAnnulusLinkParity` proves obstruction one on every original
  linking sphere. The inner and outer frame obstructions are defined separately;
  no equality between them is inferred from the local link calculation.
- `RegularCylinderFiberFourAnnulusFrame` uses the normal frame CONSTRUCTED
  from the original regular-fiber equations, not an extra framing-existence
  hypothesis. `GenericRegularSlabCylinder.exists_generic_with_original_ends`
  now includes the retained disjoint ball system for the SAME constructed map,
  while preserving all previously checked end data, genericity, and even parity.

The full entry-point build, disk regression build, and axiom audit pass:
15732 dependency audits, 9990 build jobs, and no additional axioms,
admissions, or computational-limit changes. This checkpoint adds 64 audited
declarations in eight new modules, including all new structure fields.

**Next geometric work:** prove the actual signed homology relation retaining
the inner sphere, outer sphere, and all linking spheres; apply it to the
constructed global frame; and compare the two restrictions with the ORIGINAL
endpoint framing obstructions. The local obstruction-one theorem and even
singularity count do NOT by themselves establish that boundary relation or
quadratic equality across endpoints.

**Still missing overall:** full quadratic-kernel vanishing, including
cross-end integral cancellation and nonzero coefficient obstruction;
construction of the required two-connected framed filling; Arf bordism
invariance and detection; sixth-stem generation and nontriviality;
the candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The unconditional target `SixSphereRigidity`
remains UNPROVED.

### Earlier checkpoint 15668: even singularity count for the original generic annulus

- `AnnulusDoublePointCompactness` defines the ACTUAL double-point locus
  in the open annulus with radii one and two. Its Euclidean closure is compact.
  Injectivity of the UNION of both protected collars puts at least one
  coordinate of every limiting pair in the closed middle core. Continuity
  only on the original closed annulus preserves equality of limiting images.
- `RegularSlabAnnulusDoublePoints` uses the ORIGINAL endpoint time values
  and strict-time interior condition to exclude both boundary spheres from
  this closure. The argument includes pairs approaching different ends.
- `AnnulusDoublePointTopology` constructs the genuine swap quotient of
  this same closure and proves it compact and Hausdorff. Its diagonal orbit
  set is the actual fixed-point image. `AnnulusDoublePointDiagonal` proves
  that every diagonal limit is an original intrinsic singularity, using
  local injectivity of the original embedded map at a regular differential.
- `AnnulusDoublePointInteriorCurve` gives real curve charts at every
  off-diagonal orbit from the actual seven-dimensional chart-difference
  equation. `AnnulusDoublePointGerm` compares the ORIGINAL closure germ
  with the unrestricted coordinate-map locus, retaining its topology.
- `AnnulusDoublePointBoundaryCurve` transfers the local rank-three residual
  reflection chart to the original closure and constructs half-line charts
  on its swap quotient. Coordinate zero is EXACTLY the diagonal orbit set
  throughout each chart, not just at the chosen center.
- `AnnulusDoublePointSingularBoundary` constructs a bijection between
  ORIGINAL intrinsic singularities and actual diagonal boundary orbits.
  `AnnulusDoublePointParity.finite_even_singularSet` applies the proved
  compact-curve boundary theorem to obtain a finite, EVEN singularity count.
- `GenericRegularSlabCylinder.exists_generic_with_original_ends` now
  includes this actual closure containment and even singularity count for
  the SAME constructed map in the ORIGINAL regular-fiber atlas. All prior
  endpoint values, collars, collar injectivity and immersion, original
  ambient boundary derivatives, strict-interior values, and genericity
  remain retained. Parity is derived, not added as an input hypothesis.

The full entry-point build and axiom audit pass: 15668 dependency audits,
9982 build jobs, and no additional axioms, admissions, or limit changes.
This checkpoint adds 47 audited declarations in nine new modules and
strengthens the existing original-cylinder construction.

**Next geometric work:** construct the finite disjoint parity-one linking
balls and the actual punctured annulus; retain BOTH original boundary
spheres in its signed homology relation; construct the original global
frame operator there; and compare its two endpoint restrictions with the
ORIGINAL endpoint framing obstructions. Even singularity count alone does
NOT prove that framing comparison or quadratic equality across endpoints.

**Still missing overall:** full quadratic-kernel vanishing, including
cross-end integral cancellation and nonzero coefficient obstruction;
construction of the required two-connected framed filling; Arf bordism
invariance and detection; sixth-stem generation and nontriviality;
the candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The unconditional target `SixSphereRigidity`
remains UNPROVED.

### Earlier checkpoint 15621: generic original cylinders with protected immersive ends

- `ScaledSphereBoundaryKernel` handles the actual radius-two sphere
  without replacing its spatial map. `AnnulusClockDerivative` differentiates
  the ORIGINAL inward clock and identifies its kernel at both boundary radii
  with the sphere defining-function derivative kernel.
- `AnnulusClockCollarImmersion` proves that both ORIGINAL collar derivatives
  are injective from the given endpoint immersions and their nonzero signed
  height slopes. `SmoothAnnulusBoundaryImmersion` transfers this to the SAME
  smoothed annulus, with its original endpoint values and protected collars.
- `AnnulusImmersiveBoundaryNeighborhoods` uses the compact singular set to
  produce immersive end annuli with `1 < r0 < 9/8` and `15/8 < r1 < 2`.
  It does not assert immersion in the middle.
- `AnnulusPerturbationCutoff` constructs a globally smooth nonnegative
  cutoff positive EXACTLY between those radii. `CompactRetractionAnnulusInterior`
  controls the compact active core and fixes the remaining points, preserving
  the prescribed open target at EVERY interior annulus point.
- `GenericProperFourAnnulus` constructs one small manifold perturbation
  with generic four-to-seven jets in a countable original target-chart cover.
  Both protected end maps and their actual embedded derivatives are fixed.
  Its active double-point equations are regular. The compact-image tubular
  retraction is constructed; the full target need not be compact.
- `FourAnnulusSingularities` proves finiteness of the INTRINSIC singular set
  from compactness, chartwise isolation, and the protected immersive ends.
- `GenericRegularSlabCylinder.exists_generic_with_original_ends` applies
  all these results to the ACTUAL collared cylinder and original regular-fiber
  atlas, given smooth embedded endpoint spheres. The SAME constructed map
  retains both endpoint values, the prescribed collars, their injectivity
  and immersion, both original ambient boundary derivatives, and strict-time
  interior values. Its intrinsic singular set is finite. Every interior
  double-point equation is regular, because two distinct protected points
  cannot have the same image. No two-connectivity or framing comparison is
  manufactured by this construction.

The full entry-point build and axiom audit pass: 15621 dependency audits,
9973 build jobs, and no additional axioms, admissions, or limit changes.
This checkpoint adds 30 audited declarations in ten new modules.

**Next geometric work:** exclude boundary ends of the actual annular
double-point closure, construct its compact unordered curve and diagonal
boundary charts, prove singularity parity, and compare the ORIGINAL
endpoint framing obstructions. Finiteness and double-point regularity do
NOT establish even parity or quadratic equality across endpoints.

**Still missing overall:** full quadratic-kernel vanishing, including
cross-end integral cancellation and nonzero coefficient obstruction;
construction of the required two-connected framed filling; Arf bordism
invariance and detection; sixth-stem generation and nontriviality;
the candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The unconditional target `SixSphereRigidity`
remains UNPROVED.

### Earlier checkpoint 15591: relative smoothing of the original cross-end cylinder

- `SphereAnnulusCoordinates` constructs an explicit homeomorphism between
  the actual sphere cylinder and the Euclidean annulus with radii one and
  two. Time is `(norm squared - 1) / 3`; the original endpoint spheres
  are the literal vectors `q` and `2q`. All coordinate and endpoint
  identities are proved, not merely asserted up to homotopy.
- `AnnulusCollarAmbientExtension` extends the original Euclidean-valued
  annulus map and installs both given collars on full ambient neighborhoods
  without changing any annulus value. `AnnulusCollarSmoothing` applies the
  constructed compact-image retraction and relative approximation. It fixes
  the protected subcollars `norm <= 9/8` and `15/8 <= norm`, and preserves
  a prescribed open target region at EVERY interior annulus point.
- `RegularSlabAnnulusCollars` constructs the required globally smooth
  ambient collars from the ORIGINAL endpoint spatial maps. Their height
  functions are the actual inward-clock formulas, now polynomial in the
  squared norm. Both exact collar comparisons are proved.
- `SmoothRegularSlabCylinder` constructs a map smooth near the entire
  original closed annulus in the ORIGINAL regular-fiber atlas, retaining
  both endpoint maps, both protected subcollars, and strict-time interior
  values. The full regular fiber need not be compact. No retraction or
  smoothing-existence hypothesis is added.
- `AnnulusDerivativeUniqueness` proves unique within-derivatives on the
  actual annulus, including BOTH boundary spheres, using contained convex
  balls. `SmoothSlabCylinderCollarControl` identifies each ordinary ambient
  boundary derivative with the original prescribed collar derivative.
  Agreement outside the annulus is NOT assumed. It also proves that the
  protected collars remain injective for injective original endpoint maps.

The full entry-point build and axiom audit pass: 15591 dependency audits,
9963 build jobs, and no additional axioms, admissions, or limit changes.
This checkpoint adds 50 audited declarations in seven new modules.

**Next geometric work:** prove boundary immersion from the original
endpoint immersions and the nonzero radial collar derivatives; obtain
protected immersive annuli; arrange generic four-to-seven singularities;
and compare the original endpoint framing obstructions. Interior immersion,
genericity, and quadratic equality across endpoints are NOT yet proved.

**Still missing overall:** full quadratic-kernel vanishing, including
cross-end integral cancellation and nonzero coefficient obstruction;
construction of the required two-connected framed filling; Arf bordism
invariance and detection; sixth-stem generation and nontriviality;
the candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The unconditional target `SixSphereRigidity`
remains UNPROVED.

### Earlier checkpoint 15541: actual proper cylinders with injective original end collars

- `CollaredSlabCylinderExtension` constructs the inward clock `4u(1-u)`
  and proves its positivity in the open interval, injectivity on each
  protected end collar, and strict upper bound there. The actual slab
  push and a time reparametrization produce a cylinder retaining BOTH
  original endpoint maps. Its interior lies in the strict-time interior,
  and a constructed homotopy to the input fixes both ends.
- The left and right collar formulas retain the original spatial maps
  exactly. The boundary preimage consists precisely of the two endpoint
  parameter slices when the original endpoint maps lie in the boundary.
- `RegularSlabCollaredCylinder` obtains all collar cuts and inequalities
  from the ORIGINAL regular cylinder. For an actually two-connected slab,
  such a collared cylinder exists exactly when the ORIGINAL integral
  sphere classes agree. The inclusion-map corollary allows two nonzero
  endpoint images to agree; it does not require either image to vanish.
- `RegularSlabCylinderCollarInjectivity` proves injectivity of the union
  of BOTH retained collars for injective original endpoint spheres.
  The actual inner-time cuts separate the left and right collar images.
  No injectivity of the middle of the cylinder is claimed.

The full entry-point build and axiom audit pass: 15541 dependency audits,
9956 build jobs, and no additional axioms, admissions, or limit changes.
This checkpoint adds 39 audited declarations in three new modules,
including the constructed cylinder data and all its fields.

**Next geometric work:** smooth the actual cylinder relative to these
collars, arrange generic four-to-seven singularities, and compare the
original endpoint framing obstructions. These steps have NOT been proved
for the new cylinder. Its construction is continuous, not an immersion.

**Still missing overall:** quadratic vanishing for cross-end integral
cancellation and nonzero coefficient obstruction; constructing the
required two-connected framed filling; Arf bordism invariance and
detection; sixth-stem generation and nontriviality; the candidate
collapse's required first-suspension nullity; and the final original-atlas
diffeomorphism. The exact coefficient obstruction from checkpoint 15502
is not proved zero. The unconditional target `SixSphereRigidity` remains
UNPROVED.

### Earlier checkpoint 15502: the exact coefficient obstruction on the original boundary kernel

- `CoefficientKernelLifting` identifies the precise integral-lifting
  criterion. If an integral lift has image `2b`, its half-image class
  is taken modulo the integral image PLUS genuine target two-torsion.
  This class vanishes exactly when an integral kernel lift exists.
  A mod-two null class is not declared integrally null.
- `CoefficientKernelObstruction` proves independence of all lift and
  half-image choices. The resulting linear obstruction has kernel exactly
  the image of the integral kernel, and its values are killed by two.
  It is NOT proved to be the zero map.
- `MiddleHomologyKernelObstruction` constructs this obstruction from the
  ORIGINAL singular-homology coefficient square. Only integral second
  homology of the source must vanish. The target need not be connected
  or torsion-free, and no target homology vanishing is assumed.
- `FramedSlabModTwoBoundaryEquiv` proves injectivity of the actual endpoint
  inclusion-sum map, completing its original mod-two coordinate equivalence.
- `FramedSlabKernelObstruction` specializes the obstruction to the actual
  native boundary inclusion. Its zero criterion in the ORIGINAL endpoint
  coordinates allows both integral endpoint images to cancel in the slab.
- `EndpointKernelObstructionQuadraticValue` applies the checked geometric
  disk theorem to the integral representative supplied by that criterion.
  The ORIGINAL endpoint quadratic form vanishes on the exact zero-obstruction
  subgroup. This identifies the domain of the existing integral-kernel
  result; it does not establish vanishing on a larger kernel by assumption.

The full entry-point build and axiom audit pass: 15502 dependency audits,
9953 build jobs, and no additional axioms, admissions, or limit changes.
This checkpoint adds 42 audited declarations in six new modules.

**Still missing:** geometric quadratic vanishing for cross-end integral
cancellation and for classes with nonzero coefficient obstruction;
construction of the required two-connected framed filling; Arf bordism
invariance and detection; sixth-stem generation and nontriviality;
the candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The full POLAR kernel is self-orthogonal,
but the QUADRATIC form is not yet proved zero on the full mod-two kernel.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15460: the full two-ended kernel for the original quadratic polar forms

- `ZeroSecondHomologyEvaluation` and `ZeroSecondHomologyCapPairing`
  construct the actual middle evaluation and cap pairing assuming only
  vanishing of integral second homology. They do not require the whole
  boundary to be connected. The original cochains and cap map are retained.
- `FramedSlabDisconnectedBoundaryKernel` proves second-homology vanishing
  from the separate two-connectivity of the original endpoints and the
  retained boundary diffeomorphism. For an actually two-connected filling,
  the full native mod-two boundary kernel equals its annihilator.
- `CompactManifoldOpenExtension` and `OpenEmbeddingCapPairing` prove the
  actual cap-pairing comparison for open component inclusions. Restriction
  to the same component is the identity; cross-component terms vanish.
- `FramedSlabBoundaryComponents` constructs the original open, disjoint
  endpoint inclusions, their cover of the native boundary, and the actual
  integral homology decomposition. `FramedSlabModTwoBoundarySum` proves
  every native mod-two boundary class is a sum of original endpoint images.
- `TwoComponentGeometricPairing` and `FramedSlabBoundaryPairingComparison`
  identify this cap pairing with the sum of the ORIGINAL endpoint quadratic
  polar forms. `originalEndpointPolarKernel_selfOrthogonal` covers the FULL
  kernel, including pairs whose images cancel across the two endpoints.

The full entry-point build and axiom audit pass: 15460 dependency audits,
9947 build jobs, and no additional axioms, admissions, or limit changes.
This checkpoint adds 58 audited declarations in ten new modules.

**Still missing:** quadratic vanishing on this full mod-two kernel,
including cross-end cancellation and the integral/coefficient/torsion
comparison; constructing the required two-connected framed filling;
Arf bordism invariance and detection; sixth-stem generation and
nontriviality; the candidate collapse's required first-suspension nullity;
and the final original-atlas diffeomorphism. Self-orthogonality of the
POLAR form does not prove vanishing of the QUADRATIC form.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15402: original quadratic vanishing on the integral endpoint kernel

- `ManifoldFourDiskRawFrame` transports the original punctured-disk
  extension back to its RAW normal columns by a homotopy that fixes the
  disk derivative. `IntegralKernelBoundaryFrameExtension` now constructs
  this exact raw extension for the SAME generic integral-kernel disk,
  preserving its boundary, collar, and strict-interior values.
- `CollaredDiskOperatorStabilization` appends the five fixed graph axes
  in the actual collar coordinates. Its ordered normal-source change
  fixes the four disk coordinates. `CollaredDiskCombinedTargetChange`
  transports the actual combined operator under a fixed target change.
- `ExtendedBoundaryOperatorParity`, `ExtendedBoundaryOperatorReflection`,
  and `ExtendedBoundaryOperatorQuadraticValue` prove original parity and
  quadratic vanishing from an exact boundary-operator extension, for
  either uniform collar sign. Interior immersion is NOT required.
  The original sphere-dependent source twist is retained.
- `RegularCylinderFiberCollarCoordinates` moves the actual cylinder's
  time-first ambient coordinates to height-last coordinates. The ordered
  normal-model comparison carries the ORIGINAL cylinder equation frame
  exactly to the ORIGINAL endpoint equation frame with zero height.
- `ClosedDiskCollarDerivative` and `RegularCylinderDiskCollar` compare
  ordinary derivatives using uniqueness WITHIN the original closed ball.
  The retained collar of the SAME constructed disk gives negative height
  derivative at the left end and positive height derivative at the right.
  No agreement on a full ambient neighborhood outside the disk is assumed.
- `RegularCylinderDiskBoundaryFrame` constructs the exact stabilized
  extension in the prescribed endpoint frame and original disk derivative.
  `IntegralKernelEndpointQuadraticValue` combines the actual disk,
  raw extension, collar sign, and frame comparison: an embedded sphere
  whose INTEGRAL class dies in an ACTUALLY two-connected slab has zero
  original sphere parity. With an actually two-connected endpoint, its
  original mod-two quadratic value is zero as well.
- `IntegralKernelEndpointHomology` removes the embedded-representative
  inputs using the checked construction of an embedded smooth sphere in
  the same homotopy class. The literal integral kernel is preserved.
  Native Hurewicz representatives give `integralHomologyParity_zero_of_endpoint_kernel`
  for EVERY integral endpoint class killed by the original inclusion.
  `quadraticForm_zero_on_reduced_integral_endpoint_kernel` then proves
  vanishing of the ORIGINAL quadratic form on their mod-two reductions.

The latest full entry-point build and axiom audit pass. This checkpoint
adds 61 audited declarations in 11 new modules and two existing modules.
No additional axioms, admissions, or computational-limit changes were used.

**Still missing:** constructing the required two-connected framed filling;
handling the kernel for BOTH disconnected endpoints, including classes
whose two images cancel but neither image is zero; the integral/mod-two
kernel comparison and torsion; the corresponding quadratic-kernel and
Arf bordism argument; sixth-stem generation and Arf detection; the actual
candidate collapse's required first-suspension nullity; and the final
original-atlas diffeomorphism. The new reduced-integral-kernel theorem is
NOT a theorem about every mod-two kernel class. The unconditional target
`SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 15341: the original disk boundary relation and kernel-frame extension

- `FourDiskParityBallRadial`, `FourDiskParityBallPush`, and
  `UnitDiskClamp` construct continuous original chart pushes and a radial
  clamp. `FourDiskPuncturedRetraction` combines them into an ACTUAL
  retraction from the complement of the closed-disk native singular set
  onto the original punctured disk. The inclusion is therefore injective
  on integral homology. No regularity outside the closed disk is assumed.
- `FourDiskPuncturedBall` identifies each original open chart region with
  the Euclidean ball and each center-punctured region with the punctured
  ball. `FourDiskPuncturedBallHomotopy` expands its half-radius sphere to
  the ORIGINAL linking sphere through an actual annulus avoiding every
  closed-disk singularity. Their complement homology maps agree.
- `MayerVietorisLeftEquiv` proves bijectivity of the actual intersection
  inclusion from vanishing of the adjacent ambient groups and the second
  cover-piece group. `FourDiskPunctureCover` and `FourDiskPunctureHomology`
  apply it to the ORIGINAL finite-point complement and the actual disjoint
  open-ball union. Their one-point comparison maps are literal inclusions.
- `FourDiskOuterSphereHomology` proves that the original outer sphere
  induces a homology isomorphism in each one-point complement, using the
  checked enclosing-sphere shift homotopy. `FourDiskPunctureCoordinates`
  gives actual complement coordinates, their one-point comparisons, and
  the original inclusion-sum formula, including the empty-puncture case.
- `FourDiskBoundaryCoefficients` compares the outer sphere with each
  original local model by an automorphism of integral third sphere
  homology. Each actual coefficient is one or minus one.
  `FourDiskBoundaryRelation.outer_eq_sum_linkingSpheres` then proves the
  signed relation between the ORIGINAL outer sphere and original linking
  spheres in the ACTUAL punctured disk, for every third sphere class.
  The earlier sphere-cylinder relation is not substituted for this proof.
- `FourDiskBoundaryParity` evaluates that integral relation using the
  checked frame homology invariant. Modulo two the signs disappear.
  An even actual singular count and parity-one links force zero outer
  obstruction and exact boundary-frame extension.
- `ManifoldFourDiskBoundaryExtension` applies this to the frame already
  constructed from the original disk derivative and normal framing.
  It proves `fourDiskOuterObstruction_zero` and exact extension of the
  ORIGINAL outer injective operator. The extending operator is not claimed
  to be the derivative of the original disk at interior singularities.
- `IntegralKernelBoundaryFrameExtension` constructs this extension for
  an injective immersed original boundary sphere representing an INTEGRAL
  kernel class in an ACTUALLY two-connected regular slab. The SAME smooth
  disk retains its exact boundary, original collar, and strict-interior
  values. Its needed even singularity count is proved by the generic-disk
  theorem, and its normal frame is constructed from the original equations.
  Neither parity, genericity, nor framing existence is a new hypothesis.

The actual disk boundary relation and exact original outer-operator
extension are now proved. The next gap is the comparison of that boundary
operator with the prescribed boundary geometric quadratic value, retaining
the original normal-frame normalization, ordered Euclidean coordinates,
and collar sign. The original quadratic value is NOT yet proved zero.
No immersion of the whole constructed disk is asserted or needed for the
new operator-extension conclusion.

Actual two-connectivity of the filling and boundary injectivity remain
explicit in the applicable integral-kernel theorem. Framing-preserving
connectivity surgery, integral/mod-two coefficient and torsion control,
disconnected-boundary kernel self-orthogonality, quadratic kernel vanishing,
Arf bordism invariance/detection, sixth-stem generation and nontriviality,
candidate collapse nullhomotopy, and the final original-atlas diffeomorphism
remain substantial gaps. The unconditional target `SixSphereRigidity`
is UNPROVED.

### Earlier checkpoint 15213: the original punctured-disk frame and all local link values

- `ManifoldNormalChartCoordinates` now works in every dimension. Its
  normal columns and original inverse-chart derivative give continuous
  linear coordinates with continuous inverse. Existing six-dimensional
  callers still check.
- `ManifoldFourDiskOperator` constructs the ACTUAL normal-plus-derivative
  operator of a four-disk in a seven-dimensional manifold. Its last four
  columns are `fderiv` of the original embedded map. Smoothness is needed
  only at points of the closed disk. The derivative range lies in the
  original tangent image; the prescribed normal range is orthogonal to
  it. Consequently the operator is injective throughout the original
  punctured disk. Both its operator map and normalized partial-frame map
  are continuous there. No immersion at deleted centers is asserted.
- `ManifoldFourDiskChartOperator` proves the exact factorization into
  original target coordinates and the identity-normal-block chart
  derivative, using equality of germs. In particular, the local linking
  operator does NOT acquire a derivative of the ball parametrization.
- `FourDiskParityBallOperator` constructs actual coordinate families
  with continuous inverses on the ENTIRE retained closed ball, including
  its singular center. Disk-extension equivalence for these coordinates
  and checked identity-block stability show that the original global
  operator link cannot extend. Normalization preserves nonextension.
- `ManifoldFourDiskLinkParity` identifies the exact restriction of the
  global punctured-disk map on each original linking sphere and proves
  that its actual obstruction is one. Dimension transport uses only
  proved equalities. The outer obstruction is defined, NOT proved zero.
- `RegularCylinderFiberNormalFrame` transports the original equation
  frame by the ordered ambient and normal-coordinate isometries. The
  actual tangent and normal ranges of the original regular-fiber
  embedding are computed. The resulting smooth range frame has an exact
  ambient formula in terms of the original equation differential's
  orthogonal right inverse; no arbitrary replacement framing is used.
- `RegularCylinderFiberFourDiskFrame` applies the construction on the
  ORIGINAL seven-dimensional regular-fiber atlas and proves parity one
  on every actual linking sphere. There is no additional normal-frame
  existence hypothesis in this specialization.

The global frame construction, local linking comparison, and construction
of the original-fiber normal frame are now proved. The next gap is the
signed integral homology relation between the ORIGINAL outer sphere and
these linking spheres in the actual punctured disk. The existing relation
for a punctured sphere-cylinder is not silently substituted for this one.
That relation, together with the checked even singularity count, must
still yield outer-frame extension. Its collar comparison with the
original boundary quadratic value also remains unproved.

Actual two-connectivity of the filling and the applicable boundary
injectivity requirements remain explicit. Framing-preserving connectivity
surgery, integral/mod-two coefficient and torsion control, disconnected-
boundary kernel self-orthogonality, quadratic kernel vanishing, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, candidate
collapse nullhomotopy, and the final original-atlas diffeomorphism remain
substantial gaps. The unconditional target `SixSphereRigidity` is UNPROVED.

### Earlier checkpoint 15167: original parity-one linking balls and the regular punctured disk

- `ResidualLink`, `ResidualLinkGeometry`, and `ResidualBallChart` now
  allow any finite-dimensional leading space, while retaining the actual
  four-dimensional residual, inverse chart, embedded ball, and linking
  sphere. Their existing three-to-six uses remain checked.
- `StabilizedResidualCoordinates` gives exact Euclidean block coordinates
  for any number of added identity columns. Its unit model is exactly the
  checked cusp operator with those columns, and the proved identity-block
  extension theorem shows that it does not extend. `StabilizedResidualModel`
  removes the ACTUAL invertible constant leading block and positive scale
  by a genuine continuous linear source equivalence.
- `StabilizedResidualLink` deforms the ORIGINAL residual-coordinate link
  through injective operators: first remove its Schur shears, then contract
  the leading block through the actual inverse-coordinate ball while keeping
  the nonzero residual on the linking sphere. Consequently the original
  link, not only its model, cannot extend.
- `FourSevenOperatorLocalParity` removes the actual rank-three source and
  target coordinate changes. The original four-to-seven operator on that
  same sphere has `sphereParity 2 = 1`. `FourSevenLocalContribution`
  constructs the actual charted ball in a prescribed open domain; its
  center is the only singularity and its boundary operators are the
  ORIGINAL operators. A smooth representative is used only where equality
  with the original family has been proved.
- `FourDiskParityBall` retains the original source-ball chart, original
  seven-dimensional target chart, native singularity characterization,
  actual chart-derivative link, and parity one. The actual image ball is
  embedded and compact, with proved open region, closure, and linking
  frontier. `FourDiskChartedParityBall` constructs it inside ANY prescribed
  open neighborhood of an original native singularity.
- `FourDiskParityBallSystem` uses the proved finite native singular set
  and finite Hausdorff separation to choose pairwise disjoint CLOSED balls.
  They lie in the original disk interior, cover every native singularity
  by their open regions, and retain their original parity-one links.
- `FourDiskPuncturedDomain` removes precisely these open regions from the
  ORIGINAL closed disk. The resulting domain is compact and its actual
  native derivative is injective at every point. Its frontier is exactly
  the original outer sphere together with the actual linking spheres.
  `outerBoundary` and `linkingSphere` are the original continuous maps into
  this domain, not replacement boundary maps.
- `GenericIntegralKernelDisk.exists_generic_disk_of_integral_kernel`
  now supplies `Nonempty (GenericFourDisk.ParityBallSystem g)` for the SAME
  constructed disk. No extra genericity or local-parity assumption was
  added to the existence theorem. The previously proved even native
  singular count, conditional on boundary injectivity, is retained.

The local four-to-seven parity-one contribution and the actual disjoint
puncture geometry are now proved. The GLOBAL normal-plus-disk-derivative
frame map, its comparison on those linking spheres, and the signed homology
relation for these original boundary maps still need to be assembled.
Thus extension of the ORIGINAL boundary frame and vanishing of the original
quadratic value remain unproved. No immersion of the whole disk is asserted.

Actual two-connectivity of the filling and the applicable boundary
injectivity requirements remain explicit. Framing-preserving connectivity
surgery, integral/mod-two coefficient and torsion control, disconnected-
boundary kernel self-orthogonality, quadratic kernel vanishing, Arf bordism
invariance/detection, sixth-stem generation and nontriviality, candidate
collapse nullhomotopy, and the final original-atlas diffeomorphism remain
substantial gaps. The unconditional target `SixSphereRigidity` is UNPROVED.

### Earlier checkpoint 15066: even native singularity count for the original generic disk

- The residual-level theorems in `GenericFamilyFlatGerm`,
  `GenericFamilyClosedCurve`, and `GenericFamilyLocalCurve` now permit
  arbitrary finite-dimensional parameter and leading-block spaces.
  Their existing three-to-six results remain special cases.
- `MapDoublePointTopology` identifies the ACTUAL double-point closure
  of a single map with that of its constant family over a genuine
  zero-dimensional vector space. The homeomorphism commutes with swap.
  `MapDoublePointLocalCurve` pulls back the ORIGINAL residual derivative
  through the actual continuous linear equivalence and constructs a
  real chart through the singular diagonal, with swap acting by negation.
- `DiskDoublePointGerm` proves that, near an interior point in an
  ORIGINAL target chart, the actual disk double-point closure agrees with
  the unrestricted coordinate-map closure. A swap-invariant neighborhood
  transfers the reflection chart without replacing either topology.
- `DiskDoublePointBoundaryCurve` uses the immersive outer annulus to
  place each native singularity in the region with regular rank-three
  chart residuals. It proves that EVERY such singularity belongs to the
  actual diagonal closure and constructs its reflection chart. The
  unordered quotient has a half-line chart there; coordinate zero is
  equivalent to membership in the ACTUAL diagonal orbit set throughout
  the chart source. Every diagonal orbit is covered.
- `DiskDoublePointSingularBoundary` gives an explicit bijection between
  the ORIGINAL native singular set on the closed disk and the actual
  diagonal orbit set. No singularity is omitted, duplicated, or merged.
- `DiskDoublePointParity` combines the actual off-diagonal real charts
  and diagonal half-line charts into a covering half-line atlas. The
  quotient is the already-proved compact Hausdorff space. The checked
  compact-curve boundary theorem and singular-boundary bijection prove
  that the original native singular set is finite and has EVEN cardinality.
- `GenericIntegralKernelDisk.exists_generic_disk_of_integral_kernel`
  now supplies that even count for the SAME constructed proper disk,
  conditional on injectivity of the original boundary map. Its exact
  boundary values, retained collar, strict-interior values, immersive
  outer annulus, finite native singular set, and original chart-jet and
  double-point regularity all remain in the conclusion. Genericity and
  parity are proved for the chosen parameter, not additional inputs to
  this existence theorem.

This closes the local diagonal-chart, actual singular-boundary identification,
and singularity-parity gaps for these proper generic four-disks. The next
missing result is the comparison of this parity with the ORIGINAL boundary
frame obstruction. Evenness alone does NOT prove that the disk is immersive
or that the original geometric quadratic value vanishes.

Actual two-connectivity of the filling and injectivity of the boundary
remain explicit prerequisites for the applicable disk conclusion.
Framing-preserving connectivity surgery, integral/mod-two coefficient and
torsion control, disconnected-boundary kernel self-orthogonality, and
quadratic kernel vanishing remain open. Arf bordism invariance/detection,
sixth-stem generation and nontriviality, candidate collapse nullhomotopy,
and the final original-atlas diffeomorphism remain substantial gaps.
The unconditional target `SixSphereRigidity` is UNPROVED.

### Earlier checkpoint 15041: actual compact disk double-point spaces and interior curve charts

- `DiskDoublePointCompactness` defines actual distinct equal-image pairs
  in the open unit disk. Their closure is contained in the product of the
  closed disks and is compact. Continuity only on the original closed disk
  preserves image equality at every limit pair. An injective outer collar
  and separation of interior from boundary images put the entire closure
  in the OPEN disk product; no global smoothness outside the disk is used.
- `DiskDoublePointTopology` constructs the actual coordinate-swap
  homeomorphism and its original orbit quotient. The unordered space is
  compact and Hausdorff. Its diagonal orbit set is exactly the image of
  the fixed-point set and is closed. No topology or curve structure is
  imposed by replacement.
- `RegularSlabDiskDoublePoints` supplies boundary-image separation in
  the ORIGINAL regular fiber: all interior times are strictly between the
  endpoint times, whereas the prescribed boundary values lie at an endpoint.
  Actual boundary injectivity gives the retained collar's injectivity and
  therefore excludes all boundary ends of the double-point closure.
- `DiskDoublePointInteriorCurve` applies the inverse-function theorem to
  the ACTUAL native-chart difference of the two disk images. Its source
  stays inside the distinct interior pair domain, where the actual closure
  agrees with the regular zero set. This gives real charts in the original
  subtype topology and, through the free swap quotient, unordered real
  charts at EVERY point outside the diagonal orbit set. Their sources are
  disjoint from that set.
- `DiskDoublePointDiagonal` proves that injectivity of the ORIGINAL native
  derivative excludes a diagonal limit, using local injectivity through
  the original Euclidean embedding. The first source coordinate injects
  the actual diagonal set into the finite native singular set. Thus the
  actual diagonal set and its unordered image are finite. The converse
  inclusion of singularities is NOT asserted.
- `GenericIntegralKernelDisk.exists_generic_disk_of_integral_kernel`
  now retains all these conclusions for the SAME constructed disk in
  the ORIGINAL seven-dimensional regular-fiber atlas, conditional on
  `Injective f` for the original boundary map. Exact boundary values,
  the retained outer collar, strict-interior values, the immersive outer
  annulus, finite native singularities, and actual jet/double-point
  regularity remain in its conclusion.

The next missing local theorem is that each generic rank-three singularity
belongs to this actual double-point closure and has an equivariant real
chart, giving a half-line boundary chart in the unordered quotient. Until
that is proved, the quotient is NOT yet a proved compact one-manifold with
boundary and evenness of the singular count is NOT established. The
comparison with the ORIGINAL boundary frame obstruction also remains open.

Actual two-connectivity of the filling and boundary injectivity remain
explicit inputs to the applicable disk conclusions. Framing-preserving
connectivity surgery, integral/mod-two coefficient and torsion control,
disconnected-boundary kernel self-orthogonality, and quadratic kernel
vanishing remain open. Arf bordism invariance/detection, sixth-stem
generation and nontriviality, candidate collapse nullhomotopy, and the
final original-atlas diffeomorphism remain substantial gaps.
The unconditional target `SixSphereRigidity` is UNPROVED.

### Earlier checkpoint 15013: simultaneous disk jets and actual double-point regularity

- `CompactRetractionPairSubmersion` computes the actual parameter
  derivative of the original chart-coordinate difference. Independent
  affine evaluations at distinct source points show it is surjective
  whenever AT LEAST ONE cutoff is nonzero. The other point may be fixed;
  neither source smoothness outside the valid region nor a free derivative
  operator is assumed.
- `CompactRetractionPairDomain` retains both actual source-domain,
  tubular-domain, and common target-chart conditions, together with
  distinctness and the one-active-point condition. Its difference zeros
  are exactly the actual image coincidences.
- `CompactRetractionGenericDoublePoints` applies parametric Sard on
  those genuine open domains. The same almost-everywhere parameter set
  works in every chart of a specified countable collection.
  `RegularDoublePointsOn` records surjectivity of the ACTUAL source-pair
  derivative at actual coincidences, not a replacement linear map.
- `CompactRetractionGenericMap`, `GenericProperFourDisk`, and
  `FourDiskSingularities` now choose ONE parameter satisfying BOTH
  jet genericity and double-point regularity, while retaining all previous
  compact-domain, strict-interior, exact-collar, protected-derivative,
  and finite-native-singularity conclusions.
- `SignedSphereCollarInjectivity` proves injectivity of the original
  signed collar when the original spatial sphere map is injective: its
  nonzero height coefficient determines the radius, and the sphere map
  determines the radial direction. `RegularSlabDiskCollarInjectivity`
  derives spatial injectivity from actual boundary injectivity and the
  derived one-end condition, then transfers collar injectivity to the
  perturbed disk which retains that collar.
- `GenericIntegralKernelDisk.exists_generic_disk_of_integral_kernel`
  now gives simultaneous regular jets and active double points for the
  ORIGINAL integral-kernel disk in the ORIGINAL seven-dimensional
  regular-fiber atlas. With `Injective f` supplied for the original boundary
  map, the fixed collar is injective. Pairs entirely in the protected
  collar therefore cannot be double points, and EVERY off-diagonal
  interior double point is regular. This implication is explicit; boundary
  injectivity is NOT inferred from the immersion hypothesis.

The actual compact double-point closure, exclusion of its boundary ends,
local charts at its diagonal singularities, the unordered curve, evenness
of the singular count, and the comparison with the ORIGINAL boundary
frame obstruction remain unproved for these four-disks. Regular double
points alone do not prove parity, immersion, or quadratic kernel vanishing.

The integral-kernel construction still assumes actual two-connectivity
of the filling. Framing-preserving connectivity surgery, original
boundary-frame comparison, integral/mod-two coefficient and torsion
control, and the disconnected-boundary version of kernel self-orthogonality
remain open. Arf bordism invariance/detection, sixth-stem generation and
nontriviality, candidate collapse nullhomotopy, and the final original-atlas
diffeomorphism remain substantial gaps. `SixSphereRigidity` is UNPROVED.

### Earlier checkpoint 14988: proper integral-kernel disks with finite intrinsic singularities

- `CompactRetractionGenericMap.exists_small_regular_on_compact_mem`
  selects a generic parameter in any specified neighborhood of zero.
  The earlier small-parameter theorem remains available as a corollary.
- `CompactRetractionInteriorControl` proves open-target preservation
  on a compact source subset. A compactly supported cutoff then controls
  the WHOLE disk interior: the compact inner disk stays in the open target
  region, while the remaining points are fixed. The open disk itself is
  not treated as compact, and its boundary need not lie in that open region.
- `CompactRetractionProtectedDerivative` proves exact preservation of
  the original embedded derivative at every zero of a nonnegative cutoff,
  including the edge of its support. The zero-parameter equality is proved
  on a genuine neighborhood using the retraction's original open base.
- `GenericProperFourDisk` constructs the compact-image retraction and
  a smooth nonnegative disk cutoff, then chooses ONE parameter satisfying
  both strict-interior preservation and actual four-to-seven chart-jet
  regularity. Boundary values, outer-collar values, and the original
  embedded derivatives on the protected outer annulus are unchanged.
- `DiskImmersiveOuterAnnulus` derives an immersive outer annulus from
  immersion on the boundary. The actual compact singular set has maximum
  norm strictly below one. No immersion of the whole disk is inferred.
- `FourDiskSingularities` compares the actual chart, native, and original
  embedded derivatives. Chartwise isolation gives intrinsic isolation;
  compactness and the immersive outer annulus give a FINITE intrinsic
  singular set for the new proper disk.
- `GenericIntegralKernelDisk.exists_generic_disk_of_integral_kernel`
  applies everything to the ORIGINAL integral boundary-kernel class and
  ORIGINAL seven-dimensional regular-fiber atlas. It constructs the disk,
  fixes its exact original boundary values and a possibly smaller outer
  collar, sends EVERY interior point into the strict-time slab interior,
  and gives an immersive outer annulus, finite native singular set, and
  regular actual chart jets on the inner region. The new collar radius is
  strictly between `3 / 4` and `1`; preservation of the entire former
  quarter-annulus is NOT claimed.

These results close the properness and finite-intrinsic-singularity gaps
for the disk jet construction. They do NOT prove off-diagonal double-point
transversality, the compact unordered double-point curve, evenness of the
singular count, or the local and global comparison with the ORIGINAL
boundary frame obstruction. The disk is not yet proved immersive.
The boundary input is an immersion, not an embedding. Excluding boundary
ends of the double-point curve will require actual boundary injectivity
(or an argument accounting for boundary double points); it is not supplied
by the existing injective-derivative hypothesis.

Actual two-connectivity of the filling is still an explicit input to the
integral-kernel theorem. Framing-preserving connectivity surgery,
original boundary-frame comparison, integral/mod-two coefficient and
torsion control, and quadratic kernel vanishing remain unproved. The
existing kernel self-orthogonality result still assumes two-connectivity
of both boundary and filling; an arbitrary disconnected two-ended boundary
is not covered. Arf bordism invariance/detection, sixth-stem generation
and nontriviality, candidate collapse nullhomotopy, and the final
original-atlas diffeomorphism remain substantial gaps.
The unconditional target `SixSphereRigidity` remains UNPROVED.

### Earlier checkpoint 14973: protected four-to-seven manifold jet genericity

- `RankTwoAvoidance` factors every actual operator of rank at most two
  through the real plane. Parametric avoidance applies in dimensions four
  and seven because `4 + 2 * (4 + 7) < 4 * 7`.
- `CorankOneLocalRegularity` proves residual regularity and local isolation
  without fixing the leading-block dimension. `GenericFourSevenOperators`
  applies it to rank-three operators with a four-dimensional residual.
  Its actual submersive operator families have isolated rank-three
  singularities for almost every parameter; compact subsets of the valid
  region contain finitely many singularities when the operators are continuous.
- `CompactTubularRetraction` now proves surjectivity of the normal-bundle
  projection derivative using a local section through the actual normal
  vector. Consequently the constructed compact-image retraction is
  submersive throughout its domain, without a global compactness or
  normal-frame assumption on the target.
- `CompactRetractionAffineFamily` constructs the actual source-dependent
  affine perturbations followed by that retraction. The original manifold
  atlas is retained. Valid protected points are fixed exactly. The actual
  spatial-jet parameter derivative in a target chart is surjective wherever
  the cutoff is nonzero; its derivative is not replaced by a free operator.
- `GenericFourSevenManifoldJets` proves almost-everywhere regularity of
  these actual chart jets, simultaneously in any countable collection.
  `CompactRetractionGenericMap` constructs a countable cover by the
  ORIGINAL target charts and selects one arbitrarily small parameter.
  On the whole specified compact source the map stays in the tubular
  domain, is smooth, and fixes the cutoff zero set. Its jets are regular
  on every actual active chart domain in the cover.

This does NOT yet produce a generic proper collared disk in the filling:
preservation of the strict-time slab interior still needs to be combined
with a compactly supported disk cutoff. Intrinsic finite singularity sets,
off-diagonal double-point transversality, the compact double-point curve,
evenness of its diagonal ends, and the original frame-obstruction comparison
are not proved for these four-to-seven maps. Genericity alone does not
imply that the number of singularities is even or that the map is immersive.
The direct singularity-parity route is being investigated as an alternative
to a separate global relative disk-immersion theorem; neither route is closed.

Framing-preserving connectivity surgery, original boundary-frame comparison,
integral/mod-two kernel and torsion control, and quadratic kernel vanishing
remain open. The existing kernel self-orthogonality theorem still requires
two-connectivity of both the boundary and filling and does not cover an
arbitrary disconnected two-ended boundary. Arf bordism invariance/detection,
sixth-stem generation and nontriviality, candidate collapse nullhomotopy,
and the final original-atlas diffeomorphism remain unproved.
The unconditional target `SixSphereRigidity` is still only a proposition,
not a proved theorem.

### Earlier checked result: smooth integral-kernel disks with immersive boundary collars

- `CompactTubularRetraction` constructs a genuine smooth retraction near
  a compact subset of the ORIGINAL embedded manifold, without assuming
  that the entire manifold is compact. Its actual normal-displacement
  inverse fixes an open neighborhood of that compact subset.
- `CompactRelativeManifoldSmoothing` uses this retraction after relative
  ambient approximation. Protected values stay fixed, and a specified
  compact source region stays in a specified open target region.
- `SignedSphereCollar` and `RegularSlabDiskCollar` identify the constructed
  disk's actual time and spatial coordinates with smooth collar maps.
  Their radial derivatives have the exact signed coefficient `2 * slope`.
  Original spatial immersion gives injective derivatives on the boundary.
- `RegularCylinderFiberEmbedding` constructs the original NONCOMPACT
  regular fiber's closed Euclidean embedding, retaining its regular-fiber
  atlas, time as the first coordinate, and original sphere coordinates.
- `DiskCollarAmbientExtension` preserves every original disk value while
  installing the smooth collar on a full ambient neighborhood.
  `DiskCollarSmoothing` fixes the outer quarter-annulus and keeps every
  interior point in the specified open target region. Uniqueness of
  derivatives WITHIN the closed ball gives the exact boundary derivative;
  no unjustified two-sided equality of the original disk map is used.
- `SmoothRegularSlabDisk` applies these constructions to the original
  full regular fiber and strict-time slab interior. `SmoothIntegralKernelDisk`
  constructs actual smooth FOUR-disks from original integral boundary-kernel
  classes in an actually two-connected SEVEN-dimensional slab. Boundary
  values and the outer collar are unchanged, and the ambient derivative
  is injective on the boundary when the original spatial sphere is immersive.
  The sphere's endpoint choice is derived from its proved connectivity,
  not supplied as an additional hypothesis.

Global immersion of the disk remains UNPROVED: boundary immersion does
not imply interior immersion. Framing-preserving connectivity surgery,
identification of the original induced boundary framing, integral-to-mod-two
kernel/torsion control, and quadratic kernel vanishing remain necessary.
The existing boundary-kernel self-orthogonality theorem still assumes
two-connectivity of BOTH the boundary and filling; this checkpoint does
not extend it to arbitrary disconnected two-ended boundaries.
Arf bordism invariance/detection, sixth-stem generation, candidate collapse
vanishing, and unconditional `SixSphereRigidity` remain unfinished.


### Earlier checked result: exact collared disks from the integral kernel

- `DiskRadialCollar` restricts the existing smooth radial flattening to
  the literal closed disk. It fixes the sphere, is homotopic to the
  identity relative to that sphere, and equals radial projection on the
  outer half-annulus. Its clock `1 - ‖x‖²` is positive inside and zero
  exactly on the boundary.
- `CollaredSlabDiskExtension` combines this flattening with the actual
  inward collar push. The constructed disk has the SAME boundary values,
  maps EVERY interior point into the original strict-time slab interior,
  and is homotopic to the supplied disk relative to its boundary. Both
  endpoint collars have exact formulas, with height proportional to
  `1 - u²` and unchanged boundary spatial coordinates.
- `RegularSlabCollaredDisk` obtains the collar cuts from the original
  regular-cylinder data, then constructs `CollaredDiskExtension` from
  any actual continuous disk extension. For an actually two-connected
  slab, existence of this collared disk is equivalent to vanishing of
  the ORIGINAL integral sphere class. The inclusion-kernel theorem uses
  the original homology inclusion of an arbitrary actual subspace.

These are continuous disks with exact boundary collars, NOT globally
immersed disks. The construction assumes actual two-connectivity of the
filling for the integral-kernel implication; it does not construct the
framing-preserving connectivity surgery. Mod-two nullity is not used as
integral nullity, and no coefficient/torsion gap has been discharged.
Quadratic kernel vanishing, Arf bordism invariance/detection, sixth-stem
generation, candidate collapse vanishing, and unconditional
`SixSphereRigidity` remain unproved.


### Earlier checked result: original boundary class and geometric kernel self-orthogonality

- `RelativeCoefficientTripleLift` constructs a lift through the original
  map of nested pairs from vanishing of the projected connecting class.
  The ambient chain is corrected by subtracting an actual subspace chain;
  its image is exactly the original class. Coefficients are arbitrary.
- `RelativeBoundaryLocalNonvanishing` proves the local-zero contradiction:
  such a lift, ambient local vanishing, and persistence of zero on nearby
  supports contradict the nonzero interior local values.
- `RegularSlabBoundaryFundamentalClass` identifies the actual connecting
  image with the original fundamental class for a supplied boundary atlas.
  Local and global mod-two uniqueness close the previous identification
  gap; no expected boundary class is imposed as a hypothesis.
- `FramedSlabBoundaryFundamentalClass` specializes to the ACTUAL boundary
  predicate in `A.atlas` and the RETAINED `A.boundaryAtlas`. Compactness
  is derived. Its original connecting map sends the constructed relative
  class to this boundary class. The actual cap square and cap-kernel
  criterion now concern this original fundamental class.
- `RelativeModTwoCap.pair_connecting_cap_kernel` gives the general
  restriction-image criterion from injectivity of the actual relative cap.
- `MiddleCapKernelOrthogonality` uses genuine evaluation naturality and
  the separating dual of native mod-two homology to prove self-orthogonality
  from the actual cap-kernel criterion.
- `FramedSlabBoundaryKernel` applies this to the original boundary
  inclusion, retaining the six-dimensional boundary atlas. The existing
  cap/geometric comparison gives self-orthogonality for the original
  geometric intersection and quadratic polar forms of any supplied
  actual embedding, normal frame, and tubular retraction of that boundary.

The kernel theorems explicitly assume that BOTH the actual boundary and
the filling are two-connected. They do not construct the required
framing-preserving connectivity surgery, and they are not automatically
theorems for a disconnected two-ended boundary. Quadratic VANISHING on
the kernel is still unproved: immersed disks, identification of the
prescribed boundary framing, and integral-to-mod-two coefficient control
remain necessary. Arf bordism invariance/detection, sixth-stem
nontriviality/generation, candidate collapse vanishing, and unconditional
`SixSphereRigidity` remain unfinished.

Earlier statements of the boundary-class and kernel gaps are superseded
by this checkpoint with the explicit hypotheses just stated.

### Earlier checked result: connecting-cap compatibility and local boundary homology

- `RelativeCoefficientConnecting` constructs genuine ambient and
  subspace cycle lifts for the original homology connecting map.
  `RelativeModTwoPairConnectingCochains` supplies the actual cochain
  extension and relative cocycle representing cohomological connecting.
- `RelativePairCapConnectingRepresentatives` gives an explicit capped
  chain whose boundary is the difference of the two relevant cycles.
  `RelativePairCapConnecting` proves the genuine connecting-cap identity
  for arbitrary pairs and arbitrary classes, with no manifold hypothesis.
- `RegularSlabConnectingCap` specializes this identity to the original
  relative fundamental class. Duality and actual cohomology exactness
  identify the kernel of cap with its connecting image followed by
  inclusion with the image of original cohomology restriction.
- `RegularSlabFundamentalLocalization` proves that the original pair map
  to local homology at EVERY interior point sends the relative class to
  the canonical nonzero local class, through actual neighborhood excision.
- `CollaredSlabBoundaryPuncture` proves that every positive time in the
  original collar push is strictly interior. This gives a homotopy
  equivalence whose forward map is the actual inclusion after deleting
  any boundary point. Every open neighborhood meets the actual interior.
- `RegularSlabBoundaryLocalHomology` uses this equivalence and the
  original pair and coefficient sequences to prove vanishing of the
  SLAB's local homology at every boundary point, integrally and with
  every nonzero finite-cyclic coefficient modulus, in all degrees.

The boundary-class identification and the local-vanishing plan in this
earlier checkpoint are now proved. The original intersection-kernel
theorem above has explicit two-connectivity hypotheses. Constructing
the compatible filling, immersed disks, coefficient control, and
quadratic kernel vanishing remains necessary for Arf invariance.
The unconditional smooth classification remains unproved.


### Earlier checked result: actual relative fundamental class and cap identification

- `CollaredSlabRelativeHomology` proves that the original identity from
  the boundary pair to the collar pair is an integral quasi-isomorphism.
  The actual coefficient sequence transfers this to finite-cyclic
  relative homology; no flatness of these coefficients is assumed.
- `RegularSlabCoreHomology` constructs the genuine excision equivalence
  from each compact interior core and the actual boundary-collar
  equivalence. Their forward maps are the original maps of pairs.
- `RegularSlabCoreHomologyNaturality` proves that these comparisons
  commute with the actual restriction of homology support, using the
  original chain-map composition identities.
- `RegularSlabRelativeFundamentalClass` transports the constructed
  compact-supported interior fundamental class to the original slab's
  boundary-relative homology. The class is independent of the chosen
  inner slab. Its inverse comparison on every collar-controlled core
  returns that core's original fundamental class.
- `RegularSlabRelativeFundamentalCap` proves that the previously
  constructed slab duality is precisely the original relative cap
  product with this class. Consequently this actual cap product is
  bijective in every pair of complementary degrees.

The connecting image of this relative class has NOT yet been identified
with the original boundary fundamental class. The comparison with the
original intersection pairing, kernel self-orthogonality, immersed
disks, and integral-to-mod-two coefficient control remain unfinished.
Arf bordism invariance/detection, sixth-stem nontriviality/generation,
candidate collapse vanishing, and the final original-atlas diffeomorphism
and unconditional `SixSphereRigidity` remain unproved.


### Earlier checked result: relative duality for the actual collared filling slabs

- `CollaredIntervalPush`, `CollaredSlabInteriorHomotopy`, and
  `RegularSlabInteriorEquivalence` construct an actual homotopy equivalence
  with the original interior inclusion as its forward map. The push stays
  in the original cylinder fiber and fixes the middle interval.
- `RegularSlabInteriorCapDuality` uses the native regular-fiber interior
  charts. Actual compact-support cap followed by the original inclusion
  is bijective to the homology of the original slab.
- `RegularSlabCompactCores` constructs genuine compact inner slabs and
  proves that every compact interior support lies strictly inside one
  whose exterior intervals remain constant collars.
- `CollaredSlabBoundaryTime` and `CollaredSlabBoundaryRetraction` retract
  the two actual collar neighborhoods to the endpoint fibers, fixing the
  endpoints throughout the fiber-preserving homotopy.
- `RelativeModTwoHomologyComparison`, `CollaredSlabRelativeCohomology`,
  and `RegularSlabCoreCohomology` use the original integral pair sequences,
  free relative chain groups, and actual excision pullbacks to identify
  boundary-relative cohomology with supported cohomology on each core.
- `RelativeModTwoPullbackFunctor` and `RegularSlabCoreNaturality` prove
  that these comparisons commute with actual extension of support.
  Every nested collar-controlled core transition is bijective.
- `CompactSupportCofinalComponent` and
  `RegularSlabCompactSupportComparison` prove bijectivity into the genuine
  compact-support direct limit. The boundary comparison is independent
  of the chosen core; no expected group replaces the actual direct limit.
- `RegularSlabBoundaryDuality` gives the resulting relative-cohomology
  to absolute-homology duality in complementary degrees. For the actual
  `FramedSlabData`, its relative subspace is identified with the boundary
  of the RETAINED manifold atlas, not an independently assigned atlas.

Identification with the original boundary fundamental class and
intersection pairing is still unproved, so this does not yet establish
kernel self-orthogonality or Arf bordism invariance. Constructing relative
immersed disks, preserving/identifying the original boundary framing,
and controlling integral-to-mod-two kernels remain separate obligations.
Sixth-stem nontriviality/generation and detection, candidate collapse
vanishing, and the unconditional original-atlas diffeomorphism remain open.


### Earlier checked result: constructed disk frames and integral-kernel disks

- The previous genuine framed immersed-disk theorem gives zero for the
  ORIGINAL geometric quadratic value, retaining the actual derivative,
  boundary tangent frame, source twist, and either uniform collar sign.
- `RelativeRightInverseExtension` constructs continuous right inverses
  for surjective finite-dimensional operator families. Tietze extension
  followed by the explicit correction `R + A - R D A` extends prescribed
  calibrated boundary columns exactly. No arbitrary frame extension is
  assumed; Hilbert coordinates are transported back to the original normed
  ambient product.
- `RegularDiskEquationFrame` applies this construction to the ACTUAL
  defining-equation differential along the disk. The extending frame,
  its injectivity, and its transversality to the actual disk derivative
  are now derived, not separate inputs to quadratic vanishing.
- `CollapseCollarDiskQuadraticValue` derives boundary calibration from
  agreement with the original normalized collapse-coordinate germ. Its
  vanishing theorem retains the prescribed original normal frame.
- `IntegralKernelDiskExtension` proves that an actual three-sphere in a
  two-connected target extends continuously over the ordinary closed
  four-ball exactly when its actual INTEGRAL class vanishes. Naturality
  supplies an exact disk extension for a sphere in the integral kernel
  of an actual inclusion map. These disks are not asserted to be immersed.

The remaining geometric work includes making the filling two-connected
without changing its boundary framing, relative immersed-disk approximation
with a proper collar, comparison with the compactified regular-fiber frame,
and the boundary connecting/intersection comparison and self-orthogonality.
Integral and mod-two kernels must
not be identified without a coefficient/torsion argument. Arbitrary Arf
bordism invariance and detection, sixth-stem nontriviality/generation,
candidate collapse vanishing, and unconditional original-atlas smooth
rigidity remain unproved.

### Earlier checked comparison: collapse-induced and prescribed quadratic forms

- `ManifoldNormalFrameHomotopy` constructs the actual combined-operator
  homotopy from a continuous injective normal-frame family. Tangent columns
  stay fixed, normal ranges remain complementary, and the original
  sphere-dependent source twist is retained. The original sphere parities
  are therefore equal.
- `GeometricArfFrameHomotopy` uses the proved embedded representatives of
  all actual mod-two middle classes to identify the original quadratic
  forms. Tubular retractions and basepoints may differ at the endpoints.
  The geometric Arf invariants agree as well.
- `PositiveNormalFrameHomotopy` supplies an explicit positive interpolation,
  including for nonconstant scale functions. Every actual operator remains
  injective and in the prescribed normal range.
- `CollapseInducedQuadraticForm` constructs a smooth normal frame from the
  actual orthogonal right inverse of the collapse-coordinate differential.
  Its operator equals the original prescribed frame times the positive
  tube radius. Its quadratic form and Arf invariant are consequently the
  original ones. For radius-normalized data the two frames are equal.
- The actual Hopf-product collapse has radius one, so its coordinate-induced
  frame equals `southPairEuclideanNormalFrame`. Its geometric Arf invariant
  is again proved to be one, using this differential-induced frame.

These are comparisons on the SAME original embedded manifold. Comparison
with the stereographically compactified regular-fiber frame, the geometric
boundary-kernel argument, arbitrary framed-bordism invariance and detection,
sixth-stem nontriviality/generation, candidate collapse vanishing, and the
unconditional original-atlas diffeomorphism theorem remain unproved.

### Earlier checked geometric Arf value: the actual Hopf product has value one

- `ProductModTwoThirdHomology` constructs the mod-two third-homology
  splitting using the actual projections and factor inclusions. The
  inverse identities follow from coefficient reduction and the proved
  integral splitting. For the product of three-spheres the resulting
  coordinates are linear over the field with two elements.
- The original factor sphere classes map to the two coordinate vectors.
  Their previously proved geometric quadratic values are both one.
- `ArfPlaneRecognition` proves that polar nondegeneracy forces the
  off-diagonal coefficient of a two-dimensional quadratic form to be one.
  The two actual values therefore identify the form with the anisotropic
  plane by an explicit linear isometry.
- `QuaternionicHopfArfInvariant` applies this to the ORIGINAL geometric
  quadratic form of the framed Hopf-product embedding. Its geometric Arf
  invariant is one for every tubular retraction and basepoint. The file
  also supplies an actual tubular retraction and a standalone value theorem.
- This is the same embedding and framing whose actual smooth collapse
  represents the original native sixth-stem smash-square class. No
  substitute homology group, framing, or assigned invariant is used.

The actual homology coordinates and Arf-value calculation are closed.
Geometric Arf invariance/detection, sixth-stem nontriviality and generation,
nullity of the candidate's first suspended collapse, original-atlas framed
filling, and the final diffeomorphism and unconditional smooth rigidity
remain unproved. Arf value one alone does not yet prove the native class
nontrivial, and the candidate's Arf value zero does not yet prove its
collapse nullhomotopic.

### Earlier checked factor parities: both actual values are one

- The balanced quaternionic normal-plus-tangent rotation has an explicit
  contraction through injective operators. Its two inverse diagonal blocks
  cancel by a real quarter-turn in the actual quaternionic matrix group.
- This rotation acts on the original reference normal and tangent columns.
  Placing it in either ambient factor contracts the actual raw factor-frame
  map. The retained ambient isometry, normal-coordinate changes, radius,
  signs, and doubled tangent operators are unchanged.
- The actual radial frame in seven-space is homotopic, through injective
  operators, to the one-column sphere fiber with three identity columns.
  The previously proved fiber-parity theorem gives its nonzero obstruction.
  Quaternionic conjugation and two fixed coordinate changes prove the same
  non-extension result for the inverse radial frame.
- For any constant `16 x 13` injective frame, its actual source-twisted
  stabilization differs by a FIXED ambient equivalence from fifteen identity
  columns followed by that inverse radial frame. Consequently the twisted
  constant frame does not extend over the disk. No sphere-dependent change
  of coordinates is assumed to extend.
- `QuaternionicHopfFactorParity` proves that BOTH actual factor spheres have
  spanning-disk parity one. The choice-independent geometric sphere parity
  and the original middle-homology quadratic refinement also take value one
  on each factor class, for any tubular retraction and basepoint.

The factor-parity calculation, actual mod-two homology coordinates, and
geometric Arf value one are proved. Geometric Arf invariance/detection,
sixth-stem nontriviality and generation, nullity of the candidate's
first suspended collapse, original-atlas framed filling, and the final
diffeomorphism and unconditional smooth rigidity remain unproved.


### Earlier checked raw normal columns and twisted parity test

- `NormalColumnNormalization` proves that rectangular Gram--Schmidt
  interpolation stays in the original normal range. Appending the fixed
  tangent columns therefore gives a homotopy through injective operators.
- `ManifoldRawSphereFrame` applies this to the actual normal frame of an
  embedded six-manifold. It constructs the raw combined sphere-frame map
  and proves it homotopic to the normalized map used by geometric parity.
  This homotopy also transports the actual source twist; the twist is
  neither discarded nor assumed to extend over the disk.
- `QuaternionicHopfFactorRawFrames` identifies both actual factor maps
  with their raw normal-plus-tangent formulas. The original ambient
  isometry, both normal-coordinate changes, their radius and signs, and
  the doubled tangent operators remain explicit. Vanishing of each
  factor's geometric parity is equivalent to extension of its actual
  source-twisted raw frame map.

The normal-column normalization, numerical factor-parity calculation,
and geometric Arf value one are proved. The required geometric Arf
invariance/detection theorem, sixth-stem nontriviality and generation,
nullity of the candidate sphere's first suspended collapse, original-atlas
framed filling, and the unconditional diffeomorphism theorem remain unproved.


### Earlier checked smooth collapse coordinates and factor tangent operators

- `SmoothProductTube`, `SmoothPairedTube`, and `SmoothFiberCoordinates`
  retain the actual smooth inverse under stabilization, pairing, and
  invertible fiber-coordinate changes. `DiffeomorphProductModels` permits
  genuinely different source and target normed model spaces in both factors.
- `QuaternionicHopfTubePartialDiffeomorph` composes these constructions
  with the ORIGINAL certified Hopf tube, its actual base diffeomorphism,
  and the already specified normal coordinates. Every stage has full
  source and is proved equal to its retained tube. The paired Euclidean
  partial diffeomorphism is likewise exactly `southPairEuclideanTube`.
- `FramedCollapseFromPartialTube` constructs smooth finite coordinates
  from that actual inverse. It proves their surjective differential,
  exact zero fiber, and prescribed normal derivative, and retains the
  actual collapse map. The derivative calibration is radius one; the
  original chosen tube radius is still present in the retained normal frame.
- `QuaternionicHopfSmoothCollapseData` supplies genuine `FramedCollapseData`
  for the constructed Euclidean embedding and normal frame. Its map is
  exactly the previously checked tube collapse. Its sphere map, using the
  standard Euclidean compactifications, has the ORIGINAL native sixth-stem
  smash-square class (`southPairSmoothCollapse_nativeClass`).
- The two ORIGINAL factor inclusions are smooth immersive embeddings in
  the compatible Euclidean atlas. Their native differentials are computed
  through the actual identity diffeomorphism. Their sphere-framed tangent
  operators are explicit: the retained ambient isometry applied to twice
  the corresponding quaternion-axis tangent operator, with the other
  factor zero. The original LEFT-multiplication source tangent frame is
  retained; it is not confused with the RIGHT-multiplication normal blocks.

The actual raw quaternionic combined operators now contract, and the
retained sphere-dependent source twist has its nonzero obstruction proved.
Both actual factor parities and middle-homology quadratic values are one.
The complete geometric Arf value is now proved to be one.
Geometric Arf invariance/detection, sixth-stem nontriviality
and generation, vanishing of the first ordinary suspension of the original
candidate collapse, an original-atlas framed filling, and the final
diffeomorphism and unconditional smooth rigidity remain unproved.


### Earlier checked actual Euclidean framed Hopf-product collapse

- The paired collapse homotopy is constructed on the whole one-point
  compactification. Every slice is the collapse of its actual paired
  open tube, and infinity stays fixed. Its endpoint sphere map represents
  the ORIGINAL native sixth-stem smash-square class.
- Joint smoothness of the retained tube is proved in both base and normal
  variables. The actual core is twice the original product inclusion.
  Its native differential is twice the original differential, and its
  tangent image and normal spaces are proved unchanged by that scaling.
- The six-dimensional Euclidean atlas is constructed from the original
  product charts. Both identity maps are proved smooth, and the actual
  tangent-image comparison is checked. The product smooth structure is
  retained; no homeomorphism is used to assign a different smooth structure.
- The finite ambient coordinates are an actual isometry and induce exactly
  the retained source compactification. The finite target coordinates are
  an explicit linear equivalence and induce exactly the retained target
  compactification. Both normal reflections and chosen radius factors remain.
- `southPairEuclideanEmbedding` and `southPairEuclideanNormalFrame` are the
  actual embedding and normal frame in those coordinates. The smooth open
  tube `southPairEuclideanTube` has exactly that core and normal derivative.
  `southPairEuclideanCollapse_nativeClass` identifies its actual collapse,
  using standard Euclidean compactifications, with the original native
  sixth-stem class.

The actual Euclidean tube now has a full-source smooth partial inverse
and genuine FramedCollapseData for the constructed embedding and normal
frame. Its actual standard-compactification collapse retains the ORIGINAL
native sixth-stem class. The two embedded factor spheres and their actual
source-framed tangent operators are computed, and both actual factor
parity values and geometric Arf invariant are now proved to be one.
The geometric Arf invariance/detection theorem, sixth-stem nontriviality
and generation, original candidate-collapse vanishing, framed filling, and
unconditional smooth rigidity remain unproved. The known candidate Arf-zero
value does not yet imply nullity of its first suspended collapse.


### Earlier checked actual stabilized Hopf tube-collapse homotopy

- `StereographicStabilizedCoordinates` constructs the actual ambient
  map `(v,u) -> lift(v) + u pole`, its explicit inverse, and the L2
  linear-isometry version. The paired compactification coordinates retain
  the ORIGINAL product-suspension and sphere-pairing order.
  `CollapseAmbientEquiv` proves exact equivariance of the actual collapse,
  including infinity, under the specified ambient homeomorphism.
- `QuaternionicHopfStabilizedTube` retains the ORIGINAL certified tube,
  reparametrizes its base by the actual south-fiber diffeomorphism, and
  applies those ambient coordinates. Its core is explicitly TWICE the
  quaternion-axis inclusion. Its full formula uses the endpoint of the
  checked frame homotopy, with the fixed sign and compressed normal vector.
  The corresponding paired tube has an EXACT collapse-map comparison
  with the original `southPairedProductBasedMap`, not an assigned class.
- `QuaternionicHopfNormalRotationCoordinates` constructs invertible
  normal-fiber coordinates from the proved full frame ranges. Both the
  forward and inverse operator formulas are smooth in time and base.
  `QuaternionicHopfTubeFiberRotation` starts at the identity and carries
  the endpoint normal frame back through the actual radial frame family.
  Joint continuity of both fiber homeomorphisms is proved.
- `QuaternionicHopfTubeNormalCoordinates` retains the CHOSEN tube radius
  in the fixed normal map `(v,u) -> (-2u, 2r B(v))`, where B is the actual
  inverse target-coordinate map. Differentiating the original compressed
  tube proves that its normal derivative is the endpoint frame composed
  with this map. `QuaternionicHopfNormalizedTube` reindexes by its inverse
  and proves the exact endpoint-frame derivative and target collapse change.
- `QuaternionicHopfTubeFrameHomotopy` constructs an ACTUAL based collapse
  homotopy for one stabilized Hopf factor. Every stage is an open tube,
  its core stays twice the original inclusion, and its normal derivative
  is exactly the checked radial frame at reversed time. The last normal
  derivative is the computed raw quaternionic frame. The homotopy is
  continuous on the whole one-point compactification and fixes infinity;
  its first map is the original normalized tube collapse.

The actual Euclidean tube now has a full-source smooth partial inverse
and genuine FramedCollapseData for the constructed embedding and normal
frame. Its actual standard-compactification collapse retains the ORIGINAL
native sixth-stem class. The two embedded factor spheres and their actual
source-framed tangent operators are computed, and both actual factor
parity values and geometric Arf invariant are now proved to be one.
The geometric Arf invariance/detection theorem, sixth-stem nontriviality
and generation, original candidate-collapse vanishing, framed filling, and
unconditional smooth rigidity remain unproved. The known candidate Arf-zero
value does not yet imply nullity of its first suspended collapse.


### Earlier checked actual stereographic Hopf normal-frame homotopy

- `StereographicInverseDifferential`, `StereographicProjectionCoordinates`,
  and `StereographicTargetDifferential` differentiate the ORIGINAL
  stereographic formulas. The source equator has chart radius TWO, and
  the derivative at twice a unit vector retains the positive pole term.
  The target derivative at the antipode is the actual pole-complement
  projection, not an assigned identity matrix.
- `QuaternionicHopfSourceChart` and `QuaternionicHopfChartTarget` retain
  the original source projection, the actual south-fiber parametrization,
  and the explicit invertible target map from quaternions to the chosen
  stereographic coordinates. `QuaternionicHopfChartEquations` computes
  the derivative of the original stereographic Hopf equations.
- `QuaternionicHopfChartNormalLift` constructs the explicit right inverse.
  `QuaternionicHopfChartNormalFrame` computes the kernel and proves that
  this inverse is orthogonal to it. Uniqueness identifies the ACTUAL
  canonical normal frame in the ORIGINAL regular-fiber atlas.
- `QuaternionicHopfRadialRotation` gives the exact comparison with the
  raw quaternionic normal frame by a quarter turn in the pole-radius
  plane. The factor two, fixed target-coordinate inverse, and NEGATIVE
  sign on the added radial coordinate remain explicit.
- `QuaternionicHopfRadialHomotopy` connects the identity to that rotation
  through actual orthogonal operators. Both reflection normals are
  proved nonzero. `SmoothSphereRotation` additionally proves smoothness
  in operator coordinates. `QuaternionicHopfNormalFrameHomotopy` proves
  that each rotation fixes the ORIGINAL inclusion's tangent space, and
  that every intermediate frame is smooth, injective, and has exactly
  the original normal range.
- `QuaternionicHopfProductFrameHomotopy` proves the corresponding block
  homotopy on the ACTUAL S3 x S3 product, retaining the original product
  atlas and native inclusion differential. Its endpoint formula retains
  both fixed target maps, both scale factors, and BOTH radial reflections.

The actual Euclidean tube now has a full-source smooth partial inverse
and genuine FramedCollapseData for the constructed embedding and normal
frame. Its actual standard-compactification collapse retains the ORIGINAL
native sixth-stem class. The two embedded factor spheres and their actual
source-framed tangent operators are computed, and both actual factor
parity values and geometric Arf invariant are now proved to be one.
The geometric Arf invariance/detection theorem, sixth-stem nontriviality
and generation, original candidate-collapse vanishing, framed filling, and
unconditional smooth rigidity remain unproved. The known candidate Arf-zero
value does not yet imply nullity of its first suspended collapse.


### Earlier checked canonical Hopf tube and actual product-collapse representative

- The stereographic fiber embedding, equations, induced frame, compactified
  original map, collapse data, and canonical tube comparison now work for
  arbitrary fiber dimension k, not only six. The normal-model equivalence
  and its inverse remain explicit in both the frame and collapse map.
  The original six-dimensional callers are retained and rechecked.
- `QuaternionicHopfTubeClass` constructs the ACTUAL chosen framed tube of
  the three-dimensional south Hopf fiber in its source stereographic chart.
  The original regular-fiber atlas and equation-induced normal frame are
  retained. The original-map collapse data give exactly the polynomial
  Hopf map in these pole coordinates; same-frame collapse comparison then
  proves that the canonical tube collapse has the ORIGINAL native Hopf
  class. Its unit Hopf coordinate and original suspended smash-square
  class follow without an additional hypothesis.
- `StabilizedPairSphereCoordinates` gives the specified homeomorphisms
  from the pair of stabilized ambient and normal spaces to the standard
  spheres, using the ORIGINAL product-suspension and sphere-pairing order.
- `FramedTubeNativeSmash` adds a real normal direction to each original
  certified tube and forms their literal paired tube. Its sphere map is
  DEFINED from the actual one-point collapse. The exact based-map equality
  identifies it with the ORIGINAL suspended smash of the original tube's
  sphere map, including the collapsed complements and infinity.
- `QuaternionicHopfProductCollapse.southPairedProduct_nativeClass` proves
  that this ACTUAL product-tube collapse S16 -> S10 represents the canonical
  sixth-stem square. `southPairedProduct_originalHopfClass` identifies it
  with the original explicit Hopf map's suspended smash class.

The actual Euclidean tube now has a full-source smooth partial inverse
and genuine FramedCollapseData for the constructed embedding and normal
frame. Its actual standard-compactification collapse retains the ORIGINAL
native sixth-stem class. The two embedded factor spheres and their actual
source-framed tangent operators are computed, and both actual factor
parity values and geometric Arf invariant are now proved to be one.
The geometric Arf invariance/detection theorem, sixth-stem nontriviality
and generation, original candidate-collapse vanishing, framed filling, and
unconditional smooth rigidity remain unproved. The known candidate Arf-zero
value does not yet imply nullity of its first suspended collapse.


### Earlier checked actual product collapse and Hopf product normal frame

- `PairedTubeCollapse` retains two independent base manifolds and both
  ordered normal factors. Its product tube is an open embedding, and its
  ACTUAL one-point collapse is exactly the descended product of the two
  original collapse maps. This is an equality of continuous maps, including
  their collapsed complements, not an assignment of stable classes.
- `OrthogonalRightInverseProduct` proves that the canonical orthogonal
  right inverse of the block differential is the block sum of the original
  right inverses. Ambient and normal products carry their L2 inner products;
  the ordinary product norm is not treated as an inner-product norm.
  `HilbertProductEquations` proves the corresponding derivative formula for
  the actual paired defining functions.
- `QuaternionicHopfProductFrame` constructs the literal product of the two
  south-fiber inclusions. It is a smooth closed embedding with injective
  native differential, in the original product atlas. Its paired ambient
  equations induce a normal frame which is EXACTLY the ordered block sum
  of the two computed Hopf frames.
- The transverse formula retains both right-quaternion-multiplication
  blocks. The two radial formulas give the two separate ambient radius
  vectors. `southPairNormalFrame_original` compares this frame with BOTH
  ORIGINAL regular-fiber frames via the actual `southFiberDiffeomorph`,
  retaining both copies of the fixed target coordinate change.

The canonical-tube construction now supplies a map-level representative
of the ORIGINAL suspended Hopf smash. Comparison of its stereographic tube
framing with this raw quaternionic product framing, and the geometric Arf
value, remain open. Sixth-stem nontriviality and generation, candidate-collapse
vanishing, framed filling, and unconditional smooth rigidity remain unproved.


### Earlier checked comparison with the original Hopf sphere-fiber frame

- `OrthogonalRightInverseCoordinates` proves the exact normal-frame
  change under any invertible linear target coordinate map, without
  assuming that coordinate change is an isometry.
- `QuaternionicHopfRadialTail` proves the degree-two homogeneity of
  the actual quaternion tail and its formula under the original radial
  source retraction. Since that tail vanishes on the south fiber, its
  differential is unchanged by radial normalization.
  `QuaternionicHopfRadialEquations` retains the radial norm equation
  and identifies the entire augmented derivative with the one already
  computed for the explicit normal frame.
- `QuaternionicHopfTargetChange` constructs the fixed coordinate
  equivalence from the ACTUAL south-pole derivatives of the quaternion
  tail chart and the ORIGINAL model chart. Its augmentation fixes the
  radial coordinate. It is independent of the source point in the fiber.
- `QuaternionicHopfModelRadialDerivative` proves the original chain-rule
  factorization. `QuaternionicHopfOriginalNormalFrame` then proves that
  the ORIGINAL `SphereFiberNormalFrame.normalFrame`, in its constructed
  regular-fiber atlas, is exactly the computed quaternionic frame
  precomposed with that fixed augmented coordinate inverse.
- `original_southNormalFrame_parametrized` retains the actual
  `southFiberDiffeomorph`. The transverse formula is right quaternion
  multiplication in the first axis, with the fixed target vectors and
  factor two retained explicitly. The radial formula gives the actual
  ambient radius vector. No target basis change is silently discarded.

The model-chart/radial-extension frame comparison is now complete.
Transport through the ORIGINAL suspension and smash, evaluation of the
geometric Arf invariant, sixth-stem nontriviality and generation, the
candidate collapse's vanishing, framed filling, and unconditional smooth
rigidity remain unproved.


### Earlier checked nonbasepoint Hopf fiber and computed normal frame

- `QuaternionicHopfSouthFiber` constructs the literal south pole and
  proves that it differs from the based north pole. Its entire Hopf
  fiber is the second quaternion axis, with explicit S3 parametrization
  and inverse.
- `QuaternionicHopfSouthDifferential` computes the full ambient
  differential along that fiber. In transverse first-quaternion
  directions it is `w -> 2 w conjugate(b)`. The explicit tangent
  right inverse proves that south is an ORIGINAL native regular value.
  `QuaternionicHopfSouthDiffeomorph` identifies its constructed
  regular-fiber atlas with standard S3 and retains the ambient inclusion.
- `QuaternionicHopfSouthNormalEquations` adds the actual source norm
  equation to the quaternion tail of the actual Hopf polynomial.
  Its differential, kernel, and unique orthogonal right inverse are
  computed. In quaternion coordinates that inverse sends `(r,w)` to
  `(w b / 2, r b / 2)`.
- `QuaternionicHopfSouthNormalFrame` constructs the smooth normal
  frame induced by those equations on the actual S3 parametrization,
  using the orthogonal complement of its ORIGINAL inclusion derivative.
  `southNormalFrame_transverse` proves the exact right-multiplication
  twist. The equations isolate precisely this fiber in the negative
  hemisphere; their unrestricted zero set is not asserted to be a
  single fiber.
- `QuaternionicHopfSouthTargetChart` proves that the literal quaternion
  tail is a smooth local target coordinate at south. It also retains
  the equality between the ambient equations restricted to S7 and
  these coordinates of the ORIGINAL Hopf map, and proves that the
  defining differential applied to the computed frame is the identity.

The model-chart comparison that was missing at the nonbasepoint-fiber
checkpoint is now proved by the original-normal-frame comparison above.
The original suspension/smash framing comparison, geometric Arf value,
sixth-stem nontriviality and generation, collapse vanishing, framed filling,
and unconditional smooth rigidity remain unproved.


### Earlier checked original unit Hopf coordinate

- `QuaternionicHopfFiberDivision` and `QuaternionicHopfFiberAction`
  prove continuous, unique right unit-quaternion division between
  points in the same actual Hopf fiber. The seven-sphere is never
  assigned an associative group structure.
- `QuaternionicHopfCubeBoundary` and `QuaternionicHopfConnecting`
  construct the actual native connecting map and prove independence
  from both lift choice and based-cube representative.
  `QuaternionicHopfConnectingHom` proves its native group law.
- `QuaternionicHopfFiberExactness` and `QuaternionicHopfBaseExactness`
  prove exactness for the ORIGINAL Hopf projection and fiber inclusion.
  A fiber-valued right-action correction closes a lift when its terminal
  face is nullhomotopic. In degree six the connecting map is surjective,
  using the checked vanishing of pi6(S7).
- For nonzero m, `CyclicKernelPrimitiveCoordinate` proves that a map from Z to
  Z x Z/m whose image is the kernel of a map to Z/m has primitive
  free coordinate. It uses exactness and equal finite torsion groups,
  not an assigned value or a change of marking.
- `QuaternionicHopfUnitCoordinate` proves `hopfNumber_natAbs` in namespace
  `NoExoticSixSphere.QuaternionicHopf`, namely
  `hopfNumber.natAbs = 1` for the EXPLICIT smooth polynomial and the
  ORIGINAL James--Hopf homomorphism. The source is the actual native
  identity sphere generator. `suspendedSmashClass_eq` now identifies
  its actual suspended smash square with the canonical sixth-stem
  square WITHOUT a Hopf-coordinate hypothesis.

This completes the original Hopf-coordinate comparison. Nontriviality
and generation of the sixth-stem square, its geometric Arf detection,
vanishing of the candidate six-sphere's collapse class, framed filling,
and unconditional smooth rigidity remain unproved.

### Earlier checked homotopy lifting for the explicit quaternionic Hopf map

- `QuaternionicHopfProjectionAlgebra` proves the rank-one quaternionic
  projection identities and recovers the literal Hopf polynomial from
  the image equations on unit quaternion pairs.
- `QuaternionicHopfProjectionOperator` gives the continuous operator
  family on the ORIGINAL Euclidean eight-space. On a vector in its
  original Hopf fiber, the operator is exactly twice that vector.
- `QuaternionicHopfLocalTransport` normalizes this projected vector.
  Operator-norm closeness proves nonvanishing; the image equations
  prove that the result lies over the prescribed target point. The
  diagonal transport is exactly the identity.
- `QuaternionicHopf.exists_homotopy_lift` now lifts compact homotopies
  under the ACTUAL smooth polynomial, with prescribed initial lift
  and every stationary parameter fixed. This is not the different
  quaternionic projection from Sp(2) to S7.

The lifting checkpoint alone did not construct the exact sequence or
compute the Hopf coordinate. Those two steps are now proved in the
explicit Hopf exact-sequence and unit-coordinate modules described above.
The sixth-stem/Arf and smooth-classification gaps remain.


### Earlier checked original lift squares and an actual smooth Hopf fiber

- `SphereSmashNativeCubes` constructs the actual sixteen-cube pairing
  of two native pi8(S5) classes, using the original sphere pairing and
  retaining all collapsed faces and relative homotopies.
  `SphereSmashNativeBilinear` proves exact concatenation identities
  and hence a homomorphism in each variable.
- `ThirdStemSmashParity.product_coordinates` evaluates that actual
  pairing in terms of the checked Z/24 coordinates and the previously
  constructed square class. The intrinsic twelfth-power test identifies
  odd coordinates. `original_lift_product` proves that all original
  Hopf-coordinate-one lifts give the same native sixth-stem product,
  including lifts of order eight. This does not require the arbitrary
  lift itself to generate Z/24.
- `OriginalHopfSixthSquare.sphereClass_square` retains the ORIGINAL
  James--Hopf homomorphism on pi7(S4), either sign of a unit Hopf
  coordinate, the original product suspension, and the actual smash
  square. It is a comparison theorem when that original coordinate is
  known to have absolute value one.
- `QuaternionicHopfPolynomial` constructs the explicit polynomial
  `(a,b) -> (normSq a - normSq b, 2 a conjugate(b))` as a smooth map
  between the literal standard S7 and S4. Its norm identity is proved.
  `QuaternionicHopfNorthFiber` identifies the entire north fiber with
  the first quaternion axis, with a smooth S3 parametrization and an
  explicit continuous inverse.
- `QuaternionicHopfTransverseDifferential` computes the original
  polynomial differential in the second-coordinate directions as
  `w -> (0, 2 a conjugate(w))`. Its explicit tangent right inverse and
  `SphereAmbientSubmersion` prove the ORIGINAL native derivative is
  surjective along the whole north fiber.
  `QuaternionicHopfFiberDiffeomorph.fiberDiffeomorph` identifies the
  constructed regular-fiber atlas with standard S3, retaining its
  exact ambient inclusion.
- `QuaternionicHopfNativeClass` checks the literal standard poles,
  defines the explicit polynomial's actual based native class, and
  measures `QuaternionicHopf.hopfNumber` by the original James--Hopf map.
  That definition alone did not compute the integer. The later theorem
  `QuaternionicHopf.hopfNumber_natAbs` now proves its absolute value is one,
  and `QuaternionicHopf.suspendedSmashClass_eq` discharges the coordinate
  hypothesis of the earlier comparison theorem.

Nontriviality and generation of the sixth-stem square, its geometric
Arf comparison, the original six-sphere collapse's vanishing, and
unconditional smooth rigidity remain unproved. The explicit regular
fiber and its smooth atlas do not supply these missing statements.

### Earlier checked actual sixth-stem squares of order at most two

- `HigherCubeCircleExtension` and `HigherHopfNativeEquivalence` extend
  the ORIGINAL Hopf projection's native isomorphism to every degree
  at least three, retaining its actual map and based cube lifts.
  `SphereTwoHigherHopf.piSixSphereTwoMulEquiv` gives native pi6(S2)
  as Z/12 through the original projection in standard sphere coordinates.
- `StableThirdCompositionSquare` chooses one based representative of
  the checked order-24 third-stem generator and uses its ORIGINAL
  product suspensions thereafter. The actual composites S(k+14) to
  S(k+8) give compatible native and stable sixth-stem classes.
- `SphereSmashSquare` descends the actual product map through the
  original sphere pairing. The eight-coordinate source block exchange
  has positive sign; the five-coordinate target block exchange has
  negative sign. The original native source and target sign formulas
  prove that the actual smash-square class in pi16(S10) has square one.
- `IteratedProductSphereCoordinates` and
  `SixthStemSquareComparisonCoordinates` prove the exact comparison
  with the original iterated product suspensions, including collapsed
  boundary faces. The middle S13 permutation is based homotopic to the
  identity. The final S10 permutation acts by inversion.
  `SixthStemCompositionSquareOrder` therefore proves
  `SixthStemSmashSquare.nativeClass = (StableThirdComposition.squareClass 2)⁻¹`,
  `StableThirdComposition.stableSquare_pow_two`, and
  `StableThirdComposition.squareClass_pow_two k` for every original
  stable-range representative.

These are order bounds, not exact orders. The square class is NOT yet
proved nontrivial, and it is NOT yet proved to generate the sixth stem.
No identification of the entire sixth stem with Z/2 or geometric Arf
detection is asserted. The original six-sphere collapse is still not
proved stably nullhomotopic.

### Earlier checked original attaching parity and cyclic order twenty-four

- `JamesAttachingNativeLift` chooses a based sphere representative of
  the inverse ORIGINAL ordered James comparison of `correctedSevenClass`.
  Equality of actual native classes gives its based comparison homotopy
  with the original corrected smash map. The checked finite-domain
  homotopy-reflection theorem then gives an actual homotopy in the James
  space to the four-letter word on S3 x S3. No equality on homology is
  used as a substitute for this homotopy.
- `SmoothSphereGroupInversion` identifies original cube reflection
  with pointwise inversion by a genuine based sphere homotopy.
  `JamesAttachingQuaternionHomotopy` evaluates the four-letter word in
  unit quaternions, compares it with the ordinary commutator, and applies
  the existing `Samelson.fixWedge` to fix both axes at every time.
- `JamesAttachingQuaternionClass` checks all six original cube
  coordinates and collapsed faces. Its boundary-relative homotopy gives
  `correctedQuaternionSphere_class = QuaternionSamelson.nu` in native
  pi6 of unit quaternions. `corrected_retraction_eq_nu` and
  `originalAttaching_retraction_eq_nu_or_inv` identify the ORIGINAL
  sphere retraction through the actual pointed quaternion homeomorphism.
- `SphereFiveEighth.torsionParity_eq_one` proves that the
  ORIGINAL attaching relation's torsion coordinate has parity one.
  The quaternionic class has proved order twelve and is not a square;
  its inverse is also not a square. The checked retraction/parity test
  therefore applies independently of the noncanonical Hopf lift.
- `StableThirdCyclicGroup` proves that native pi8(S5) is cyclic of
  order 24 and supplies `SphereFiveEighth.groupEquiv` with Z/24.
  `StableThirdAttaching.groupEquiv k` gives the same result for every
  native pi(k+8)(S(k+5)), and `groupEquiv_stepHom` retains the ORIGINAL
  suspension maps. Cyclicity uses an element with nontrivial twelfth
  power together with the injected order-twelve torsion subgroup.
  The arbitrary Hopf-coordinate lift itself is NOT claimed to generate:
  its order could be eight rather than twenty-four.

### Earlier checked prerequisites retained

- The actual attaching Hopf coefficient has absolute value two.
  Native pi7(S4) has the proved Z x Z/12 marking; the original relation
  presents pi8(S5), and the original suspensions transport it thereafter.
- The literal quaternion cube is primitive. The explicit seven-sphere
  commutator lift has degree of absolute value one, proved using its
  original local charts, unique antipodal fiber, and relative homology.
  Its connecting image proves that the original Samelson class generates
  native pi6(S3), has order twelve, and is not a square.
- The actual James comparison induces all-degree native isomorphisms
  for sphere dimension at least two. Exact disk-side lifting and an
  explicit homotopy-pullback fiber equivalence give homotopy reflection
  on finite-cell domains, including S3 x S3 with its actual product atlas.
- The genuine framed embedding and collapse of a candidate six-sphere
  are constructed. A manifold homeomorphic to S6 has geometric Arf
  invariant zero. This is not yet a stable-nullhomotopy theorem.
- `CubicalStableSix.piFourteenSphereEightMulEquiv` identifies the
  actual stable sixth-stem group with native pi14(S8).
  `SixSphereThirteen.stableClass_eq_one_iff_suspendedNativeClass`
  reduces the original collapse's stable vanishing to its actual first
  suspended native class. That class is NOT proved to be the identity.
- The framed-filling and recognition constructions retain the original
  manifold atlas but still require the missing nullhomotopy. The nearby
  `smale_theorem_a` proves a homeomorphism, not a diffeomorphism.

### Remaining proof obligations

1. Prove generation of the entire sixth stem by the original square class,
   the stable sixth-stem/Arf detection calculation, and its
   comparison with the actual geometric collapse class. Apply the
   proved geometric Arf-zero result to obtain stable vanishing and a
   finite nullhomotopy. A group calculation alone does not supply the
   geometric Arf comparison.
2. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity` for the original atlas with
   no additional hypotheses.

The full metastable EHP results may be used only within their proved
dimension bounds. Any additional sphere-group computation, map formula,
or larger EHP range required by the sixth-stem argument must be proved.
See `JamesHomotopyComparisonPlan.md` for the current exact maps and bounds.
Historical records below describe earlier checkpoints, not current status.

### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 13260 jobs.
- All 17547 dependency reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`, or no axioms.
- The source scan covers 2819 task files and
  8681 local root-import files
  (8684 distinct scanned paths including configuration).
  No proof placeholders, added axioms, unsafe declarations, native
  evaluation shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.

## Historical checkpoints

### Checkpoint 13412 — archived status snapshot

The following is historical, including its then-missing steps.

#### Current checked milestone — 13412 dependency audits

The unconditional theorem `SixSphereRigidity` remains unproved.

##### Latest checked result: finite-domain homotopy reflection

- `NativeEquivalenceDiskLifting.relativeDiskLifting_of_native_bijective`
  proves exact disk lifting from the original native homotopy-group
  bijections. The prescribed source boundary and the entire target-side
  homotopy are retained, including their endpoints. Source boundary
  extension is proved using native injectivity, not assumed.
- `HomotopyPullbackFiberEquivalence.projectionFiberEquiv` constructs
  an actual homotopy equivalence between the left projection's fiber
  and the original map's fiber. Both inverse homotopies are checked.
  The original fiber exact sequence then proves the path-space diagonal
  induces native bijections. Existing finite-cell lifting for that
  diagonal reflects actual homotopies through the original map.
- `JamesComparisonHomotopyReflection` specializes this to the actual
  James comparison, compact smooth manifolds, and the literal product
  S3 x S3. The ordered version cancels the genuine coordinate-reordering
  homeomorphism. No global homotopy equivalence of the James space
  with a loop space is assumed. The original attaching-class/quaternion
  comparison is still missing; torsion parity is not yet evaluated.

##### Checked native degree, Samelson order, and retraction parity

- `QuaternionCommutatorNativeGenerator.quaternionClass_generates`
  proves that the literal quaternion cube is primitive. Its possible
  sign cancels in the Samelson square, so `connecting_sphereClass_nu`
  identifies the ORIGINAL connecting image with `QuaternionSamelson.nu`.
- `QuaternionCommutatorBlockChart`, `QuaternionCommutatorCubeCoordinates`,
  and `QuaternionCommutatorNativeCharts` compare the actual cube charts
  with the centered quaternion charts, retaining the reversed lift time.
  `QuaternionCommutatorNativeLocalHomeomorph.localModel_eq_sphereMap`
  gives an actual local homeomorphism for the ORIGINAL descended map
  at its unique antipodal preimage.
- `LocalHomeomorphMapHomology` proves the original relative homology
  map bijective using the actual neighborhood excision diagram.
  Contractible punctured spaces and absolute/relative naturality then
  give bijectivity of the original absolute homology map above degree one.
- `QuaternionCommutatorNativeHomology.degreeMap_degree_natAbs`
  proves degree of absolute value one for the literal sphere map.
  `QuaternionCommutatorNativePrimitivity.sphereClass_generates` and
  `sphereClass_degree_natAbs` retain its native class and original
  quaternionic degree marking. No arbitrary representative is assigned
  the checked local regularity or degree.
- `nu_generates` proves that the ORIGINAL Samelson class generates
  pi6(S3). `QuaternionSamelsonOrder.orderOf_nu` proves exact order 12,
  and `square_ne_nu` proves it is not a square. The ORIGINAL James
  attaching torsion comparison remains missing, so the third-stem
  parity value and the main theorem are still unproved.

- `JamesQuaternionRetractionParity.originalAttaching_parity` proves
  that the ORIGINAL relation's torsion parity is the parity of its
  actual quaternion James-retraction image. The noncanonical Hopf-lift
  contribution is multiplied by plus or minus two and disappears
  modulo two. `originalAttaching_square_iff_parity` gives an exact test:
  this parity is zero iff the actual retracted attaching class is a
  square in pi6(S3). Its geometric comparison with the nonsquare
  Samelson generator is still missing; the parity value is not proved.

##### Checked local regularity and explicit native sphere map

- The actual first-column derivative in centered quaternion sphere
  charts is (a,v,w) -> (-v,4a+w), with v,w imaginary quaternions.
  `QuaternionCommutatorTangentEquiv.tangentEquiv` proves that the
  resulting map between the actual seven-dimensional tangent spaces
  is a continuous linear isomorphism.
- `SphereCenteredChartDifferential.hasFDerivAt_chart` identifies the
  target stereographic derivative with the genuine tangent projection.
  `QuaternionCommutatorLocalRegularity.localHomeomorph` applies the
  inverse function theorem to the actual coordinate expression, with
  zero in both source and target. No regularity hypothesis is assumed.
- `QuaternionCommutatorNativeSphere` constructs explicit quaternion
  three-cubes using the ORIGINAL smooth-interior sphere quotient and
  quaternion coordinate homeomorphism. Its seven-loop descends to an
  actual map on the standard seven-sphere, retaining its exact native
  connecting image as the Samelson square of this explicit input class.
- `sphereMap_unique_antipodal_fiber` proves that this actual descended
  sphere map has exactly one antipodal preimage. This goes beyond the
  previously checked interval-product fiber calculation.
- The native chart transport, explicit three-cube primitivity,
  absolute degree one, and Samelson generation are now proved above.
  The ORIGINAL attaching torsion comparison and main theorem remain
  unproved.

##### Checked commutator lift and product fiber

- `QuaternionCommutatorRotation` constructs real rotations in the
  ORIGINAL unitary quaternion matrix group Sp(2). Conjugation through
  a quarter-turn moves the fiber inclusion to the first diagonal block,
  which commutes with the original fiber. The resulting commutator
  contraction fixes every input with either quaternion equal to one.
- `QuaternionCommutatorBoundaryLift` reverses that family to give an
  actual `QuaternionicFibration.CubeLift` of a native seven-loop.
  `connecting_fundamentalProjectedLoop` identifies its ORIGINAL
  connecting image with the genuine quaternion Samelson square, via
  the proved pointed fiber homeomorphism. No degree is assigned to it.
- `QuaternionCommutatorColumns` calculates the literal matrix entries
  and their real parts. `QuaternionCommutatorAntipodalFiber` proves
  `contraction_antipode_iff`: the first-column map hits the south pole
  exactly at the interval midpoint with both quaternion inputs minus one.
- Local regularity, native sphere transport, absolute degree one,
  and generation of pi6(S3) by the original Samelson class are proved.
  Its comparison with the ORIGINAL attaching torsion coefficient is
  still missing. The parity gap is not closed.

##### Checked order 24 and intrinsic parity test

- `TwoResiduePresentation.normalEquiv` proves unique representatives
  with integer coordinate zero or one for a single relation whose
  integer coefficient has absolute value two.
- `SphereFiveEighth.cardinality` and `StableThirdAttaching.cardinality`
  apply this to the ORIGINAL attaching presentation: pi8(S5) and every
  later third-stem stage have exactly 24 elements. These are actual
  native homotopy groups, transported by the original suspensions.
- `StableThirdParityCriterion` proves the original suspended torsion
  inclusion is injective, and its elements have twelfth power one.
  The Hopf-coordinate lift has twelfth power one exactly when the
  original relation's torsion coordinate has zero parity in Z/2.
  Changing the Hopf lift by any torsion class preserves this test.
- The required nonzero parity is NOT proved. Cardinality 24 is not
  being used as a substitute for cyclicity or an identification with Z/24.

##### Checked original attaching Hopf coefficient

`AttachingSquare.originalAttachingClass_hopf_natAbs_two` proves
`Int.natAbs SphereFiveEighth.relation.1.toAdd = 2` for the ORIGINAL
attaching relation. This is a proved numerical value, not a hypothesis.
Its torsion coordinate is still unevaluated.

- `SixthWordSum.wordMap_homology` proves that the actual finite-word
  presentation on S6 letters induces the sum of the actual one-letter
  coordinate maps in H6. It uses genuine product homology splittings
  and proved five-connectivity of the sphere products. No global
  continuous multiplication on the full James space is assumed.
- `SphereSixCube.identity_generates` proves that the original smooth
  cube quotient represents a primitive native pi6(S6) class. Its genuine
  Hurewicz image is the previously constructed S6 top class or its
  negative. No cube orientation or triangulation sign is assumed.
- `SphereSixCube.reflection_homology` and `blockSwap_homology` prove
  the actual H6 signs. The original sphere pairing respects these
  reflections and block exchanges in every coordinate, including all
  collapsed faces.
- `HopfPairTerms.term_productGenerator` evaluates the six actual pair
  terms as top, zero, top, negative top, zero, top. The zero terms factor
  through S3. The finite-word sum therefore gives twice the actual
  one-letter S6 homology class.
- `hopf_six_bijective` proves that the ORIGINAL Hopf map J(S3) -> J(S6)
  is an H6 isomorphism. It uses the actual two-letter word/pairing
  square and the original one-letter inclusion. Canceling this map
  gives `fourWord_productGenerator`, exactly twice the primitive
  `SecondCell.generator` in H6(J(S3)).
- `meridian_adjoint_eq_two_or_neg` transports that calculation through
  the actual ordered loop comparison and original native cube. The
  proved attaching-class/Hopf comparison then gives absolute coefficient
  two for the ORIGINAL relation. No native torsion-class equality is
  inferred from this homology calculation.

##### Earlier checked prerequisites

- The actual source contraction, sphere-product descent, smash pairing,
  Moore commutator homotopy, and source-generator comparisons are proved.
  The original attaching class equals its corrected source class or its
  inverse, and their actual Hopf coordinates are retained.
- The original metastable EHP sequence is established within its proved
  bounds. Native pi7(S4) is marked as Z x Z/12, with the first coordinate
  equal to the original James--Hopf coordinate.
- The original attaching relation presents pi8(S5), and actual
  suspension transports the same presentation through the third stable
  stem. The integer coefficient now has absolute value two, but the
  torsion parity and a conclusion of Z/24 remain unproved.
- The actual framed sphere collapse class and geometric Arf invariant
  are constructed. A homeomorphic six-sphere has geometric Arf zero.
  Stable vanishing and the finite collapse nullhomotopy do not yet follow.
- Framed filling and smooth recognition retain the original manifold
  atlas but still need that nullhomotopy. The neighboring
  `smale_theorem_a` concludes a homeomorphism, not a diffeomorphism.

##### Remaining proof obligations

1. Determine the ORIGINAL attaching relation's torsion parity, retaining
   the noncanonical Hopf-generator lift. The absolute integer coefficient
   two is proved. Compute the actual quaternion James-retraction image
   of that original attaching class, using the checked square/parity
   criterion. Finish the remaining third-stem group calculation and
   prove every additional homotopy result or EHP range used.
2. Prove the stable sixth-stem/Arf detection calculation and apply it to
   the actual sphere collapse class. Construct its finite nullhomotopy;
   the proved geometric Arf zero alone is not the detection theorem.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity` with no additional hypotheses.

These are substantial mathematical gaps, not just elaboration cleanup.
See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below describe earlier checkpoints, not current status.

##### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 8600 jobs.
- All 13412 dependency reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`, or no axioms.
- The source scan covers 2181 task files and
  4412 local root-import files
  (4415 distinct scanned paths including configuration).
  No proof placeholders, added axioms, unsafe declarations, native
  evaluation shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.

### Checkpoint 12973 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- The source contraction's attaching tracks respect the two original
  tail-sphere quotients at every time. `sphereLoopHomotopy` descends
  the corrected loop family jointly to the actual product of spheres.
  The common constant loop stays fixed. At the terminal time, the
  whole sphere fat wedge is constant.
- `TwoLetterHomology.pairing_six_bijective` proves that the ORIGINAL
  pairing S3 x S3 -> S6 induces a sixth-homology isomorphism.
  The inverse image of the genuine S6 top class is `productGenerator`;
  its actual two-letter word image is exactly `SecondCell.generator`.
  The finite James-stage splitting supplies this result without an
  assumed cross-product or orientation convention.
- `correctedSmashSphere_homology` identifies the actual sixth-homology
  maps of the corrected attaching family and the Moore smash commutator.
  `pairing_tail_cube` retains all six original cube coordinates and
  collapsed faces. Hurewicz naturality gives `correctedCube_hurewicz`.
- `originalAttachingClass_eq_corrected_or_inv` proves that the ORIGINAL
  attaching class is `correctedSevenClass` or its inverse. The cube
  identity's primitive generator property and both source signs are
  proved, not supplied as hypotheses.
- `orderedLoopComparison` is the actual James map followed by the
  coordinate-ordered loop-space homeomorphism. It induces homology
  isomorphisms and its native currying equals the ORIGINAL comparison.
  `correctedSevenClass_adjointClass` consequently identifies the two
  genuine James-adjoint Hurewicz classes.
  `originalAttachingClass_hopf_natAbs` proves that the original relation's
  absolute integer coordinate equals the actual meridian commutator's.
  No equality of their native torsion coordinates is inferred.
- `SmoothCube.reflection` is an actual sphere homeomorphism descended
  from one-coordinate cube reversal. Precomposition acts by inversion
  on native homotopy classes. `reverse_native` proves the corresponding
  statement for path reversal. `reversed_meridians` constructs the
  needed Moore-family homotopy through the actual normalization maps.
- `commutator_fourWord_homology` replaces the meridian commutator on
  homology by the actual four-letter word x, y, rho(x), rho(y).
  `hopf_fourWordMap` gives its six paired letters in their original
  right-lexicographic order. `ProductSixthHomology.map_product` proves
  the actual factor-sum formula for five-connected product spaces.
  The numerical coefficient 2 is NOT yet proved by these results.

#### Earlier checked prerequisites

- The original metastable EHP sequence is established in the proved
  bounds. The native pi7(S4) is marked as Z x Z/12, with the first
  coordinate equal to the original James--Hopf coordinate.
- The original attaching relation presents pi8(S5), and actual
  suspension transports that same presentation through the third
  stable stem. Its numerical integer coefficient and torsion parity
  are not yet evaluated; Z/24 is not yet a proved conclusion.
- The actual framed sphere collapse class and geometric Arf invariant
  are constructed. A homeomorphic six-sphere has geometric Arf zero.
  Stable vanishing and the finite collapse nullhomotopy do not yet follow.
- The framed filling and smooth recognition work retains the original
  manifold atlas, but still needs that nullhomotopy. The neighboring
  `smale_theorem_a` concludes a homeomorphism, not a diffeomorphism.

#### Remaining proof obligations

1. Finish the numerical attaching calculation. For the six-term Hopf
   word, prove the two self-pair terms vanish, evaluate the four mixed
   terms with the actual reflection and block-swap signs, and combine
   them using actual homology maps. Retain the primitive sphere/cube
   generator comparison. Then determine the original relation's torsion
   parity, accounting for the noncanonical Hopf-generator lift, and
   prove every additional sphere-group result or EHP range used.
2. Prove the stable sixth-stem/Arf detection calculation and apply it to
   the actual sphere collapse class. Construct its finite nullhomotopy;
   the proved geometric Arf zero alone is not the detection theorem.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity` with no additional hypotheses.

These are substantial mathematical gaps, not just elaboration cleanup.
See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below describe earlier checkpoints, not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 8539 jobs.
- All 12973 dependency reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`, or no axioms.
- The source scan covers 2136 task files and
  4351 local root-import files
  (4354 distinct scanned paths including configuration).
  No proof placeholders, added axioms, unsafe declarations, native
  evaluation shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12835 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `AttachingSquare.fullBoundaryHomeomorph` identifies the whole
  clock-and-tail boundary with the ORIGINAL characteristic boundary.
  It restricts literally to both earlier face parametrizations and sends
  the zero point to the original selected characteristic corner.
- `collapsedFacesData` proves homotopy extension for the union of the
  tail-boundary faces and the zero-clock face. The corner neighborhood
  motion preserves the clock perimeter, so product neighborhood data
  restricts to the actual full boundary. `collapsedContraction` first
  zeros the clocks, then contracts the tails; it fixes the original corner.
- `sourceExtension_faces` retains all prescribed contraction tracks.
  `sourceCollapse_map_bijective` proves that collapsing these actual faces
  preserves every native homotopy class. `sourceAttachingHomotopy` factors
  the ORIGINAL attaching map through this quotient by a based homotopy.
- `perimeter_eq_iff` and `perimeter_surjective` prove the exact fibers of
  the actual left-associated clock path. `cubeSourceMap` consequently
  collapses exactly the native cube boundary and has singleton other
  fibers. `sourceSphereHomeomorph` identifies its quotient with the
  standard sphere, retaining the leading clock and original tail coordinates.
- `sourceAttaching_comparison` retains the actual native maps under this
  source equivalence. `fourSourceSign_natAbs` proves its seventh-sphere
  generator coefficient has absolute value one.
  `originalAttachingClass_eq_or_inv` proves that the ORIGINAL S4 attaching
  class is `sourceFourAttachingClass` or its inverse. No orientation sign
  is assumed. Equality with the previously constructed Moore commutator
  still requires compatibility of the prescribed boundary contractions;
  the numerical Hopf coefficient and torsion parity remain unproved.
- `AttachingSquare.boundaryMap` inserts the two original suspension
  clocks and tail cubes into the actual max-norm characteristic boundary.
  Its four edge formulas evaluate the ORIGINAL attaching map exactly.
  `trace_commutator` identifies the full oriented perimeter with the two
  ordered meridians followed by their reversals, as actual native paths.
- `Moore.Loop.commutatorNormalizationHomotopy` adjusts durations at the
  three multiplication vertices. It compares the actual normalized
  Moore commutator with the left-associated native path commutator,
  continuously including zero durations and fixing the common constant
  loop. No strict inverse identity is imposed on the Moore monoid.
- `AttachingSquare.traceToSmashHomotopy` connects that ORIGINAL attaching
  trace to the previously constructed smash commutator. It retains the
  original cube quotients, sphere pairing, meridians, normalization, and
  target reordering, and fixes all parameters with both tail spheres at
  their poles. Its terminal map is constant whenever either tail cube
  is on its boundary. This family homotopy does NOT alone identify the
  original attaching class with the chosen Moore commutator class.
- `AttachingSquare.tailNullhomotopy` contracts the actual attaching map
  on the union of the remaining tail-boundary faces by moving both
  clocks to zero. It fixes the zero-clock face and agrees literally with
  the perimeter parametrization on their overlap. Coherence with the
  prescribed commutator-axes contraction remains to be proved before
  the Moore commutator-class identification. The source quotient and
  its primitive generator comparison are now checked separately above.
- `quotient_homology_bijective_above` proves that the ORIGINAL full James
  quotient preserves integral homology above degree n+1. The actual pair
  sequence and quotient naturality discharge the absolute comparison.
- `SphereFourHopfHomology.wordIntegerEquiv` marks the actual H6 of J(S3)
  by Z. `coordinate_hurewicz` identifies the first coordinate of every
  actual `pi_7(S^4)` class with the sixth Hurewicz class of its James
  adjoint. `attaching_coordinate` applies this to the fixed attaching
  relation. Vanishing of this homology class is equivalent to belonging
  to the original suspended `pi_6(S^3)` image.
- `SecondCell.generator` comes from the actual bottom S6 of J(S3)/S3 and
  its genuine sphere top class. It generates H6(J(S3)); its Hopf-compatible
  integer coordinate has absolute value one. The normalization proof
  passes at the default heartbeat limit after separating the elementary
  integer-equivalence argument. No orientation sign or attaching
  coefficient is assigned.
- `MooreLoopReversal`, `MooreLoopCancellation`, and `MooreLoopCommutatorAxes`
  construct continuous reversal and both based cancellation homotopies,
  including duration zero. The actual commutator contracts on the whole
  two-axes union while fixing their common identity point. No strict
  inverse law for the Moore-loop monoid is asserted.
- `SphereMooreCommutator` extends that prescribed axes contraction over
  the actual sphere product using the proved fat-wedge cofibration.
  Its terminal map descends through the ORIGINAL sphere pairing, with
  exact pole value and a based homotopy from the original commutator.
  `MeridianCommutator.fourLoop` is the resulting explicit native seven-
  cube in S4 for the original Moore meridians. Its class has NOT yet been
  identified with the original attaching class or numerically evaluated.
- `SphereFourAttaching.attachingClass` is the image of the proved integral
  generator of the original `pi_7(S^7)` under the actual S4 second-cell
  attaching map. `suspension_eq_one_iff` proves that its integer powers
  are exactly the kernel of the ORIGINAL suspension to `pi_8(S^5)`.
  `quotientEquiv` identifies the quotient by this cyclic subgroup with
  that native eighth group, and its representative formula is suspension.
- `SphereFiveEighth.presentationEquiv` transports this exact presentation
  to `(Z x Z/12) / <relation>`. The relation is defined by the actual
  attaching class, not supplied as a hypothesis. Its first coordinate
  is the marked original James--Hopf image. The proved null-class test
  is the pair of integer and mod-12 equations for an integer multiple
  of that relation. Neither numerical coordinate has been evaluated.
- `StableThirdAttaching.fromFirst` recursively composes the original
  native suspensions, each proved bijective, from `pi_8(S^5)` to every
  `pi_(k+8)(S^(k+5))`. The same actual relation presents all these stages
  and detects the kernel of every iterated suspension from `pi_7(S^4)`.
  This does not yet identify the third stem with Z/24 and does not compute
  the sixth stem or the Arf detection map.
- `UnitalAttaching.nullhomotopy` contracts the actual second James-cell
  attaching map whenever the original sphere has a continuous unital
  multiplication. It uses the two original characteristic blocks and
  fixes the actual corner. Associativity is not assumed. The induced
  attaching homomorphisms vanish in every positive degree, and the
  original EHP connecting maps vanish in the established metastable range.
- `ThreeAttaching.multiplication` is genuine quaternion multiplication
  in the original three-sphere coordinates, with both pole-unit laws
  proved. Thus its actual attaching map is based-nullhomotopic and the
  three-sphere connecting maps vanish in the required finite range.
- `ThreeRetraction.retraction` evaluates actual James words in the unit
  quaternions. It is continuous and retracts the original sphere inclusion
  literally. Transport through the checked all-degree James comparison
  gives `sectionHom_suspension`, a left inverse of the original suspension
  on every positive native group of S3. This does not extend the EHP range.
- `SphereFourSeventh.groupEquiv` proves the native group
  `pi_7(S^4) = Z x Z/12`. The first coordinate is the original James--Hopf
  map under the checked integer marking of `pi_7(S^7)`. Original suspension
  from `pi_6(S^3)` maps to the second coordinate with its checked Z/12
  marking. The short exact sequence splits using a chosen lift of the
  Hopf generator; no canonical quaternionic Hopf-map identification is
  asserted. The S4 attaching-map value and stable sixth stem remain open.
- `IntegralSplitting` proves the missing marked integral direct-sum
  helper and retains the supplied inclusion as its first summand. Explicit
  imports repair two existing surgery dependencies exposed by the combined
  build. Both callers and their downstream root dependencies now compile.
- `RoundCell.quotientHom_eq_suspension` identifies the original cell
  quotient homomorphism with the original cubical suspension through
  constructed based boundary and target homeomorphisms. The comparison
  uses the genuine round and max-norm disks and a based homotopy of their
  contractions. `quotientHom_bijective` proves the original map bijective
  for positive `n,d` with `d + 3 < 4n`.
- `EHPCell.comparisonHom_bijective` consequently parametrizes every input
  of the original EHP connecting map for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `connecting_comparisonHom` recovers the actual second-cell
  attaching homomorphism. `suspension_eq_one_iff_attaching` proves that
  the native suspension kernel is exactly this attaching-map image on
  the native groups of `S^(2n-1)`. No numerical attaching-map evaluation
  or stable sixth-stem calculation is inferred from this image formula.
- `CellBoundary.connecting_quotientGenLoop` now evaluates the original
  EHP connecting map on explicit second-cell representatives. The actual
  attaching map is lifted using straight contraction of its characteristic
  disk to the all-zero cube corner. The proved quotient-cube formula
  retains the leading path-time coordinate and the two original pairing
  blocks. Applying the connecting map to its suspension recovers exactly
  the original attaching map on the boundary representative. The
  comparison above now identifies its quotient homomorphism with cubical
  suspension through constructed based homeomorphisms. No orientation
  sign or numerical attaching-map calculation is inferred.
- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Calculate the actual source class's sixth-homology coefficient in
   the primitive second-cell basis and determine the torsion parity.
   The original attaching class is now proved equal to this source class
   or its inverse. A possible next route descends the source-corrected
   loop family to the product of tail spheres and compares homology;
   that descent and calculation are not yet proved. A full native-class
   comparison with the Moore commutator additionally requires compatible
   boundary tracks. Retain the noncanonical Hopf lift and prove all further
   sphere-group results or EHP ranges used by the calculation.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 8524 jobs.
- All 12835 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2121 task files and 4336 local root-import files
  (4339 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12705 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `AttachingSquare.boundaryMap` inserts the two original suspension
  clocks and tail cubes into the actual max-norm characteristic boundary.
  Its four edge formulas evaluate the ORIGINAL attaching map exactly.
  `trace_commutator` identifies the full oriented perimeter with the two
  ordered meridians followed by their reversals, as actual native paths.
- `Moore.Loop.commutatorNormalizationHomotopy` adjusts durations at the
  three multiplication vertices. It compares the actual normalized
  Moore commutator with the left-associated native path commutator,
  continuously including zero durations and fixing the common constant
  loop. No strict inverse identity is imposed on the Moore monoid.
- `AttachingSquare.traceToSmashHomotopy` connects that ORIGINAL attaching
  trace to the previously constructed smash commutator. It retains the
  original cube quotients, sphere pairing, meridians, normalization, and
  target reordering, and fixes all parameters with both tail spheres at
  their poles. Its terminal map is constant whenever either tail cube
  is on its boundary. This family homotopy does NOT yet identify the
  original boundary-sphere generator with the suspended smash generator.
- `AttachingSquare.tailNullhomotopy` contracts the actual attaching map
  on the union of the remaining tail-boundary faces by moving both
  clocks to zero. It fixes the zero-clock face and agrees literally with
  the perimeter parametrization on their overlap. Coherence with the
  prescribed commutator-axes contraction and the source-generator
  comparison remain to be proved before any attaching-class equality.
- `quotient_homology_bijective_above` proves that the ORIGINAL full James
  quotient preserves integral homology above degree n+1. The actual pair
  sequence and quotient naturality discharge the absolute comparison.
- `SphereFourHopfHomology.wordIntegerEquiv` marks the actual H6 of J(S3)
  by Z. `coordinate_hurewicz` identifies the first coordinate of every
  actual `pi_7(S^4)` class with the sixth Hurewicz class of its James
  adjoint. `attaching_coordinate` applies this to the fixed attaching
  relation. Vanishing of this homology class is equivalent to belonging
  to the original suspended `pi_6(S^3)` image.
- `SecondCell.generator` comes from the actual bottom S6 of J(S3)/S3 and
  its genuine sphere top class. It generates H6(J(S3)); its Hopf-compatible
  integer coordinate has absolute value one. The normalization proof
  passes at the default heartbeat limit after separating the elementary
  integer-equivalence argument. No orientation sign or attaching
  coefficient is assigned.
- `MooreLoopReversal`, `MooreLoopCancellation`, and `MooreLoopCommutatorAxes`
  construct continuous reversal and both based cancellation homotopies,
  including duration zero. The actual commutator contracts on the whole
  two-axes union while fixing their common identity point. No strict
  inverse law for the Moore-loop monoid is asserted.
- `SphereMooreCommutator` extends that prescribed axes contraction over
  the actual sphere product using the proved fat-wedge cofibration.
  Its terminal map descends through the ORIGINAL sphere pairing, with
  exact pole value and a based homotopy from the original commutator.
  `MeridianCommutator.fourLoop` is the resulting explicit native seven-
  cube in S4 for the original Moore meridians. Its class has NOT yet been
  identified with the original attaching class or numerically evaluated.
- `SphereFourAttaching.attachingClass` is the image of the proved integral
  generator of the original `pi_7(S^7)` under the actual S4 second-cell
  attaching map. `suspension_eq_one_iff` proves that its integer powers
  are exactly the kernel of the ORIGINAL suspension to `pi_8(S^5)`.
  `quotientEquiv` identifies the quotient by this cyclic subgroup with
  that native eighth group, and its representative formula is suspension.
- `SphereFiveEighth.presentationEquiv` transports this exact presentation
  to `(Z x Z/12) / <relation>`. The relation is defined by the actual
  attaching class, not supplied as a hypothesis. Its first coordinate
  is the marked original James--Hopf image. The proved null-class test
  is the pair of integer and mod-12 equations for an integer multiple
  of that relation. Neither numerical coordinate has been evaluated.
- `StableThirdAttaching.fromFirst` recursively composes the original
  native suspensions, each proved bijective, from `pi_8(S^5)` to every
  `pi_(k+8)(S^(k+5))`. The same actual relation presents all these stages
  and detects the kernel of every iterated suspension from `pi_7(S^4)`.
  This does not yet identify the third stem with Z/24 and does not compute
  the sixth stem or the Arf detection map.
- `UnitalAttaching.nullhomotopy` contracts the actual second James-cell
  attaching map whenever the original sphere has a continuous unital
  multiplication. It uses the two original characteristic blocks and
  fixes the actual corner. Associativity is not assumed. The induced
  attaching homomorphisms vanish in every positive degree, and the
  original EHP connecting maps vanish in the established metastable range.
- `ThreeAttaching.multiplication` is genuine quaternion multiplication
  in the original three-sphere coordinates, with both pole-unit laws
  proved. Thus its actual attaching map is based-nullhomotopic and the
  three-sphere connecting maps vanish in the required finite range.
- `ThreeRetraction.retraction` evaluates actual James words in the unit
  quaternions. It is continuous and retracts the original sphere inclusion
  literally. Transport through the checked all-degree James comparison
  gives `sectionHom_suspension`, a left inverse of the original suspension
  on every positive native group of S3. This does not extend the EHP range.
- `SphereFourSeventh.groupEquiv` proves the native group
  `pi_7(S^4) = Z x Z/12`. The first coordinate is the original James--Hopf
  map under the checked integer marking of `pi_7(S^7)`. Original suspension
  from `pi_6(S^3)` maps to the second coordinate with its checked Z/12
  marking. The short exact sequence splits using a chosen lift of the
  Hopf generator; no canonical quaternionic Hopf-map identification is
  asserted. The S4 attaching-map value and stable sixth stem remain open.
- `IntegralSplitting` proves the missing marked integral direct-sum
  helper and retains the supplied inclusion as its first summand. Explicit
  imports repair two existing surgery dependencies exposed by the combined
  build. Both callers and their downstream root dependencies now compile.
- `RoundCell.quotientHom_eq_suspension` identifies the original cell
  quotient homomorphism with the original cubical suspension through
  constructed based boundary and target homeomorphisms. The comparison
  uses the genuine round and max-norm disks and a based homotopy of their
  contractions. `quotientHom_bijective` proves the original map bijective
  for positive `n,d` with `d + 3 < 4n`.
- `EHPCell.comparisonHom_bijective` consequently parametrizes every input
  of the original EHP connecting map for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `connecting_comparisonHom` recovers the actual second-cell
  attaching homomorphism. `suspension_eq_one_iff_attaching` proves that
  the native suspension kernel is exactly this attaching-map image on
  the native groups of `S^(2n-1)`. No numerical attaching-map evaluation
  or stable sixth-stem calculation is inferred from this image formula.
- `CellBoundary.connecting_quotientGenLoop` now evaluates the original
  EHP connecting map on explicit second-cell representatives. The actual
  attaching map is lifted using straight contraction of its characteristic
  disk to the all-zero cube corner. The proved quotient-cube formula
  retains the leading path-time coordinate and the two original pairing
  blocks. Applying the connecting map to its suspension recovers exactly
  the original attaching map on the boundary representative. The
  comparison above now identifies its quotient homomorphism with cubical
  suspension through constructed based homeomorphisms. No orientation
  sign or numerical attaching-map calculation is inferred.
- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Prove the global source-generator comparison for the ORIGINAL S4
   attaching map, including coherence of the tail-face contraction and
   the prescribed axes tracks. The perimeter formula and its family
   homotopy to the smash commutator are now checked, but equality of the
   actual seventh homotopy classes is not. Compute the sixth-homology
   coefficient in the primitive second-cell basis and the torsion parity.
   The mod-12 coordinate depends on the chosen Hopf-generator lift.
   Prove further necessary sphere-group results and any additional EHP range.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 8512 jobs.
- All 12705 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2109 task files and 4324 local root-import files
  (4327 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12622 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `quotient_homology_bijective_above` proves that the ORIGINAL full James
  quotient preserves integral homology above degree n+1. The actual pair
  sequence and quotient naturality discharge the absolute comparison.
- `SphereFourHopfHomology.wordIntegerEquiv` marks the actual H6 of J(S3)
  by Z. `coordinate_hurewicz` identifies the first coordinate of every
  actual `pi_7(S^4)` class with the sixth Hurewicz class of its James
  adjoint. `attaching_coordinate` applies this to the fixed attaching
  relation. Vanishing of this homology class is equivalent to belonging
  to the original suspended `pi_6(S^3)` image.
- `SecondCell.generator` comes from the actual bottom S6 of J(S3)/S3 and
  its genuine sphere top class. It generates H6(J(S3)); its Hopf-compatible
  integer coordinate has absolute value one. The normalization proof
  passes at the default heartbeat limit after separating the elementary
  integer-equivalence argument. No orientation sign or attaching
  coefficient is assigned.
- `MooreLoopReversal`, `MooreLoopCancellation`, and `MooreLoopCommutatorAxes`
  construct continuous reversal and both based cancellation homotopies,
  including duration zero. The actual commutator contracts on the whole
  two-axes union while fixing their common identity point. No strict
  inverse law for the Moore-loop monoid is asserted.
- `SphereMooreCommutator` extends that prescribed axes contraction over
  the actual sphere product using the proved fat-wedge cofibration.
  Its terminal map descends through the ORIGINAL sphere pairing, with
  exact pole value and a based homotopy from the original commutator.
  `MeridianCommutator.fourLoop` is the resulting explicit native seven-
  cube in S4 for the original Moore meridians. Its class has NOT yet been
  identified with the original attaching class or numerically evaluated.
- `SphereFourAttaching.attachingClass` is the image of the proved integral
  generator of the original `pi_7(S^7)` under the actual S4 second-cell
  attaching map. `suspension_eq_one_iff` proves that its integer powers
  are exactly the kernel of the ORIGINAL suspension to `pi_8(S^5)`.
  `quotientEquiv` identifies the quotient by this cyclic subgroup with
  that native eighth group, and its representative formula is suspension.
- `SphereFiveEighth.presentationEquiv` transports this exact presentation
  to `(Z x Z/12) / <relation>`. The relation is defined by the actual
  attaching class, not supplied as a hypothesis. Its first coordinate
  is the marked original James--Hopf image. The proved null-class test
  is the pair of integer and mod-12 equations for an integer multiple
  of that relation. Neither numerical coordinate has been evaluated.
- `StableThirdAttaching.fromFirst` recursively composes the original
  native suspensions, each proved bijective, from `pi_8(S^5)` to every
  `pi_(k+8)(S^(k+5))`. The same actual relation presents all these stages
  and detects the kernel of every iterated suspension from `pi_7(S^4)`.
  This does not yet identify the third stem with Z/24 and does not compute
  the sixth stem or the Arf detection map.
- `UnitalAttaching.nullhomotopy` contracts the actual second James-cell
  attaching map whenever the original sphere has a continuous unital
  multiplication. It uses the two original characteristic blocks and
  fixes the actual corner. Associativity is not assumed. The induced
  attaching homomorphisms vanish in every positive degree, and the
  original EHP connecting maps vanish in the established metastable range.
- `ThreeAttaching.multiplication` is genuine quaternion multiplication
  in the original three-sphere coordinates, with both pole-unit laws
  proved. Thus its actual attaching map is based-nullhomotopic and the
  three-sphere connecting maps vanish in the required finite range.
- `ThreeRetraction.retraction` evaluates actual James words in the unit
  quaternions. It is continuous and retracts the original sphere inclusion
  literally. Transport through the checked all-degree James comparison
  gives `sectionHom_suspension`, a left inverse of the original suspension
  on every positive native group of S3. This does not extend the EHP range.
- `SphereFourSeventh.groupEquiv` proves the native group
  `pi_7(S^4) = Z x Z/12`. The first coordinate is the original James--Hopf
  map under the checked integer marking of `pi_7(S^7)`. Original suspension
  from `pi_6(S^3)` maps to the second coordinate with its checked Z/12
  marking. The short exact sequence splits using a chosen lift of the
  Hopf generator; no canonical quaternionic Hopf-map identification is
  asserted. The S4 attaching-map value and stable sixth stem remain open.
- `IntegralSplitting` proves the missing marked integral direct-sum
  helper and retains the supplied inclusion as its first summand. Explicit
  imports repair two existing surgery dependencies exposed by the combined
  build. Both callers and their downstream root dependencies now compile.
- `RoundCell.quotientHom_eq_suspension` identifies the original cell
  quotient homomorphism with the original cubical suspension through
  constructed based boundary and target homeomorphisms. The comparison
  uses the genuine round and max-norm disks and a based homotopy of their
  contractions. `quotientHom_bijective` proves the original map bijective
  for positive `n,d` with `d + 3 < 4n`.
- `EHPCell.comparisonHom_bijective` consequently parametrizes every input
  of the original EHP connecting map for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `connecting_comparisonHom` recovers the actual second-cell
  attaching homomorphism. `suspension_eq_one_iff_attaching` proves that
  the native suspension kernel is exactly this attaching-map image on
  the native groups of `S^(2n-1)`. No numerical attaching-map evaluation
  or stable sixth-stem calculation is inferred from this image formula.
- `CellBoundary.connecting_quotientGenLoop` now evaluates the original
  EHP connecting map on explicit second-cell representatives. The actual
  attaching map is lifted using straight contraction of its characteristic
  disk to the all-zero cube corner. The proved quotient-cube formula
  retains the leading path-time coordinate and the two original pairing
  blocks. Applying the connecting map to its suspension recovers exactly
  the original attaching map on the boundary representative. The
  comparison above now identifies its quotient homomorphism with cubical
  suspension through constructed based homeomorphisms. No orientation
  sign or numerical attaching-map calculation is inferred.
- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Compare the constructed meridian commutator with the ORIGINAL S4
   attaching class, and compute its sixth-homology class in the primitive
   second-cell basis. The Hopf/Hurewicz coordinate bridge is checked, but
   the attaching coefficient and torsion parity are not. The exact mod-12
   coordinate depends on the chosen Hopf-generator lift. Further required
   sphere-group calculations and any extra EHP range must also be proved.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 8507 jobs.
- All 12622 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2104 task files and 4319 local root-import files
  (4322 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12510 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `SphereFourAttaching.attachingClass` is the image of the proved integral
  generator of the original `pi_7(S^7)` under the actual S4 second-cell
  attaching map. `suspension_eq_one_iff` proves that its integer powers
  are exactly the kernel of the ORIGINAL suspension to `pi_8(S^5)`.
  `quotientEquiv` identifies the quotient by this cyclic subgroup with
  that native eighth group, and its representative formula is suspension.
- `SphereFiveEighth.presentationEquiv` transports this exact presentation
  to `(Z x Z/12) / <relation>`. The relation is defined by the actual
  attaching class, not supplied as a hypothesis. Its first coordinate
  is the marked original James--Hopf image. The proved null-class test
  is the pair of integer and mod-12 equations for an integer multiple
  of that relation. Neither numerical coordinate has been evaluated.
- `StableThirdAttaching.fromFirst` recursively composes the original
  native suspensions, each proved bijective, from `pi_8(S^5)` to every
  `pi_(k+8)(S^(k+5))`. The same actual relation presents all these stages
  and detects the kernel of every iterated suspension from `pi_7(S^4)`.
  This does not yet identify the third stem with Z/24 and does not compute
  the sixth stem or the Arf detection map.
- `UnitalAttaching.nullhomotopy` contracts the actual second James-cell
  attaching map whenever the original sphere has a continuous unital
  multiplication. It uses the two original characteristic blocks and
  fixes the actual corner. Associativity is not assumed. The induced
  attaching homomorphisms vanish in every positive degree, and the
  original EHP connecting maps vanish in the established metastable range.
- `ThreeAttaching.multiplication` is genuine quaternion multiplication
  in the original three-sphere coordinates, with both pole-unit laws
  proved. Thus its actual attaching map is based-nullhomotopic and the
  three-sphere connecting maps vanish in the required finite range.
- `ThreeRetraction.retraction` evaluates actual James words in the unit
  quaternions. It is continuous and retracts the original sphere inclusion
  literally. Transport through the checked all-degree James comparison
  gives `sectionHom_suspension`, a left inverse of the original suspension
  on every positive native group of S3. This does not extend the EHP range.
- `SphereFourSeventh.groupEquiv` proves the native group
  `pi_7(S^4) = Z x Z/12`. The first coordinate is the original James--Hopf
  map under the checked integer marking of `pi_7(S^7)`. Original suspension
  from `pi_6(S^3)` maps to the second coordinate with its checked Z/12
  marking. The short exact sequence splits using a chosen lift of the
  Hopf generator; no canonical quaternionic Hopf-map identification is
  asserted. The S4 attaching-map value and stable sixth stem remain open.
- `IntegralSplitting` proves the missing marked integral direct-sum
  helper and retains the supplied inclusion as its first summand. Explicit
  imports repair two existing surgery dependencies exposed by the combined
  build. Both callers and their downstream root dependencies now compile.
- `RoundCell.quotientHom_eq_suspension` identifies the original cell
  quotient homomorphism with the original cubical suspension through
  constructed based boundary and target homeomorphisms. The comparison
  uses the genuine round and max-norm disks and a based homotopy of their
  contractions. `quotientHom_bijective` proves the original map bijective
  for positive `n,d` with `d + 3 < 4n`.
- `EHPCell.comparisonHom_bijective` consequently parametrizes every input
  of the original EHP connecting map for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `connecting_comparisonHom` recovers the actual second-cell
  attaching homomorphism. `suspension_eq_one_iff_attaching` proves that
  the native suspension kernel is exactly this attaching-map image on
  the native groups of `S^(2n-1)`. No numerical attaching-map evaluation
  or stable sixth-stem calculation is inferred from this image formula.
- `CellBoundary.connecting_quotientGenLoop` now evaluates the original
  EHP connecting map on explicit second-cell representatives. The actual
  attaching map is lifted using straight contraction of its characteristic
  disk to the all-zero cube corner. The proved quotient-cube formula
  retains the leading path-time coordinate and the two original pairing
  blocks. Applying the connecting map to its suspension recovers exactly
  the original attaching map on the boundary representative. The
  comparison above now identifies its quotient homomorphism with cubical
  suspension through constructed based homeomorphisms. No orientation
  sign or numerical attaching-map calculation is inferred.
- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Determine the necessary invariants of the actual S4 attaching
   relation, then compute the further groups and map values needed for
   the stable sixth stem. The integer coordinate and the torsion parity
   are the next targets; the exact torsion coordinate depends on the
   chosen Hopf-generator lift. The actual one-relation presentation is
   checked, but its numerical evaluation and the required geometric
   identities are not. Any additional EHP range must also be proved.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 8495 jobs.
- All 12510 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2093 task files and 4307 local root-import files
  (4310 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12473 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `UnitalAttaching.nullhomotopy` contracts the actual second James-cell
  attaching map whenever the original sphere has a continuous unital
  multiplication. It uses the two original characteristic blocks and
  fixes the actual corner. Associativity is not assumed. The induced
  attaching homomorphisms vanish in every positive degree, and the
  original EHP connecting maps vanish in the established metastable range.
- `ThreeAttaching.multiplication` is genuine quaternion multiplication
  in the original three-sphere coordinates, with both pole-unit laws
  proved. Thus its actual attaching map is based-nullhomotopic and the
  three-sphere connecting maps vanish in the required finite range.
- `ThreeRetraction.retraction` evaluates actual James words in the unit
  quaternions. It is continuous and retracts the original sphere inclusion
  literally. Transport through the checked all-degree James comparison
  gives `sectionHom_suspension`, a left inverse of the original suspension
  on every positive native group of S3. This does not extend the EHP range.
- `SphereFourSeventh.groupEquiv` proves the native group
  `pi_7(S^4) = Z x Z/12`. The first coordinate is the original James--Hopf
  map under the checked integer marking of `pi_7(S^7)`. Original suspension
  from `pi_6(S^3)` maps to the second coordinate with its checked Z/12
  marking. The short exact sequence splits using a chosen lift of the
  Hopf generator; no canonical quaternionic Hopf-map identification is
  asserted. The S4 attaching-map value and stable sixth stem remain open.
- `IntegralSplitting` proves the missing marked integral direct-sum
  helper and retains the supplied inclusion as its first summand. Explicit
  imports repair two existing surgery dependencies exposed by the combined
  build. Both callers and their downstream root dependencies now compile.
- `RoundCell.quotientHom_eq_suspension` identifies the original cell
  quotient homomorphism with the original cubical suspension through
  constructed based boundary and target homeomorphisms. The comparison
  uses the genuine round and max-norm disks and a based homotopy of their
  contractions. `quotientHom_bijective` proves the original map bijective
  for positive `n,d` with `d + 3 < 4n`.
- `EHPCell.comparisonHom_bijective` consequently parametrizes every input
  of the original EHP connecting map for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `connecting_comparisonHom` recovers the actual second-cell
  attaching homomorphism. `suspension_eq_one_iff_attaching` proves that
  the native suspension kernel is exactly this attaching-map image on
  the native groups of `S^(2n-1)`. No numerical attaching-map evaluation
  or stable sixth-stem calculation is inferred from this image formula.
- `CellBoundary.connecting_quotientGenLoop` now evaluates the original
  EHP connecting map on explicit second-cell representatives. The actual
  attaching map is lifted using straight contraction of its characteristic
  disk to the all-zero cube corner. The proved quotient-cube formula
  retains the leading path-time coordinate and the two original pairing
  blocks. Applying the connecting map to its suspension recovers exactly
  the original attaching map on the boundary representative. The
  comparison above now identifies its quotient homomorphism with cubical
  suspension through constructed based homeomorphisms. No orientation
  sign or numerical attaching-map calculation is inferred.
- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Compute the remaining actual cell-attaching homomorphisms and
   sphere groups needed for the stable sixth stem. The S3 attaching map
   is now contracted and `pi_7(S^4) = Z x Z/12` is checked with its original
   suspension and Hopf maps. The S4 attaching-map value, the subsequent
   numerical groups, and the required Whitehead-product calculations
   remain. Any additional EHP range must be proved separately.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 8492 jobs.
- All 12473 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2090 task files and 4304 local root-import files
  (4307 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12414 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `RoundCell.quotientHom_eq_suspension` identifies the original cell
  quotient homomorphism with the original cubical suspension through
  constructed based boundary and target homeomorphisms. The comparison
  uses the genuine round and max-norm disks and a based homotopy of their
  contractions. `quotientHom_bijective` proves the original map bijective
  for positive `n,d` with `d + 3 < 4n`.
- `EHPCell.comparisonHom_bijective` consequently parametrizes every input
  of the original EHP connecting map for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `connecting_comparisonHom` recovers the actual second-cell
  attaching homomorphism. `suspension_eq_one_iff_attaching` proves that
  the native suspension kernel is exactly this attaching-map image on
  the native groups of `S^(2n-1)`. No numerical attaching-map evaluation
  or stable sixth-stem calculation is inferred from this image formula.
- `CellBoundary.connecting_quotientGenLoop` now evaluates the original
  EHP connecting map on explicit second-cell representatives. The actual
  attaching map is lifted using straight contraction of its characteristic
  disk to the all-zero cube corner. The proved quotient-cube formula
  retains the leading path-time coordinate and the two original pairing
  blocks. Applying the connecting map to its suspension recovers exactly
  the original attaching map on the boundary representative. The
  comparison above now identifies its quotient homomorphism with cubical
  suspension through constructed based homeomorphisms. No orientation
  sign or numerical attaching-map calculation is inferred.
- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Compute the actual cell-attaching homomorphisms on the sphere
   classes needed for the stable sixth stem, including the required
   Whitehead-product calculations if used. The quotient-to-suspension
   comparison and EHP kernel formula are checked, but the numerical
   groups and map values are not. Any additional range needed by that
   computation must be proved separately.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7802 jobs.
- All 12414 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2084 task files and 3658 local root-import files
  (3661 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12296 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `CellBoundary.connecting_quotientGenLoop` now evaluates the original
  EHP connecting map on explicit second-cell representatives. The actual
  attaching map is lifted using straight contraction of its characteristic
  disk to the all-zero cube corner. The proved quotient-cube formula
  retains the leading path-time coordinate and the two original pairing
  blocks. Applying the connecting map to its suspension recovers exactly
  the original attaching map on the boundary representative. This does
  not yet identify that quotient class with a standard sphere generator.
- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Identify the explicit second-cell quotient classes with the
   standard sphere classes and compute the connecting map on the
   generators needed for the stable sixth stem. Prove the required
   Whitehead-product identification if used. The checked cell formula
   and metastable exactness do not yet calculate these groups.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7787 jobs.
- All 12296 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2071 task files and 3643 local root-import files
  (3646 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12254 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `FiberQuotient.hom_bijective_range` now proves the original full James
  fiber-to-quotient map bijective for `n >= 2`, positive `d`, and
  `d + 3 <= 3n`. `JamesSphereEHPMetastable` discharges that comparison
  input in all three consecutive EHP exactness statements. The original
  native suspension, coordinate-corrected James--Hopf map, and transported
  fiber projection are retained. No Whitehead-product formula or stable
  sixth-stem computation is claimed by this exactness result.
- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- The earlier `FiberQuotient.hom_bijective_first_range` and
  `EHPFirstRange` remain checked through positive degree `2n - 1`.
  The full required metastable range now follows from the geometric
  finite comparison and the finite-to-full map identities below.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  This supplies the finite-to-full quotient factor used below.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  The following factorization now identifies this finite result with
  the quotient-path comparison and transfers it to the full James space.
- `collapse_map_bijective` proves that the actual cone collapse induces
  native bijections at every point of the cone image. A linear disk
  contraction to that chosen point is extended while fixing it; both
  inverse homotopies retain the original basepoints. Contractibility of
  the cone image and the genuine fiber sequence prove bijectivity of
  the cone-side quotient-loop factor in every positive degree.
- `FiniteFiberQuotient.hom_bijective` is the finite quotient comparison
  for the original one-letter sphere, not a substitute source. The
  lower-subspace homeomorphism changes only the fiber source coordinate
  and leaves its actual path unchanged.
- `SecondStageHomologyRange.fullMap_bijective` proves the original
  second-stage inclusion a homology isomorphism for `2 <= k < 3n`.
  Actual cell pushouts and compact factorization prove the range; at
  the upper edge, the source homology vanishes above the `2n`-cell.
  `SecondStage.wordInclusion_pi_bijective` gives native isomorphisms
  through positive degree `3n - 2`, at every second-stage point.
- `HomotopyFiberTargetMap` proves literal naturality of path
  postcomposition with projection and the fiber boundary. The checked
  group diagram argument gives `FiniteFiberQuotient.toFullHom_bijective`
  through positive degree `3n - 3`. The original finite-to-full quotient
  map is separately proved bijective through positive degree `3n - 2`.
- `FiniteFiberQuotient.hom_toFull` proves the commuting square on the
  original cube representatives. Canceling the proved finite-to-full
  factor gives `FiberQuotient.hom_bijective_range` itself and the full
  required EHP exactness stated above, without an excision hypothesis.

#### Remaining proof obligations

1. Compute the connecting map in the dimensions needed for the stable
   sixth stem, including a Whitehead-product identification if used.
   Metastable EHP exactness is now checked, but exactness alone does not
   determine those maps or calculate the groups.
2. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
3. Finish unconditional framed filling and smooth classification,
   supplying a term of `SixSphereRigidity`. The neighboring
   `smale_theorem_a` concludes a homeomorphism, not the required
   diffeomorphism. The main theorem remains unproved.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7783 jobs.
- All 12254 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2067 task files and 3639 local root-import files
  (3642 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12185 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- `FiberQuotient.hom_bijective_first_range` now proves the genuine native
  fiber-to-quotient comparison bijective in every positive degree
  `d <= 2n - 1`. `EHPFirstRange` discharges the comparison input for all
  three consecutive EHP exactness statements in precisely this range.
  For `n = 2` it is the full range `d <= 3n - 3`; for larger `n` the
  higher metastable degrees remain unproved. No Whitehead-product
  formula for the connecting map has been proved here.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  Their larger range does not by itself extend the fiber comparison.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  The punctured-cell retractions and finite-pair fiber comparison
  assembled from this geometry are now checked below.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. The moving-bottom correction is now checked.
- `SupportedCorrection.exists_correction` constructs a supported
  deformation that fixes original cone points, preserves the original
  James-stage image, and preserves avoidance of the second puncture.
  Its initial-time track retains the original starting map. Applying
  the second puncture deformation then ends in the actual James stage.
- `SecondStageCone.exists_cubical_compression` combines these steps for
  `n >= 2` and `d <= 3n - 2`. The bottom stays in the cone and ends in
  the original lower subspace. Top and protected parameter faces stay
  in the James stage, with their common-subspace points fixed.
- `SecondStageCone.FiberComparison.map` is the literal map of actual
  homotopy fibers induced by the pair inclusion
  `(J_2(S^n), S^n) -> (P, cone disk)`, expressed using the embedded lower
  subspace. `map_surjective` proves native surjectivity through degree
  `3n - 2`; `map_injective` and `map_bijective` prove native bijectivity
  through `3n - 3`, for `n >= 2` and every chosen lower-subspace point.
  Cylinder reflection lifts the moving endpoint tracks through the
  original embedding, retaining the exact original representatives.
  This finite-pair theorem is not yet the full `FiberQuotient.hom`
  comparison, and no additional full-James EHP degrees are claimed.

#### Remaining proof obligations

1. Extend the actual `FiberQuotient.hom` from `d <= 2n - 1` through
   `d <= 3n - 3`. The remaining homology route requires the original
   `toLoops` maps in degrees `2n` through `3n - 2`. The comparison
   spaces can have nonzero lower homotopy there, so the new first-degree
   theorem alone does not establish this extension. Boundary-fixing
   punctured-cell retractions and attachment descent are now checked.
   The actual cone model, moving-bottom correction, and finite-pair
   native fiber bijectivity are now checked. What remains is to identify
   this finite-pair map with the original quotient-path comparison and
   pass to the full James space in the required range, proving the
   needed map identities and naturality throughout.
2. Discharge the higher-range input in `EHPAssembly`. The restricted
   unconditional EHP result is checked; full metastable exactness and
   any connecting-map/Whitehead-product formula needed for computation
   remain separate obligations.
3. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
4. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7768 jobs.
- All 12185 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2052 task files and 3624 local root-import files
  (3627 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12134 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- `FiberQuotient.hom_bijective_first_range` now proves the genuine native
  fiber-to-quotient comparison bijective in every positive degree
  `d <= 2n - 1`. `EHPFirstRange` discharges the comparison input for all
  three consecutive EHP exactness statements in precisely this range.
  For `n = 2` it is the full range `d <= 3n - 3`; for larger `n` the
  higher metastable degrees remain unproved. No Whitehead-product
  formula for the connecting map has been proved here.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  Their larger range does not by itself extend the fiber comparison.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  This is not yet homotopy excision. The punctured-cell retractions are
  now checked below; the original relative homotopy comparison is not.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This alone does not extend EHP.
- `CompactCellAttachment` constructs a concrete compact Hausdorff disk
  attachment without assuming that the boundary map is surjective.
  `SecondStageCone.Space n` is the actual second James stage with an
  `(n+1)`-disk attached along its one-letter sphere. Its `2n`-cell and
  disk interior have proved disjoint open Euclidean charts.
- `SecondStageCone.collapse_homotopyEquivalence` proves a homotopy
  equivalence whose forward map is the actual cone collapse. Its
  restriction to the original James stage is exactly the original
  quotient map. The collapse fibers and homotopy-extension inputs are
  proved; no equivalence hypothesis remains here.
- `first_isPushout` presents the same cone space in the opposite
  attachment order. Thus puncturing either cell gives a checked strong
  deformation retraction onto the other original closed piece, fixing
  that piece pointwise. The complements of the open cells are identified
  with the actual embedded James stage and cone disk.
- `SecondStageCone.exists_point_excision` applies the constructed
  geometry to arbitrary continuous cylinders in this actual model for
  `n >= 2` and parameter dimension `d <= 3n - 2`. Its preliminary
  homotopy preserves both original closed pieces and fixes their
  intersection. The graph homotopy has the stated top/side and point-
  avoidance controls. This is not yet the relative homotopy comparison:
  its moving bottom face still needs correction within the cone disk.

#### Remaining proof obligations

1. Extend the actual `FiberQuotient.hom` from `d <= 2n - 1` through
   `d <= 3n - 3`. The remaining homology route requires the original
   `toLoops` maps in degrees `2n` through `3n - 2`. The comparison
   spaces can have nonzero lower homotopy there, so the new first-degree
   theorem alone does not establish this extension. Boundary-fixing
   punctured-cell retractions and attachment descent are now checked.
   The actual two-cell cone model and its collapse equivalence are now
   checked. What remains is the moving-bottom correction, the comparison
   on original relative/fiber homotopy classes, and the finite-to-full
   James passage in the required range.
2. Discharge the higher-range input in `EHPAssembly`. The restricted
   unconditional EHP result is checked; full metastable exactness and
   any connecting-map/Whitehead-product formula needed for computation
   remain separate obligations.
3. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
4. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7758 jobs.
- All 12134 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2042 task files and 3614 local root-import files
  (3617 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 12055 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- `FiberQuotient.hom_bijective_first_range` now proves the genuine native
  fiber-to-quotient comparison bijective in every positive degree
  `d <= 2n - 1`. `EHPFirstRange` discharges the comparison input for all
  three consecutive EHP exactness statements in precisely this range.
  For `n = 2` it is the full range `d <= 3n - 3`; for larger `n` the
  higher metastable degrees remain unproved. No Whitehead-product
  formula for the connecting map has been proved here.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  Their larger range does not by itself extend the fiber comparison.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  This is not yet homotopy excision. The punctured-cell retractions are
  now checked below; the original relative homotopy comparison is not.
- `PuncturedConvexCell.deformationRel` gives a boundary-fixed radial
  deformation for a closed bounded convex neighborhood punctured at the
  origin. Its actual Minkowski gauge supplies the retraction. Translation
  gives `PuncturedDiskRetraction.deformationRel` for a characteristic
  disk punctured at any interior point, not just its center.
- `OpenPushoutRestriction.isPushout` proves that an open subset containing
  the whole base retains the original attachment pushout, with the cell
  leg restricted to its actual preimage. `PuncturedCellAttachment` uses
  this to descend the punctured-disk retraction, fixing the entire base.
  `CellAttachmentChart.chart` is the actual open-cell coordinate chart.
- `JamesSphere.PuncturedStage.deformationRel` applies these constructions
  to the original finite James stages: deleting any point of the open
  top cell gives a strong deformation retraction onto the preceding
  stage, fixing it pointwise. `inclusion_val` retains the literal word
  inclusion, and `openCell_eq_topStratum` identifies the coordinate chart
  with the actual top word stratum. This does not yet prove the two-cell
  cone/relative comparison or any additional EHP degrees.

#### Remaining proof obligations

1. Extend the actual `FiberQuotient.hom` from `d <= 2n - 1` through
   `d <= 3n - 3`. The remaining homology route requires the original
   `toLoops` maps in degrees `2n` through `3n - 2`. The comparison
   spaces can have nonzero lower homotopy there, so the new first-degree
   theorem alone does not establish this extension. Boundary-fixing
   punctured-cell retractions and attachment descent are now checked.
   The geometric excision route still needs the actual two-cell cone
   model and its original relative/fiber map comparison before it can
   extend the James-space result.
2. Discharge the higher-range input in `EHPAssembly`. The restricted
   unconditional EHP result is checked; full metastable exactness and
   any connecting-map/Whitehead-product formula needed for computation
   remain separate obligations.
3. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
4. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7753 jobs.
- All 12055 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2037 task files and 3609 local root-import files
  (3612 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 11957 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- `FiberQuotient.hom_bijective_first_range` now proves the genuine native
  fiber-to-quotient comparison bijective in every positive degree
  `d <= 2n - 1`. `EHPFirstRange` discharges the comparison input for all
  three consecutive EHP exactness statements in precisely this range.
  For `n = 2` it is the full range `d <= 3n - 3`; for larger `n` the
  higher metastable degrees remain unproved. No Whitehead-product
  formula for the connecting map has been proved here.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  Their larger range does not by itself extend the fiber comparison.

- `TwoCellExcision.exists_excision` now constructs the geometric
  two-cell point-avoidance step for an arbitrary continuous cubical
  cylinder map. The hypotheses are two disjoint open Euclidean cells,
  their dimensions `a,b`, a parameter cube of dimension `d` with
  `d + 2 < a + b`, and the stated side/top/bottom avoidance conditions.
  Smooth coordinate descriptions are constructed by supported target-cell
  homotopies and actual smooth approximation. A joint-image dimension
  bound chooses cell points with disjoint projected fibers; a continuous
  graph deformation removes one point while the moving bottom avoids
  the other. The preliminary homotopy preserves both cell memberships.
  This is not yet homotopy excision: punctured-cell retractions and the
  application to the original relative homotopy maps are still missing.

#### Remaining proof obligations

1. Extend the actual `FiberQuotient.hom` from `d <= 2n - 1` through
   `d <= 3n - 3`. The remaining homology route requires the original
   `toLoops` maps in degrees `2n` through `3n - 2`. The comparison
   spaces can have nonzero lower homotopy there, so the new first-degree
   theorem alone does not establish this extension. The new geometric
   excision route still needs boundary-fixing punctured-cell retractions,
   the actual two-cell attachment model, and its relative/fiber map
   comparison before it can extend the James-space result.
2. Discharge the higher-range input in `EHPAssembly`. The restricted
   unconditional EHP result is checked; full metastable exactness and
   any connecting-map/Whitehead-product formula needed for computation
   remain separate obligations.
3. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
4. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7747 jobs.
- All 11957 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2031 task files and 3603 local root-import files
  (3606 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 11887 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `CollapsedSubspace.relativeHomology_bijective` proves that the original
  cofibration quotient `(X,A) -> (X/A,*)` induces integral relative-homology
  isomorphisms in every degree. Its proof retains the genuine collapse,
  upper-cylinder retraction, excision map, and exact commuting square.
- `FullFirstStageCofibration.hasHomotopyExtension` extends the original
  first-stage homotopy coherently over every finite James stage. The
  final word topology and continuous path evaluation give an actual
  homotopy on the full James space. Thus
  `quotient_relative_homology_bijective` applies to the original full
  James quotient in every degree, with no remaining cofibration input.
- `FirstStage.homeomorph` has the actual one-letter map as its forward
  function. The original first-stage inclusion induces homology
  isomorphisms for `2 <= d < 2n`, including the upper-edge injection.
  `FirstStage.fiber_pi` proves vanishing through `2n - 2` at every point
  of every fiber over the first stage. The quotient singleton fibers
  have the same proved connectivity, with every basepoint retained.
- `toLoops_homology_bijective_first_range` proves that the original
  fiber-to-quotient path-composition map is an integral homology
  isomorphism for `2 <= d <= 2n - 1`, for `n >= 2`. The source and
  target fiber homeomorphisms and literal map factorization are checked.
  This includes the first potentially nonzero homology degree.
- `NativeFirstDegreeHomologyComparison.map_bijective` proves a general
  first-degree comparison: for simply connected spaces with vanishing
  lower native groups, a homology isomorphism in degree `d >= 2` gives
  bijectivity of the original native map in degree `d`. Induction uses
  actual loop-map homology and native-currying naturality, starting with
  second Hurewicz. No extra homology degree is required in this theorem.
- `FiberQuotient.hom_bijective_first_range` now proves the genuine native
  fiber-to-quotient comparison bijective in every positive degree
  `d <= 2n - 1`. `EHPFirstRange` discharges the comparison input for all
  three consecutive EHP exactness statements in precisely this range.
  For `n = 2` it is the full range `d <= 3n - 3`; for larger `n` the
  higher metastable degrees remain unproved. No Whitehead-product
  formula for the connecting map has been proved here.
- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  Their larger range does not by itself extend the fiber comparison.

#### Remaining proof obligations

1. Extend the actual `FiberQuotient.hom` from `d <= 2n - 1` through
   `d <= 3n - 3`. The remaining homology route requires the original
   `toLoops` maps in degrees `2n` through `3n - 2`. The comparison
   spaces can have nonzero lower homotopy there, so the new first-degree
   theorem alone does not establish this extension.
2. Discharge the higher-range input in `EHPAssembly`. The restricted
   unconditional EHP result is checked; full metastable exactness and
   any connecting-map/Whitehead-product formula needed for computation
   remain separate obligations.
3. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
4. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7736 jobs.
- All 11887 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2020 task files and 3592 local root-import files
  (3595 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 11796 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- The original bottom-sphere native map and quotient Hopf factor remain
  proved isomorphisms through positive degree `3n - 2`, for `n >= 2`.
  The separate actual fiber-to-quotient metastable comparison is unproved.
- `InclusionRange` identifies the genuine one-letter native map with
  cubical suspension through the checked coordinate-corrected James
  comparison. The original inclusion is injective through `2n - 2`
  and surjective through `2n - 1`, including its literal image basepoint.
- `FiberQuotient.fiber_pi` proves native vanishing through `2n - 2`
  at every point of the actual one-letter inclusion fiber. This is not
  the different James-comparison fiber. `FirstStageQuotient.pi_below_bottom`
  proves quotient vanishing below `2n`; its genuine loop space has native
  vanishing through `2n - 2`. Both comparison spaces are simply connected.
- `hom_bijective_below_bottom` proves the actual fiber-to-quotient map
  bijective through `2n - 2`, where both groups vanish. The required
  larger range through `3n - 3` is not obtained from this fact.
  `hom_bijective_of_homology` reduces that missing range to the original
  continuous `toLoops` homology maps in degrees `2` through `3n - 2`.
- `FiberQuotient.boundaryHom` transports the genuine fiber boundary
  along the proved pole-image/unit-word equality. Its quotient formula
  and the three native exactness statements are checked. `EHPAssembly`
  proves all three consecutive EHP kernel/image statements with one
  explicit remaining input: bijectivity of the actual `FiberQuotient.hom`
  in the indicated degree. EHP therefore remains conditional.
- `SingularHomotopyPrismNaturality` proves the commuting square for
  Mathlib's actual signed singular-chain prism. `transgression_natural`
  descends this identity to the original fiber-to-relative-homology map.
  No replacement prism or independently chosen group map is used.
- `recoveryLift_eq_transgression` identifies the constructed ending-path
  recovery with that original transgression. The checked recovery is
  therefore a left inverse, proving original transgression injectivity
  whenever the specified normalization data have been constructed.
- `fiber_homology_bijective_of_connectivity` constructs all normalization
  inputs from bounded native fiber connectivity. An isomorphism of the
  actual relative-homology map then gives an isomorphism of the actual
  fiber-homology map in that degree. Its lower-connectivity conditions
  must still be verified in applications; it is not full homotopy excision.

#### Remaining proof obligations

1. Prove the actual `FiberQuotient.hom` bijective through native fiber
   degree `3n - 3`. The comparison map, source/target connectivity, and
   below-bottom range are checked. The first potentially nonzero degree
   and the remaining metastable degrees still need the excision argument.
   The new homology comparison provides tools, not this missing result.
2. Discharge the explicit comparison input in `EHPAssembly` to obtain
   unconditional EHP exactness. The native basepoint transport and
   kernel/image assembly no longer remain separate unproved algebra.
3. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
4. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7719 jobs.
- All 11796 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 2003 task files and 3575 local root-import files
  (3578 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 11737 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- The original all-degree James comparison, suspension coordinate
  correction, full-quotient Hopf factorization, and actual fiber-to-quotient
  map with its boundary identity remain checked. The last map's
  metastable bijectivity is still unproved.
- `MayerVietorisInclusionRange` and `DoubleMappingCylinderHomologyRange`
  prove homology injection and surjection for the actual pushout inclusion.
  `NormedDiskHomology` supplies the genuine max-norm disk and boundary
  homology and the boundary's homotopy-extension property.
- `FirstStageQuotient.CellAttachment.isPushout` identifies each later
  finite quotient with its actual cell-attachment pushout. The cells after
  the bottom sphere have dimensions `(k + 3) * n`. The original finite
  transition maps, characteristic maps, attaching boundary, and maps into
  the full quotient are retained, not replaced by abstract group maps.
- `FirstStageQuotient.HomologyStages` lifts every full-quotient homology
  class to an actual finite stage and detects zero at a later stage.
  The checked transition-map homology bounds therefore pass to the
  original full-quotient inclusion of the second stage.
- `bottomSphere_homology_bijective_range` proves that the original map
  `S^(2n) -> J(S^n)/S^n` induces integral homology isomorphisms for
  `n >= 2` and `2 <= d < 3n`. This discharges the former homology input,
  including the actual generator map and the upper-edge injection.
- `bottomSphere_pi_bijective_range` now proves native homotopy
  isomorphisms for that original map in every positive degree
  `d <= 3n - 2`, with its actual pole and quotient basepoint.
  `bottomSpherePiEquiv` has that induced map as its forward function.
- `CubicalSphereSuspension.hom_bijective` proves the original native
  cubical suspension is bijective when `m + 3 < 2 * (n + 1)`.
  `sphereHopfHom_bijective_range` combines it with the bottom-sphere
  result and the checked map identity: the actual quotient Hopf factor
  is an isomorphism for positive `d <= 3n - 2`. This is not a claim that
  the full Hopf map is an isomorphism, or that EHP exactness is proved.

#### Remaining proof obligations

1. Prove metastable bijectivity of the actual `FiberQuotient.hom`: its
   native fiber degree is one less than its quotient degree. The map and
   boundary identity are checked, but homotopy excision is not.
2. Combine that comparison with the genuine fiber exact sequence and
   the now-proved quotient Hopf-factor isomorphism to prove EHP exactness,
   including the reverse kernel/image inclusion and actual basepoint
   transport. A zero composite does not supply this conclusion.
3. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
4. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact next maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7707 jobs.
- All 11737 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 1991 task files and 3563 local root-import files
  (3566 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 11669 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- The all-degree original James comparison, explicit suspension coordinate
  correction, actual second-stage sphere quotient, and native full-quotient
  Hopf factorization remain checked. These map identities are not EHP exactness.
- `FiberQuotientComparison.hom` is the original fiber-to-quotient comparison:
  compose each actual fiber path with the quotient, then use native currying.
  `hom_boundary` proves that its composite with the genuine fiber boundary
  map is the original quotient-induced map, on actual cube representatives.
  `JamesSphere.FiberQuotient` instantiates this for the one-letter inclusion,
  retaining the actual pole, fiber basepoint, and full quotient basepoint.
- `CollapsedSubspaceSeparation` proves that collapsing a compact subset
  of a Hausdorff space is proper and has a Hausdorff quotient. It does not
  require the whole source to be compact. This applies to the actual
  full James quotient, and its finite second stage and bottom sphere are
  now proved closed embedded subspaces.
- `FirstStageCofibration.hasHomotopyExtension` proves the actual first-to-
  finite-stage inclusion has homotopy extension. `CollapsedSubspacePushout`
  proves the literal collapse pushout. The genuine double-cylinder
  comparison and van Kampen give simple connectivity of every finite-stage
  quotient in sphere dimension at least two.
- `FirstStageQuotient.exists_continuous_stage_factorization` factors any
  compact-domain continuous map through an actual finite-stage quotient.
  Properness and the original James compact-factorization theorem supply
  the finite bound, and the range homeomorphism supplies the continuous map.
  `FirstStageQuotient.simplyConnectedSpace` then contracts every original
  loop in the full quotient through such a finite stage.
- `HomologyRangeConnectivity.map_pi_bijective` proves the finite-range
  comparison for actual maps of simply connected spaces: integral homology
  isomorphisms in degrees `2` through `D + 1` imply native homotopy
  isomorphisms in positive degrees through `D`. Strong induction uses the
  checked relative recovery and all-degree vanishing-form Hurewicz; actual
  mapping-cylinder transport returns the original induced map.
- `bottomSphere_pi_bijective_of_homology` applies this to the original
  bottom-sphere map, with both simple-connectivity assumptions discharged
  and the actual pole/basepoint identity retained. Its homology hypothesis
  is explicit and remains unproved in the required metastable range.

#### Remaining proof obligations

1. Prove that the actual bottom-sphere map induces integral homology
   isomorphisms through degree `3n - 1`. The checked finite-range theorem
   would then give native homotopy isomorphisms through `3n - 2`.
2. Prove metastable bijectivity of the actual `FiberQuotient.hom`: its
   native fiber degree is one less than its quotient degree. The map and
   boundary identity are checked, but homotopy excision is not.
3. Combine these comparisons with the actual fiber sequence, target
   suspension isomorphism, and checked Hopf factorization to prove EHP
   exactness, including the reverse kernel/image inclusion.
4. Prove the stable sixth-stem/Arf calculation and apply it to the actual
   candidate collapse class. Geometric Arf zero is proved, but stable
   triviality and the nullhomotopy needed for framed filling are not.
5. Finish unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` concludes a
   homeomorphism, not the required diffeomorphism.

See `JamesHomotopyComparisonPlan.md` for the exact next maps and bounds.
Historical records below retain earlier progress and then-missing steps;
they are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7695 jobs.
- All 11669 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 1979 task files and 3551 local root-import files
  (3554 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 11618 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

#### Latest checked results

- `NativeHomotopyBasepointVanishing.subsingleton` transports native
  positive-degree vanishing from one point to every point of a
  path-connected space. It uses actual sphere-basepoint adjustment and
  the checked disk nullhomotopy criterion. `loops_subsingleton` combines
  this with native currying, retaining every loop-space basepoint.
- `PointInclusionFiber.loopsHomeomorph` identifies the actual fiber of a
  singleton inclusion with the original compact-open based loop space.
  It sends the actual fiber basepoint to the native constant loop.
- `NativeHurewiczVanishing.subsingleton` proves vanishing-form Hurewicz
  detection in every degree at least two. For a simply connected space,
  lower native homotopy vanishing and zero homology in degree `d` imply
  native homotopy vanishing in degree `d`. Induction applies the checked
  relative-homology recovery to the actual point-inclusion pair and then
  uses the native loop dimension shift. No higher Hurewicz assertion is
  an assumption.
- `JamesSphere.FiberConnectivity.fiber_pi` annihilates every positive
  native homotopy group of the original source-inclusion fiber, at every
  point. Its homology vanishes in every degree at least two. The actual
  source-image inclusion induces bijections in every positive degree.
- `DeformationRetractionNativeHomotopy` proves that every actual fiber
  of a strong deformation retraction is contractible. The genuine fiber
  sequence gives native retraction-map bijectivity at every basepoint.
  `MappingCylinderNativeHomotopy.original_pi_bijective` transports the
  inclusion result through the actual source homeomorphism and cylinder
  projection; their composition is checked on original native cubes.
- `JamesSphere.HomotopyComparison.comparison_pi_bijective` proves that
  **the original James comparison induces bijections in every native
  degree**, for sphere dimension at least two and every source basepoint.
  Positive-degree `comparisonPiEquiv` is an actual group isomorphism with
  that original map as its forward function. The original comparison
  fiber has vanishing positive native homotopy groups at every point.
  No homotopy equivalence of spaces is inferred from these group results.
- `JamesSphere.NativeHopf.spherePiEquiv` uses the actual unit-word
  basepoint and native currying. `hopfHom` transports the constructed
  second James--Hopf map to the original sphere homotopy groups, with
  its comparison formula proved. `hopfHom_letterHom` proves that it
  kills the actual one-letter homomorphism. This is not EHP exactness.

- `JamesSphere.SuspensionCoordinates.reorder` retains the actual difference
  between appending the James loop coordinate and placing the cubical
  suspension coordinate first. `coordinateEquiv_letterHom` proves that
  the coordinate-corrected one-letter homomorphism is exactly the existing
  cubical suspension. No homotopy of this reordering to the identity is
  asserted. `orderedHopfHom_suspension` proves the resulting zero composite.
- `JamesSphere.SecondStage.collapse` descends the original sphere pairing
  through the genuine second-stage word presentation. Its pole fiber is
  exactly the first stage; every other fiber is a singleton.
  `quotientHomeomorph` identifies the actual quotient by the independently
  specified collapse relation with the sphere of dimension `n + n`.
  Its composite with the quotient map is exactly this collapse, and the
  original James--Hopf map factors through it and the target inclusion.
- `SecondStage.orderedHopfHom_comparisonHom` checks the native map formula:
  on actual second-stage classes, the coordinate-corrected James--Hopf
  map is the cubical suspension of the quotient-collapse class. This
  retains the original maps and basepoints. It does not establish that
  all classes in the required range have second-stage representatives.

- `FirstStageQuotient.Space` is now the genuine full James quotient by
  its first stage, with the quotient topology; no compactification of the
  noncompact complement is substituted. The original Hopf map descends
  to `hopfMap`. `bottomSphere` embeds the actual second-stage sphere in
  this quotient and maps its pole to the actual quotient basepoint.
- `FirstStageQuotient.sphereHopfHom_quotientMap` factors the original
  coordinate-corrected native Hopf homomorphism through this full quotient.
  `sphereHopfHom_bottomSphere` proves that the factor on the embedded
  sphere is exactly the existing cubical suspension. The native maps,
  original basepoints, and coordinate reorderings are all explicit.
  The embedding is not yet proved to induce isomorphisms in the required
  metastable range, and the relative-to-quotient comparison is unproved.

#### Remaining proof obligations

1. Prove the two metastable comparisons: from the actual James pair
   to its full quotient, and from the embedded bottom sphere to that
   quotient, in degrees `i ≤ 3n - 2`. The quotient spaces, their maps,
   and native Hopf/suspension identities are checked. The required range
   isomorphisms and the reverse inclusion in EHP exactness are unproved.
2. Prove the stable sixth-stem/Arf computation and apply it to the actual
   candidate collapse class. Its geometric Arf value is already zero,
   but the required stable class is not yet proved trivial. The original
   smooth-atlas framed filling still requires that nullhomotopy.
3. Finish the unconditional smooth classification and supply a term of
   `SixSphereRigidity`. The neighboring `smale_theorem_a` declaration has
   a homeomorphism conclusion, not the required diffeomorphism conclusion;
   topological recognition cannot discharge this obligation.

See `JamesHomotopyComparisonPlan.md` for the next homotopy argument.
Earlier geometric, framing, collapse, and surgery results are retained
below as historical checkpoint records; their former missing-step notes
are not current status.

#### Verification

- `lake build Wikipedia.NoExoticSixSphere Wikipedia.NoExoticSixSphere.Audit`
  completed successfully: 7684 jobs.
- All 11618 dependency reports contain only `propext`, `Classical.choice`,
  and `Quot.sound`, or no axioms.
- The source scan covers 1968 task files and 3540 local root-import files
  (3543 distinct scanned paths including configuration). No proof
  placeholders, added axioms, unsafe declarations, native evaluation
  shortcuts, or computational-limit changes were found.
- Lake options are unchanged from HEAD. The existing
  `maxSynthPendingDepth = 3` setting was not increased.
- These checks verify the stated prerequisites, **not the main theorem**.



### Checkpoint 11506 — archived status snapshot

The following is historical, including its then-missing steps.

The unconditional theorem `SixSphereRigidity` remains unproved.

Latest checked reductions:

- `EndingPath.loopContraction` contracts the actual compact-open loop
  space of ending paths by pointwise shortening. The actual auxiliary
  fiber equivalence identifies its projection with the product projection,
  so `EndingPathPair.projection_homology_bijective` holds in every degree
  without connectivity or Hurewicz assumptions.
- `RelativeDiskLifting` and `RelativeSimplexFiberLifting` construct actual
  boundary-fixed lifts in arbitrary dimension. The lower native fiber
  groups fill the whole boundary in the actual fiber. `Data.next` extends
  the coherent normalization by one dimension; `ofConnectivity` iterates
  it, preserving every original face, support, vertex, and edge identity.
- `RelativeNormalization.ofFiberConnectivity` derives the needed original
  inclusion surjectivity from the genuine fiber sequence. An actual
  homotopy equivalence transfers native connectivity at every point to
  the auxiliary fiber. `EndingPathPair.normalizationData` constructs its
  normalization from the original fiber connectivity.
- `Data.fiberHomologyMap_recoveryLift` and `fiberHomologyMap_surjective`
  now hold in every supplied normalization degree. The theorem
  `fiber_homology_subsingleton_of_fiberConnectivity` constructs both sets
  of data: lower native fiber connectivity and zero relative homology
  imply vanishing of the next actual fiber homology group. No normalization
  or detection assertion is left as an additional input to this theorem.
- `JamesSphere.HigherFiberDetection.fiber_pi_le_seven` applies strong
  induction to the actual James pair, using the existing second through
  seventh Hurewicz equivalences. Native fiber homotopy vanishes in degrees
  1 through 7 at every fiber point. `fiber_homology_le_eight` proves
  homology vanishing in degrees 2 through 8. The original source-image
  inclusion is bijective on native homotopy in degrees 2 through 7 and
  surjective in degree 8.
  **The next missing native fiber degree is 8**, despite its now-vanishing
  homology. Full higher detection, transport to the original comparison,
  EHP, stable sixth-stem/Arf calculation, candidate vanishing, and
  unconditional smooth classification remain unproved.

- `RelativeThreeSimplexLifting.exists_source_filling` lifts the whole
  tetrahedron boundary into the actual two-connected inclusion fiber,
  fills it there, and projects to an exact source filling. The existing
  relative disk lift then gives a homotopy fixing every original boundary
  point. `RelativeThreeSkeletonNormalization` extends this to a coherent
  family in all dimensions, with subspace-valued terminal tetrahedra.
- `RelativeNormalization.Data` records only actual continuous homotopies
  and their checked face, support, vertex, edge, and endpoint identities.
  The all-degree signed cancellation and cone-apex comparison prove that
  its actual fiber-class assignment kills subspace chains and genuine
  boundaries. `Data.fiberHomologyMap` descends to original relative
  homology in every supplied normalization degree. Its raw-simplex,
  projection/connecting, and naturality formulas are proved.
- `ContractibleNativeHomotopy.subsingleton` proves native homotopy
  vanishing at every point, not only at a selected contraction point.
  `EndingPathPair.threeNormalizationData` discharges all auxiliary-pair
  inputs. The original fiber sequence and third Hurewicz prove projection
  bijectivity on third homology; the two connecting formulas give recovery.
- `RelativeNormalization.Data.fiberHomologyMap_surjective_three` transports
  that recovery through the exact ending-path fiber section. Applied to
  the actual James pair, `ThreeSkeletonNormalization.fiber_homologyThree_eq_zero`
  proves third fiber homology vanishing and `fiber_piThree_subsingleton`
  proves native third homotopy vanishing at every fiber point.
  `inclusion_piThree_bijective` and `inclusion_piFour_surjective` identify
  the resulting conclusions for the actual source-image inclusion.
  Native fiber homotopy through degree 7 and homology in degrees 2
  through 8 are now proved above. Full comparison, EHP, stable sixth-stem/Arf
  calculation, candidate vanishing, and unconditional smooth classification
  remain open.

- `RelativeNormalizedFiberClasses.homologyMap_simplex_eq_fiberClass`
  identifies the normalized assignment with the original raw cone-path
  class whenever the first vertex is based. Its actual map is natural
  for based maps of pairs, and projection after it is the original
  connecting homomorphism, with the sign checked on simplex cycles.
- `EndingPathPair` constructs the source-evaluation preimage pair in the
  contractible ending-path space. Its source is homeomorphic to the
  original fiber. An explicit section of the new fiber evaluation
  recovers both the original source point and its whole path exactly.
  Native higher homotopy vanishes in the ambient ending-path space;
  the actual fiber sequence and second Hurewicz prove that its fiber
  projection is bijective on second homology.
- `RelativeNormalizedFiberClasses.recoveryLift` uses this ending-path
  pair to construct an actual right inverse of `homologyMap`. The identity
  `homologyMap_recoveryLift` follows from naturality, the two connecting
  formulas, and the explicit fiber section. Thus `homologyMap_surjective`
  proves detection by third relative homology. No generic naturality
  assertion for the original evaluation prism is assumed.
- `JamesSphere.PairNormalization.fiber_homologyTwo_eq_zero` applies
  this surjectivity to the already acyclic original James pair.
  `fiber_piTwo_subsingleton` then annihilates native second homotopy
  at every point of its actual source-inclusion fiber.
  `inclusion_piThree_surjective`, `transgression_injective`, and
  `prismHurewiczThree_injective` are now proved for that pair.
  Third fiber homology and homotopy vanishing are now proved above.
  Detection in subsequent degrees, full homotopy comparison, the stable
  sixth-stem/Arf calculation, candidate vanishing, and unconditional
  smooth classification remain unproved.

- `SimplexBoundaryChains.cycle` is the actual signed cycle in the
  boundary subspace. Its inclusion image is the boundary of the identity
  simplex. `RelativeBoundaryFiberClass.homologyClass_firstVertex` proves
  that its whole-boundary cone-path class equals the existing fiber class.
- `FourSimplexBoundaryFiber.sum_fiberClass` proves the signed four-face
  relation in actual fiber homology. Common-apex lifts cancel by the
  literal coface identities, and the exceptional face is compared by
  moving the apex along a basepoint-valued first-edge path.
- `RelativeNormalizedFiberClasses.classOperator_boundary` discharges
  these geometric conditions for the coherent normalization and proves
  that the original assignment kills every actual singular four-boundary.
  `homologyMap` therefore descends to the actual relative third homology,
  with checked cycle, simplex, and evaluation-prism representative formulas.
- `JamesSphere.PairNormalization.fiberHomologyMap` is this descended
  map for the original James pair, with all connectivity inputs discharged.
  `assignedPrism_eq_zero` uses the proved relative acyclicity to annihilate
  its assigned evaluation-prism classes.
  The ending-path detection argument above now proves fiber homology
  vanishing and transgression injectivity for the James pair. The generic
  original-prism left-inverse formula is not needed or asserted. Full
  higher comparison and unconditional classification remain unproved.

- `RelativeFiberSubspacePaths.homeomorph` identifies the actual subspace
  of inclusion-fiber paths lying entirely in the source with its actual
  compact-open ending-path space. The explicit contraction proves this
  subspace contractible without a connectivity assumption on the source.
- `RelativeSingularHomology.contractibleSubspaceEquiv` is the actual
  absolute-to-relative homology map, proved bijective above degree one
  using the original pair exact sequence.
- `RelativeSimplexFiberClass.fiberClass` assigns an actual fiber-homology
  class to a relative simplex with based first vertex. Literal barycentric
  cone paths give the relative cycle. A simplex lying wholly in the source
  gives zero. The cone also satisfies the exact retained-face identities.
- `fiberClass_eq_of_pairHomotopy` proves invariance when the boundary moves
  within the source and the first vertex stays fixed. The boundary-fixed
  specialization gives a literal boundary-fixed homotopy of fiber simplices.
- `RelativeNormalizedFiberClasses.classOperator` linearizes these actual
  classes on the original singular three-chains and kills subspace chains.
  `JamesSphere.PairNormalization.fiberClassOperator` applies it to the
  original James pair with all connectivity inputs discharged.
  Four-boundary vanishing, descent, and second fiber homology detection
  are now proved above. Higher-degree detection, full homotopy comparison,
  and unconditional classification remain unproved.

- `RelativeTwoSkeletonNormalization` constructs face-compatible actual
  simplex homotopies preserving the original subspace. Vertices and edges
  are based, then second-homotopy surjectivity compresses triangles into
  the subspace while fixing their boundaries. Every terminal tetrahedron
  has its entire boundary in the subspace.
- `RelativeSimplexHomotopyHomology.endpointCycle_class` proves that
  normalization preserves the original relative homology class. The
  endpoint and genuine prism preserve subspace chains, and the actual
  prism gives the required relative boundary between representatives.
- `RelativeNormalizedThreeHomology.classOperator` assigns actual relative
  three-cycle classes to normalized tetrahedra. It preserves classes,
  vanishes on subspace chains and four-boundaries, and is surjective onto
  the genuine third relative homology. Its signed four-face relation is
  a relation in homology, not an unproved relation in fiber homotopy.
- `JamesSphere.PairNormalization` discharges the connectivity hypotheses
  for the original cylinder pair, including the needed second-homotopy
  surjectivity. `JamesPairRelativeCycles` proves the actual representative
  formula and the preceding homology identities for this pair.
  Four-face compatibility and second fiber homology detection are now
  proved above. Full higher homotopy comparison, the stable sixth-stem/Arf
  calculation, and unconditional classification remain unproved.

- `HomotopyFiberConnectivity.homotopy_subsingleton_of_maps` derives
  actual fiber homotopy vanishing from injectivity and surjectivity at
  consecutive terms of the proved native exact sequence. Degree zero
  and degree one give path connectedness and simple connectivity.
- `JamesSphere.ComparisonFiber.simplyConnectedSpace` proves simple
  connectivity of the original comparison fiber in sphere dimension
  at least two. `ComparisonCylinder.sourceFiber_simplyConnected` proves
  this separately for the actual source-image inclusion fiber.
- `RelativeFiberHomology.transgression` is the genuine degree-raising
  map from inclusion-fiber homology to relative homology, constructed
  from the actual evaluation prism. Both endpoint chain maps factor
  through the original subspace. The cycle condition, boundary sign,
  and descent through categorical homology are proved in every degree.
- `RelativeFiberHomology.connecting_transgression` proves the exact
  connecting-map identity: projection homology minus constant-map
  homology. `ComparisonCylinder.prismHurewiczThree_mk` identifies the
  degree-three obstruction map on each original generalized square.
  Injectivity in fiber degree two is now proved for the James pair,
  as is vanishing of that fiber's second homotopy. Detection in subsequent
  degrees and full homotopy comparison remain unproved. See
  `JamesHomotopyComparisonPlan.md` for the next obligation.
  EHP, the stable sixth-stem/Arf argument, candidate vanishing, and the
  unconditional original-atlas classification also remain unproved.

- `JamesSphere.ComparisonCylinder.relative_homology_subsingleton` proves
  vanishing in every degree for the actual mapping-cylinder pair when
  sphere dimension is positive. The original source is homeomorphic to
  its actual closed image, and the proved pair exact sequence is used.
- `JamesSphere.stage_simplyConnected` and `JamesSphere.simplyConnectedSpace`
  prove simple connectivity of every finite stage and of the full James
  space for sphere dimension at least two. The proof uses the actual
  fat-wedge attachments, their cofibrations, the genuine double-cylinder
  cover and van Kampen, and compact factorization of each original loop.
- `JamesSphere.ComparisonCylinder.comparison_piTwo_bijective` proves the
  actual comparison is an isomorphism on the native second homotopy
  group at every source basepoint, for sphere dimension at least two.
  The loop space, mapping cylinder, and source image are all proved
  simply connected. The second-homotopy conclusion uses the naturality
  of the checked second Hurewicz isomorphism, not a Whitehead assumption.
  **Higher homotopy comparison remains unproved.** Neither relative
  acyclicity nor the checked second-homotopy isomorphism is presented as
  a full homotopy equivalence. The later EHP, stable sixth-stem/Arf,
  candidate-vanishing, and smooth-classification steps are still missing.

- `JamesSphere.HomologyComparison.comparison_homology_bijective_of_pos`
  proves that the actual James comparison induces integral homology
  isomorphisms in every degree for positive sphere dimension.
  `comparisonHomologyEquiv_apply` identifies the equivalence with the
  homology map of the original continuous comparison.
- Natural projection-kernel equivalences for circle products and actual
  suspension covers reduce kernel-map bijectivity to lower homology
  degrees. Restricting the checked word and loop splittings to these
  kernels gives strong induction on degree; actual path connectedness
  handles degree zero. No Kunneth or homotopy-comparison assumption is used.
  **The required homotopy comparison remains unproved.** EHP, the stable
  sixth-stem/Arf argument, candidate vanishing, and original-atlas smooth
  classification also remain unproved.

- `CompactExhaustionHomology` proves compact support for actual singular
  chains, finite-stage lifts of cycles and homology classes, and detection
  of zero classes at a later stage of an increasing compactly exhaustive
  family. `James.HomologyStages` applies these results to the original
  James space and its products, using the proved compact factorization.
- `JamesSphere.WordHomology.projectionActionEquiv` proves the full
  word-space splitting in every positive degree. Its two coordinates are
  the actual projection and prepend homology maps. Surjectivity and
  injectivity follow from the checked finite-stage splitting, exact
  stage naturality, and the actual lifting and zero-detection results.
- `JamesSphere.HomologyComparison.splitting_square` proves that the
  original James comparison commutes with both homology splittings.
  Projection commutes exactly; prepend uses the constructed action
  homotopy. `product_bijective_iff` identifies the two bijectivity
  questions but does not establish either one.
  The homology-isomorphism conclusion is now proved above. The
  homotopy comparison is not yet proved. The subsequent EHP,
  stable sixth-stem/Arf argument, candidate vanishing, and smooth
  classification remain unproved.

- `PushoutOutsideAttachment` proves that an open or closed embedding
  disjoint from the attaching image remains so after a native pushout.
  The double cylinder's two end inclusions are closed embeddings without
  injectivity assumptions on the original span.
- `DoubleMappingCylinder.lowerEquiv` and `upperEquiv` have the literal
  end inclusions as their forward maps. `overlapHomeomorph` identifies
  the actual overlap with the open middle interval times the attaching
  space. `overlapEquiv` inserts the literal midpoint; composing with
  the cover retractions recovers the original attaching maps exactly.
- `DoubleMappingCylinder.attachingHomologyEquiv` derives the joint
  attaching-map homology isomorphism from the genuine open-cover
  Mayer--Vietoris sequence when the actual double cylinder is contractible.
  Its two map coordinates and removal of the second sign are proved.
- `JamesSphere.StageHomology.projectionActionEquiv` applies this to
  the proved contractible James double cylinders. For every positive
  degree it identifies the actual projection to the kth stage and
  prepend to the next stage as a joint integral homology isomorphism.
  The passage from finite stages to the full word space is now proved
  above. The James homotopy comparison, EHP, stable sixth-stem/Arf argument,
  candidate vanishing, and smooth classification remain unproved.

- `CompactAdjunction.isPushout` proves the native topological pushout
  property of the original auxiliary quotient. `DoubleMappingCylinder`
  constructs the actual inserted cylinder using two native pushouts,
  with exact jointly continuous gluing on both ends and the cylinder.
- `DoubleMappingCylinder.exists_collapse_equiv` proves that the literal
  cylinder collapse is a homotopy equivalence when the left attaching
  map has homotopy extension. The inverse and both inverse homotopies
  are constructed on the actual spaces. Applied to the James attaching
  maps, `ConeStage.exists_double_equiv` identifies the actual collapse,
  and `doubleSpace` is proved contractible.
- The cylinder height gives the genuine open cover below two thirds and
  above one third, with exact endpoint and interior-cylinder formulas.
  `lowerMotion` and `upperMotion` start at the identity, preserve their
  respective open pieces, fix the end spaces, and end in the right and
  left end-space images, respectively.
  The cover-piece and overlap equivalences and their homology-map
  identifications and the full word-space splitting are proved above.
  The James homotopy comparison, stable sixth-stem/Arf argument, and unconditional
  smooth classification remain unproved.

- `JamesSphere.ReducedCone.Space` is the actual compact Hausdorff range
  of generator prefixes. The exact quotient fibers collapse only zero
  length and the basepoint letter. Its original sphere boundary is a
  closed embedding and has homotopy extension. An explicit shrinking-time
  contraction fixes the cone point.
- `JamesSphere.ConeStage.Space` attaches this cone times the kth word
  stage to the next word stage by the literal prepend map. The actual
  adjunction quotient is proved compact Hausdorff, with the original
  word stage embedded as a closed subspace. Exact fiber formulas and
  closed embeddings between successive auxiliary stages are proved.
- `exists_stage_deformation` constructs a strong deformation retraction
  of each auxiliary stage onto its actual embedded predecessor. Its
  inverse image is the proved product-boundary cofibration, and all
  nontrivial quotient fibers lie over the predecessor. The first stage
  is homeomorphic to the reduced cone. Induction proves
  `ConeStage.contractibleSpace` for every stage and proves vanishing of
  its positive-degree integral singular homology.
  The cone-cover homology calculation and both finite-stage and full
  word-space splittings are now proved above. The James homotopy comparison,
  EHP, stable sixth stem, Arf detection, candidate vanishing, and
  classification remain unproved.

- `SpherePointCofibration.data` constructs actual neighborhood-deformation
  data at any point of the standard sphere. Its supported time cutoff uses
  the stereographic contraction of the antipodal complement.
  `FatWedge.sphere_hasHomotopyExtension` proves homotopy extension for
  arrays with at least one basepoint entry, by product-boundary induction.
- `JamesSphere.StageAttachment.isPushout` proves the literal
  Cartesian-power quotient attachment. `hasHomotopyExtension` and
  `isClosedEmbedding` apply to each original inclusion from the kth James
  stage to the next, using the proved fat-wedge fibers and quotient topology.
- `RelativeCompression.exists_relative` straightens a homotopy of pairs
  into the target subspace while fixing a source cofibration.
  `QuotientRelativeCompression.exists_deformation` descends it through an
  actual quotient whose nontrivial fibers lie over that subspace.
  These supply the extension and descent steps now applied to the actual
  auxiliary cone stages above. The full word-space splitting is also
  proved above. The James homotopy comparison, EHP, stable sixth stem, Arf detection,
  and classification remain unproved.

- `JamesSphere.Overlap.middleDeformation` gives a strong deformation
  retraction of the actual twice-punctured sphere onto the actual middle
  slice. The scale-two stereographic formulas and dilation are proved.
  `pathEquiv` lifts this to the actual restricted ending-path spaces;
  its forward map is the literal inclusion.
- `JamesSphere.CoverMaps.lowerHomotopy` and `upperHomotopy` identify
  the actual cover maps with projection and generator concatenation.
  The homotopies move the start of the generator tail within its respective
  hemisphere, and use a continuous native-path unitor at the endpoint.
- `JamesSphere.LoopHomology.projectionActionEquiv` proves that these
  actual projection and concatenation maps jointly induce an integral
  homology isomorphism in every positive degree. The signed
  Mayer--Vietoris map is identified and its second sign is removed.
  The full word-space splitting and its comparison square are now proved
  above. **The James comparison equivalence remains unproved**, as do EHP
  exactness, the stable sixth-stem computation, Arf detection, candidate
  vanishing, and smooth classification.

- `SpherePathCover.contraction` strongly contracts an actual punctured
  sphere to any specified remaining point through its stereographic chart.
  `JamesSphere.punctureCoverHomologyEquiv` applies the path-cover homology
  splitting to two explicit, proved-distinct points on the actual generator.
  Both cover pieces contain the original sphere pole.
- `HomotopyFiberDeformationRetract.equivalence` lifts a specified source
  deformation retract to a genuine equivalence of the actual homotopy fibers.
  Applying it to the two endpoint slices proves homotopy invariance of these
  fibers. A nullhomotopy gives `nullhomotopyEquiv` with the source times
  native loops. Its inverse is proved to follow the specified homotopy
  and then the supplied loop, with the source coordinate unchanged.
- `loopEvaluation_isQuotientMap` proves that the actual sphere-loop
  evaluation is a surjective quotient map. `clock_eq_iff` identifies only
  the interval endpoints; interior time slices are closed embeddings.
- `middlePathEquiv` identifies the actual inverse image of the middle
  sphere slice under path evaluation with the sphere times native loops.
  Its inverse curve is exactly the remaining half of the original
  generator followed by the loop, and its initial point is the specified
  middle-slice point.
- `clock_eq_coordinate` identifies the actual finite clock with tangent
  compactification. Its quarter, middle, and three-quarter coordinates are
  exactly -1, 0, and 1. `middle_finite` identifies the middle slice with
  the compactified coordinate hyperplane, and the two puncture formulas
  give the literal finite axis points.
  The actual overlap and its homology maps are now identified above.
  The full word-space splitting is proved; the James homotopy comparison remains unproved.
  These results do not prove the James comparison equivalence, the stable
  sixth-stem computation, Arf detection, candidate vanishing, or smooth
  classification.

- `Moore.Loop.normalizationEquiv` proves a genuine ordinary homotopy
  equivalence between variable-duration Moore loops and native unit-interval
  loops. Its explicit duration-adjustment homotopy keeps normalization
  unchanged. The duration-one inverse does not preserve the zero-duration
  Moore unit. **This is not the James loop-space equivalence.**
- `multiplicationHomotopy` compares normalized Moore multiplication with
  native path concatenation. `JamesSphere.actionHomotopy` applies it to the
  actual generator and reduced-word comparison. The word action is jointly
  continuous with its locally compact sphere parameter.
- `ComparisonCylinder.action` glues the word and loop actions on the actual
  topological mapping cylinder, using compact-parameter pushout descent.
  Its source and target restrictions are proved exactly, and it preserves
  the actual source subspace. No comparison equivalence is assumed.
- `EndingPath.Space` is the compact-open space of paths ending at the chosen
  point. Evaluation at zero has native path-space fibers; moving the initial
  time to one gives an explicit contraction of the total space.
- `HomotopyFiberStrongContraction.equivalence` uses the previously proved
  transport formula to identify the actual homotopy fiber with native loops
  when a strong contraction of its source to the specified point is supplied.
  `EndingPath.restrictionHomeomorph` identifies actual projection inverse
  images with these homotopy fibers. The inverse loop map is the literal
  inclusion, not an unspecified equivalence.
- `EndingPath.cover_left_bijective` proves that the signed intersection map
  of any actual two-open-set cover of the contracted path space is bijective
  on positive-degree integral homology. `loopCoverHomologyEquiv` identifies
  its two target groups with loop homology for a base cover supplied with
  strong contractions to the terminal point.
  The concrete punctured-sphere cover and its identification with the actual
  projection/loop-action map, full word-space splitting, and comparison
  square and comparison homology isomorphisms are now proved above. The
  homotopy comparison remains unproved, as do EHP exactness, the stable
  sixth-stem computation, Arf detection, candidate vanishing, and classification.

- `JamesSphere.Cell.characteristic` gives the actual characteristic map
  of each length-`k` stratum from the max-norm disk in dimension `k * n`.
  Its open disk is injective and maps exactly to words of length `k`.
  Its boundary maps to strictly shorter words. For positive `n`, the
  closed disk maps onto the original `k`th James stage.
- `chart_continuousOn_symm` proves continuity of the actual inverse cell
  chart by restricting the compact closed-disk quotient to the open
  exact-length stratum. The characteristic maps and partial inverses are
  not hypotheses in the resulting CW structure.
- `JamesSphere.CW.cwComplex` constructs Mathlib's genuine classical
  `CWComplex` on the original James space for `n > 0`. Closure finiteness
  and the weak topology are proved. The structure is of finite type, with
  one cell in each dimension `k * n` and no cells at other dimensions.
- `skeleton_eq_stage` identifies the native `k * n` skeleton with the
  original length-`k` stage. `zero_skeleton` identifies its zero-skeleton
  with the empty word. Path connectedness is proved for positive-dimensional
  spheres; more generally, the James construction preserves path connectedness.
  **The CW prerequisite is proved, but the loop-space equivalence is not.**
  EHP exactness, the stable sixth-stem computation, Arf detection, candidate
  vanishing, and original-atlas classification remain proof obligations.

- `James.exists_continuous_stage_factorization` proves that every continuous
  map from a compact space into the actual James space factors through a
  finite reduced-word stage when the base space has closed points. This
  includes sphere maps and homotopies. Compactness of the stages themselves
  is proved when the base space is compact.
- `Moore.Loop` is a genuine topological monoid of variable-duration loops.
  Its unit and associativity hold before quotienting by homotopy.
  `continuous_timed` proves continuity even where duration vanishes, using
  compact-open neighborhoods of the constant unit-interval loop.
- `JamesSphere.loopComparison` constructs the actual continuous comparison
  into Mathlib's native based path space on the standard next-dimensional
  sphere. Its one-letter value is the explicit product-compactification
  suspension adjoint. The Moore-loop lift preserves products and the unit.
- `mooreComparison_injective` follows from unique excursion factorization:
  the non-pole generators have positive duration and no interior pole visit.
  Consequently the James sphere space is Hausdorff. Its finite stages are
  compact Hausdorff, their Cartesian-power presentations are quotient maps,
  and `isClosedEmbedding_stageMooreComparison` gives closed embeddings of
  these stages into the actual Moore-loop space.
  **No embedding of the whole James space into Moore loops is asserted.**
  The CW structure and characteristic maps are now supplied above.
  The required loop-space equivalence (in positive sphere dimensions),
  EHP exactness, stable sixth-stem computation, and Arf detection remain
  unproved. These constructions do not prove that the candidate's stable
  class vanishes.

- `James.Space` is constructed as reduced words with the final topology
  from all finite Cartesian powers. `continuous_iff_on_words` proves its
  continuity criterion, and `word_delete_basepoint` checks the defining
  basepoint-deletion relation.
- `James.secondHopfMap` is the actual continuous ordered-pair word map.
  `JamesSphere.hopf` specializes it to the product-compactification pairing
  of the genuine standard spheres. Its one-letter composite is constant,
  and its two-letter value is the prescribed sphere pairing.
  **These are map constructions, not an EHP exactness theorem.** The
  James/loop-space equivalence, required exactness, stable sixth-stem
  computation, and Arf detection remain unproved.

- `OnePointProduct.addFactor_assoc` and the coordinate-naturality identities
  compare genuine compactification products everywhere, including infinity.
  `EuclideanFactorProduct.step_square` identifies a direct Euclidean factor
  with successive real factors under explicit coordinate homeomorphisms.
- `SphereRepresentative.iterate_nullhomotopic_iff` transports an actual
  map square through every finite suspension. The two sphere representatives
  may use different coordinate homeomorphisms and dimensions.
- `EuclideanFactorProduct.iterate_nullhomotopic_iff_product` compares the
  direct product by a Euclidean q-space with q ordinary suspensions, after
  any further number of suspensions. `finite_product_nullhomotopic_iff`
  proves equality of their finite vanishing criteria.
- `AffineProductCollapse.finite_collapseData_nullhomotopic_iff` applies that
  comparison to the actual affine product collapse. Positive radius
  normalization is removed by the proved same-frame collapse homotopy.
- `RoundedTrace.surgery_cubicalStableClass_eq_one_iff` proves that the actual
  surgery target's stable collapse class is the identity exactly when the
  original manifold's class is the identity. The original orthonormal frame,
  original atlas, independently constructed surgery atlas, and arbitrary
  collapse choices are retained. The input ambient dimension is at least
  eight, and the attaching product has radius two.
  **This preserves vanishing; it does not prove either class vanishes.**
  It is not a computation of the stable group or the missing Arf detection
  theorem. Middle surgery alone does not settle the candidate, whose middle
  homology is already zero.

- `cubicalStableClass_eq_of_same_frame` proves actual native stable-group
  equality for arbitrary collapse choices on the same framed embedding.
  It uses the constructed sphere homotopies and native based-group comparison.
- `RoundedTrace.endpoint_cubicalStableClass_eq` proves equality for arbitrary
  collapse choices on the two actual framed surgery endpoints. The original
  endpoint here retains its height-cylinder embedding and signed normal frame.
- `SmoothRangeFrame.normalized` packages the actual smooth orthonormal frame
  on the original projection range. Normalization fixes an already
  orthonormal frame exactly and is idempotent. Separately,
  `FramedCollapseData.normalized` positively rescales the actual collapse
  target to make its radius one and its normal derivative the identity.
- `AffineProductCollapse.collapseData` constructs genuine collapse data for
  affine product coordinates, with exact zero fiber, smooth coordinates,
  surjective derivative, and the prescribed normal frame. Its map is the
  literal product compactification of the normalized old collapse and
  the identity on the added Euclidean factor.
- `OriginalEnd.orthonormalInputCollapseData` supplies these coordinates
  for the actual trace, accounting for all six added directions, the height
  translation, the column permutation, and the last-column reflection.
  `surgery_cubicalStableClass_eq_orthonormal_product` identifies the actual
  surgery class with this product representative while retaining the
  original orthonormal input frame and original manifold atlas.
  **No class is proved trivial.** The six-factor product/suspension comparison
  is now supplied above. The group computation, Arf detection, and
  classification remain unproved.

- `exists_sphere_map_prescribed_pair` prescribes the values at two distinct
  source points by actual orthogonal path lifts and localized homotopies.
- `SemicircleSuspension.descend` descends continuous families of paths
  through the actual suspension quotient. The inverse cosine time change
  gives exact recovery on meridians and descends whole homotopies.
- `SphereMapSuspension.exists_homotopic_suspension` proves surjectivity
  of the literal ordinary suspension when `m + 2 < 2 * (n + 1)`.
  Its representative is constructed using the minimum-path comparison.
- `CubicalStableSix.stepHom_surjective` proves surjectivity of the
  actual cubical group transition for `k ≥ 5`. The already proved
  injectivity gives `stepMulEquiv` and `stableMulEquiv` for `k ≥ 6`.
- `piFourteenSphereEightMulEquiv` is a genuine group isomorphism from
  the native `π₁₄(S⁸)` to the constructed stable sixth-stem group.
  Its forward map is the actual cubical direct-limit map. **This does not
  compute the group, prove Arf detection, or prove the candidate's class
  is the identity.** The comparison of the candidate's ordinary-suspended
  class with its original stable class remains an equivalence of vanishing,
  not an asserted equality between the ordinary and cubical transitions.

- `sphere_homotopicRel_finite_of_homotopic` corrects a homotopy into a
  simply connected sphere at finitely many marked points. The inverse
  orthogonal correction is localized away from points already fixed, and
  both original endpoint maps remain unchanged.
- `SemicircleSuspension.minimumPath_eq_latitude` identifies the actual
  minimum semicircles with the existing suspension latitudes under an
  explicit cosine time change and the genuine zero-head equator.
  Fixing both poles and currying gives native fixed-endpoint path homotopies.
- `SphereMapSuspension.homotopic_of_map_homotopic` proves reflection for
  the literal ordinary suspension when `m + 3 < 2 * (n + 1)`.
  `iterate_nullhomotopic_iff` proves that all later suspensions retain
  exactly the same nullity in this range.
- `CubicalStableSix.ofNative_injective` proves that the actual native
  sixth-stem groups inject into the constructed stable group for `k ≥ 6`,
  that is, from target dimension eight onward.
- `SixSphereThirteen.stableClass_eq_one_iff_suspendedNativeClass` reduces
  the candidate's stable identity to identity of its actual once-suspended
  class in the native group `π₁₄(S⁸)`. **That class is not proved to be the
  identity.** This is finite-stage detection, not a group computation or
  the missing implication from zero geometric Arf invariant.

- `GenericLinearAvoidance.ae_avoids_zero` proves actual linear-parameter
  avoidance of every vector in a lower-dimensional nonzero smooth family.
  Parametric Sard supplies the result on open charts, including countable
  simultaneous families; it is not a genericity hypothesis.
- `LinearProjection.ae_good` simultaneously avoids all secants and nonzero
  tangent vectors of the original compact manifold embedding. Good linear
  projections are dense whenever the target dimension exceeds twice the
  manifold dimension. `exists_euclideanEmbedding_twice_add_one` constructs
  a closed smooth embedding in that precise dimension, with original atlas
  and injective native differential.
- `SixSphereThirteen.embedding` and `frame` now construct the candidate's
  actual framed embedding in dimension thirteen, with normal rank seven.
  Its `sphereMap` is a literal map from the standard thirteen-sphere to
  the standard seven-sphere. `nativeClass_eq_original` and
  `stableClass_eq_original` identify its native and stable classes with
  the constructed original collapse. **Neither class is proved trivial.**

- `CubicalSphereSuspension.hom` is a proved homomorphism of Mathlib's
  native homotopy groups. Its representative is exactly the existing
  product-compactification map on the whole cube, including its boundary.
  Its iterates preserve precisely the same nullity as ordinary suspension.
- `CubicalStableSix.Group` is the commutative direct-limit group of these
  homomorphisms. Identity in this group is equivalent to a finite-stage
  identity witness, and for sphere representatives to a finite ordinary
  suspension nullhomotopy.
- `FramedCollapseData.cubicalStableClass_eq_one_iff_finite` applies that
  criterion to the original framed collapse. The group and the comparison
  are constructed, not postulated. **The candidate's identity equality
  remains unproved.** The transition surjectivity and injectivity ranges
  above are proved; an order-two computation and Arf detection remain unproved.

- `nativeStageEquiv` identifies each actual sphere-map stage with
  Mathlib's native `HomotopyGroup (Fin (k + 8)) (Sphere (k + 2))`.
  A loop contraction and an exact orthogonal lift turn ordinary sphere
  homotopies into based homotopies without changing their endpoint maps.
  The native identity corresponds to the original constant-map class.
- `nativeStep_sphereClass` identifies the native transition with the
  literal suspension of the original sphere map. `nativeClassEquiv`
  identifies the two actual directed limits and preserves their constants.
  These ordinary-suspension transitions have proved identity preservation.
  Their equality with the separate cubical homomorphisms above is not asserted;
  the proved comparison preserves nullity after every finite suspension.
- `nativeSixthStageClass` is the native cube-relative class of the
  original framed collapse. `nativeStableCollapse` corresponds to its
  existing stable collapse class. Equality with the identity is equivalent
  to an actual finite native identity witness, and to an actual finite
  suspension nullhomotopy. **No such equality is inferred.**

- `FramedCollapseData.sphereMap_homotopic` constructs a homotopy between
  any two collapse records for the same compact smooth framed embedding.
  A uniform normal-coordinate estimate gives an open neighborhood where
  convex interpolation has exactly the original zero fiber. A supported
  local homotopy and the fiber-germ comparison give the global homotopy.
  No equality of local germs is assumed. The comparison retains nullity
  at every specified finite suspension stage.
- `sixthStableClass_eq_of_same_frame` proves equality in the actual
  direct limit for these collapse choices. The embedding and frame remain fixed.
- `exists_nonzero_canonical_tube_representative` now gives a regular-fiber
  representative whose actual canonical framed-tube collapse has nonzero
  stable class. Its finite-suspension nullity is compared with that of the
  original sphere map. Two-connectivity and Arf detection are not inferred.

- `exists_nonzero_framed_collapse_representative` constructs a nonempty
  smooth regular six-dimensional fiber for every nonconstant stable class.
  Stereographic coordinates give an actual Euclidean embedding and the
  normal frame induced by the original regular equations. The associated
  `FramedCollapseData` map is exactly the original sphere map conjugated by
  explicit homeomorphisms, and preserves nullity at each finite suspension.
  Its stable collapse class is proved nonconstant. This does not assume the
  fiber is two-connected or compute the stable group. The comparison with
  the canonical tube collapse is now supplied by the results above.

- `StableSixSphereMaps.Class` is the directed limit of actual homotopy
  classes of maps `Sphere (k + 8) → Sphere (k + 2)`, with literal suspension
  transitions. `ofMap_eq_nullClass_iff` proves that equality with its constant
  class gives exactly a finite ordinary suspension nullhomotopy. The native
  comparison above is proved; no two-element computation is assumed.
- `FramedCollapseData.sixthStableClass_eq_null_iff` applies this criterion to
  the original framed collapse, using only equality of natural-number dimensions.
- `exists_originalAtlas_filling_of_stable_class_zero` constructs the actual
  normally framed filling and original-atlas boundary diffeomorphism from that
  stable-class equality. **The equality remains an explicit hypothesis.**
- `exists_sixSphereStableCollapseData` constructs the candidate's frame and
  collapse at sufficient codimension and retains the finite-witness criterion.
  More generally, the framing is constructed at any prescribed large codimension.

- `OnePointProduct.productMap` is constructed on the actual product
  compactifications. Jointly continuous based homotopies descend through
  the compact product quotient. `OpenFiberCollapse.productTube_collapseMap`
  proves exact equality with the actual collapse of the product tube.
- `SuspensionProductComparison.quotientEquiv` constructs a homotopy inverse
  of the actual meridian quotient. Its exceptional fiber is computed, and
  a supported whole-sphere contraction preserves that fiber at every time.
  The endpoint and homotopy descend through the original quotient maps.
- `FramedTubeData.product_collapse_nullhomotopic_iff` transfers actual
  nullhomotopies in both directions between the original product-tube
  collapse and the ordinary suspension of the original framed collapse.
- `FramedTubeData.iterate_product_collapse_nullhomotopic_iff` retains this
  comparison after every specified finite number of further suspensions.
  Explicit Euclidean product coordinates and the constructed sphere homotopy
  equivalences supply both inverse homotopies at each stage. This does not
  assert that either compared map is nullhomotopic.

- `SphereFiberGerm.exists_homotopy_of_fiber_germs` constructs a homotopy
  between original sphere maps which agree near their common distinguished
  fiber. Every point where the endpoints agree, including a shared basepoint,
  stays fixed. Equality only on the fiber is not being treated as enough.
- `FramedCollapseData.iterate_nullhomotopic_iff_of_fiber_germs` applies the
  comparison to the actual framed collapse and preserves nullhomotopy at
  each specified finite suspension stage.
- `FramedCollapseData.exists_originalAtlas_filling_of_iterate_nullhomotopic`
  constructs a compact normally framed filling with the entire native
  boundary diffeomorphic to the original manifold and atlas. The smooth
  regular representative is constructed. The boundary inclusion is exactly
  the iterated equatorial embedding. **The actual finite-suspension
  nullhomotopy remains an explicit hypothesis.** Equality with a separately
  prescribed original boundary frame is not asserted.

Previously checked:


- `EuclideanEmbedding.cap_pairing_eq_geometric_form` identifies the original
  cap and geometric intersection pairings on **all** native mod-two middle
  classes of a normally framed compact two-connected six-manifold (`Type`).
  The existing native kink insertion and finite Whitney cancellation construct
  embedded representatives; their existence is not a new hypothesis.
- `modTwoHomologyIntersection_nondegenerate` and
  `modTwoHomologyQuadraticForm_nondegenerate` follow from the proved cap duality.
- `GeometricArf.invariant` uses the actual finite middle group and original
  quadratic form. Its value on a candidate six-sphere is proved zero.
- `GeometricArf.invariant_preserved_by_unit_surgery` uses the actual native
  surgery isometry and the constructed target atlas. An attaching product
  and an integral unit detector remain explicit surgery data. No separate
  nondegeneracy or integral second-homology assumption is needed.

The integrated build and all 11506 axiom-dependency checks passed; the only
reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The source scan found no placeholders, extra axioms, or limit overrides.
Computational limits remain unchanged.

Still missing: a proof that the actual candidate's class in `π₁₄(S⁸)` is
the identity, equivalently that its stable collapse class is the constant
class. Zero geometric Arf has not been proved to give this equality.
The original-atlas filling consequences are checked but not their premise. Seven-dimensional
surgery and original-atlas classification remain further obligations.
The universe lift is already proved in `Transport.lean` and must be applied
after proving base-universe rigidity.



The current section above supersedes older statements of unfinished work below.


The unconditional six-sphere theorem is still unproved. The current construction
has a compact rounded attachment with a global smooth boundary atlas,
an exact native boundary-set description, immersive ambient inclusion, and
a full smooth normal frame. The whole attaching collar matches the original
map and frame. The actual native boundary now has a constructed six-dimensional
atlas, and its original end is diffeomorphic to the original manifold in its
original atlas. The boundary inclusion is immersive, and the compact boundary
splits smoothly into the original manifold and a compact complementary end.
The latter contains the whole handle and rounded collar boundary; its cylinder
piece is precisely at height zero. The rounded collar has explicit
`S³ × S²` times an interval coordinates. The unchanged handle is now exactly
an open four-ball times `S²`, and the retained original piece is exactly the
original manifold outside a closed tube. Their native diffeomorphisms, exact
collar overlap domains, and ambient overlap maps are checked. The entire
framed attaching data can now be normalized to surgery radius one, and the
three piece maps into the independently constructed canonical surgery atlas
are smooth and agree on both overlaps. Their global assembly, bijectivity,
and smooth inverse are now checked: the actual complementary end is
diffeomorphic to canonical surgery in its independently constructed atlas.
The full native boundary is smoothly the original manifold plus that surgery.
The smooth local outward normals now agree exactly and descend globally.
Appending the outward column last gives a full smooth orthonormal frame of
the actual boundary normal space. The original-end comparison, including the
positive height sign and the explicit permutation to ordinary six-coordinate
stabilization, is checked. Transport to canonical surgery is now also checked,
including its actual Euclidean embedding, full normal range, exact piece
formulas, and standard normal-model frame. The chosen collapse maps are now
compared through the actual trace, including tube choices, coordinate changes,
and smooth regular sphere representatives. General framed-bordism detection,
filling, and final classification remain unproved.
The sections below record successive geometric constructions.

The original middle cap-evaluation pairing is now proved nondegenerate.
The required equality with the geometric intersection pairing remains
unproved, so this does not yet supply the geometric surgery obstruction.
Proper pullback and an actual product normal-fiber class are checked,
including unit cap augmentation after restriction to every fiber.
The sphere-product cap is now the original zero-section class. Constructed
internal open tubes give actual supported duals of framed embedded spheres
in the original manifold. Native transversality, the actual inverse tube,
and original point pullbacks now prove local intersection-count evaluation.
The cap and geometric pairings agree for an embedded immersive first sphere
and every second homology class. The internal normal frame is constructed
from the manifold framing. Coverage of arbitrary first classes remains required.

The resolution-frame prerequisite now has an actual three-to-six tangent
remainder, a checked source-only formula, and a proved Whitney comparison.
Constructed reference charts give the frame sum at sufficiently small scales.
The actual clean resolution satisfies the corrected quadratic-parity identity.
Preparation of arbitrary sphere classes, native-addition comparison, and
quadratic descent to actual mod-two middle homology of two-connected framed
compact six-manifolds are now checked. The constructed form has the actual
geometric intersection pairing as its polar form. General nondegeneracy and
framed-bordism detection remain unproved.

Arbitrary based sphere pairs now have constructed smooth self-transverse
immersed representatives, unique common-center fibers, and mutual native
transversality everywhere. Based homotopies, protected model insertion,
derivative preservation, simultaneous genericity, and regular slices are all
checked. The quadratic identity now holds for arbitrary continuous based
inputs and the original hemisphere pinch, with both cap reparametrizations
explicitly removed. Actual hemisphere-collapse homotopies and homology exchange
give the integral class sum; the native Hurewicz isomorphism and exact
coefficient reduction give the quadratic descent. The integrated checkpoint
has 9234 successful dependency
audits. The original compact-support cap map on Euclidean models of
dimension at least three is now proved bijective in every complementary
degree. Manifold local-to-global duality is now proved; geometric nondegeneracy
remains unproved. Actual relative cohomological excision and Mayer–Vietoris
are now checked with their original maps. Actual compact-support
open-embedding extension is functorial, and cap commutes with open
inclusion. The actual compact-support connecting map, all three
Mayer–Vietoris exactness identities, and degree-zero injectivity are now
proved. Localized cap chains and their boundary formulas, and original
connecting-cochain lifts, are now checked. Cap connecting-map compatibility
and manifold local-to-global duality are now proved.

The actual mod-two middle homology of a two-connected compact smooth
manifold is now proved finite. The finite Morse sequence, its actual handle
homology maps, and its regular-band homeomorphisms prove integral finite
generation; exact coefficient reduction gives the finite mod-two vector
space. This supplies the finiteness needed by the Arf algebra, but does not
establish intersection nondegeneracy or bordism detection.

## Checked geometric product

For an actual smooth embedded immersive sphere `f : S³ → M`, the theorem
`EuclideanEmbedding.exists_radialFramedDiskThickening` uses the original embedding
and normal frame and constructs all of the following from `M ≃ₜ S⁶`:

- An actual `StabilizedSpanningDisk.DiskData` with boundary the six-coordinate
  stabilization of `e ∘ f`, the prescribed open collar, and interior avoiding
  the old ambient space.
- A smooth orthonormal partial normal frame `T` over the closed four-disk,
  with the exact radial original normal columns and five graph axes on a whole
  closed inner annulus, where the disk retains its prescribed collar formula.
- A smooth orthonormal three-frame `C` spanning the orthogonal complement
  of the combined `T` and actual disk-derivative columns, exactly equal to
  its radial boundary values on the same annulus.
- A positive radius for which `H(x,v) = D(x) + C(x)v` embeds the entire closed
  product `D⁴ × D³` and has injective derivative everywhere on it.
- A full smooth orthonormal normal frame of `H` on that product, agreeing
  exactly with `T` along the original disk core. Its boundary-core values
  are the specified original normal columns and graph axes.

`SmoothProjectionDiskFrame` transports projection ranges along the disk
contraction, extends the continuous frame, and smooths it by projection and
normalization. `SmoothDiskNormalComplement` applies this to the actual combined
operator, whose complementary rank is proved to be three.

`DiskThickening` computes the exact core derivative and normal space.
`CompactCoreImmersion` proves local and compact-neighborhood injectivity from
pointwise smoothness at the core, using actual inverse functions of a left-inverse
projection. It does not assume a uniform smooth neighborhood of a pointwise
infinitely differentiable compact locus. `EmbeddedDiskThickening` then applies
the product tube lemma to obtain one positive radius.

`ThickeningNormalFrame` projects `T` into the actual normal spaces of `H` and
normalizes. A further uniform radius preserves injectivity, and actual rank
equality gives a full frame. The derivative's source is first put in Euclidean
seven-dimensional coordinates: the plain product norm is not an inner-product
norm, so the Gram formula is not applied directly to it.

`FramedDiskThickening.FramedProduct` retains this data and its exact core formula.
Its constructor works for any actual embedded disk with the required smooth
partial normal extension. The candidate-specific theorem obtains that extension
from the proved geometric parity vanishing, not from a new hypothesis.

The full main-module build and all 7488 dependency audits pass with only the
standard Lean axioms, no placeholders, and unchanged computational limits.

## Checked original-atlas neighborhood and first-order comparison

`SphereInternalNormalSpace` defines the actual intersection of the original
manifold tangent image and the orthogonal complement of the sphere derivative.
Its dimension is proved to be three. `SpanningDiskBoundaryComplement` compares
this space with the actual stabilized collar and normal columns.

There is now also a construction independent of the spanning disk:
`SphereInternalNormalFrame` frames the rank-three projection of any smooth
immersed three-sphere by contracting its genuine general-linear clutching
map. It does not assume zero parity. For an embedding, the actual internal
tube then gives a disjoint homotopic push-off and zero self-intersection.
This does not give a compatible framed spanning disk at nonzero parity.
`SelfTransverseSphereRepresentative` constructs self-transverse immersions for
arbitrary continuous sphere maps. Their transverse normal push-offs have the
same finite count as their ordered double-point sets. The free sheet swap
proves this count even, giving general geometric self-intersection zero and
homological alternation. Eliminating double points remains a separate problem.

`GeometricSphereParity` now extends the disk-compatible parity to arbitrary
continuous sphere maps through actual self-transverse immersed representatives.
It is homotopy invariant and vanishes on nullhomotopic maps. This does not
remove the embedding requirement from the attaching-product construction:
the quadratic identity, homological descent, and the necessary global
surgery and bordism-detection arguments remain unproved.

`ManifoldSphereTransverseFrame.transverse_range_boundary` identifies the entire
constructed three-plane with the stabilization of this original internal normal
space. `append_boundaryTransverse` proves there are no added-coordinate components.
The projected three-frame is smooth, norm preserving, and spans the full
internal normal space, rather than just lying in the ambient disk normal space.

`TubularRetractionDifferential` proves that the actual retraction differential
is inverse to the embedding differential on the original tangent image.
`AmbientSphereTube` computes the native derivative of `e(f(s)) + C(s)v`, and
`SphereTubeCoreImmersion` proves its range is the original six-dimensional
tangent image. `InternalSphereTube` applies the original retraction and proves
invertibility of the native core derivative and actual local inverse existence.

`CompactLocalDiffeomorph` and `EmbeddedInternalSphereTube` produce a single
positive radius for a closed embedded `S³ × D³` in the original manifold, with
local diffeomorphisms throughout it and all points in the actual retraction
domain. `SixSphereAttachingNeighborhood` assembles this with the candidate's
constructed framed disk and the exact original boundary normal columns.

`FramedDiskAttachingComparison.thickening_boundary_affine` is an exact formula
on the entire affine face, not only at zero. The embedded retracted tube has
the same native derivative as that affine tube at the zero section. Equality
away from the zero section has not been proved and is not being assumed.

## Next geometric obligations

1. Use the constructed actual normally framed surgery trace in the global
   framed-bordism argument. Its boundary normal ranges, original-end
   stabilization, canonical surgery embedding and full frame, and exact
   piece formulas are now checked in the independently constructed atlases.
2. Prove the global surgery and framed-bordism detection statements needed to
   produce a filling. Candidate middle-homology and Arf vanishing do not supply
   this step. The final original-atlas diffeomorphism remains a further obligation.

The repository already contains a genuine surgery quotient and its native
smooth atlas in `SmoothSixDPoincare/FramedSurgeryBoundary` and
`FramedSurgerySmoothBoundary`. `FramedSurgeryPresentationComparison` compares
closed-piece presentations topologically. The new smooth comparison uses the
actual open boundary pieces and does not rely on that topological comparison.
The non-unit seam mismatch is now resolved by an explicit transverse linear
normalization, preserving all fields of the actual framed attaching product.
The construction radius becomes two and the surgery radius one. Both sides
then use exactly the same squared-radius coordinate. `UnitSurgeryOverlapMaps`
proves agreement in the existing quotient, and `UnitSurgerySmoothMaps` proves
smoothness in its independent atlas. `UnitSurgeryComparisonMap` uses
`SmoothOpenCoverRestriction` to glue these maps. `UnitSurgeryTargetCover` proves
surjectivity, and `UnitSurgeryOverlapFibers` recovers exactly the actual overlaps
from quotient equality. `UnitSurgeryComparisonDiffeomorph` proves the smooth
inverse using explicit local coordinate inverses. `UnitSurgeryTraceBoundary`
gives the compact canonical target and full native boundary splitting.

`RoundedTraceSmoothPieceOutwardNormal` now supplies actual smooth local unit
outward columns. `CoorientedHypersurfaceNormal` proves that normalizing the
projection of a transverse vector depends only on its defining-differential
sign. The actual tangent-kernel and ambient-range comparisons are checked,
as is the smooth normal projection of the native boundary embedding. The
collar's smoothness proof uses fixed transverse variables and a genuine
manifold-parameter derivative, not a globally smooth raw manifold differential.

`RoundedTraceOutwardNormalOverlaps` now compares the actual projected normal
directions on both overlaps, and `RoundedTraceGlobalOutwardNormal` descends
them smoothly. `RoundedTraceInducedBoundaryFrame` proves exact full range.
`RoundedTraceCylinderOutwardNormal` fixes the two endpoint signs, and
`RoundedTraceOriginalFrameStabilization` gives the exact original frame plus
six axes with its explicit, norm-preserving column reordering.

`UnitSurgeryInducedEmbedding` constructs the actual canonical surgery embedding
and proves equality of its tangent image with that of the corresponding native
boundary point. `UnitSurgeryInducedFrame` supplies its full smooth frame and
the exact two end restrictions. `UnitSurgeryInducedPieceFrames` retains the
actual exterior, handle, and collar formulas. `UnitSurgeryNormalFraming` gives
the frame in the new embedding's standard normal model, without changing its
vectors or assigning a new atlas.

The projected unit normal now has the proved negative defining differential
in every actual superlevel piece. `RoundedTraceOutwardTangentSection` lifts
it to a smooth section of the trace tangent bundle along the boundary and
proves genuine boundary transversality. `SmoothImmersionTangentLift` uses
actual tangent trivializations and a local operator left inverse; it does
not assert global smoothness of raw manifold derivative coordinates.
This is intrinsic boundary data for the pending bordism construction.

The global boundary equation and bordism time are now also checked.
`RoundedTraceBoundaryDefiningFunction` glues the actual nonnegative local
equations with a smooth partition of unity. Its zero set is exactly the native
boundary, and its differential is negative on the intrinsic outward vector.
`RoundedTraceEndCutoff` separates the two closed ends. The smooth function
constructed in `RoundedTraceBordismTime` has exactly these zero and one levels
and values in `(0, 1)` exactly on the interior.
`RoundedTraceBordismTimeDifferential` proves regularity and the two outward
signs using actual manifold derivatives. These data still need to be used
in the geometric collapse/bordism comparison; they do not produce a filling.

`RoundedTraceBoundaryTimeKernel` identifies the native boundary tangent image
with both end-time kernels. `RoundedTraceTimeGraph` now embeds the actual
trace as a closed smooth graph in the Euclidean time slab. Normal projections
are smooth for its genuine boundary model by `ImmersionNormalProjection`.
`RoundedTraceTimeGraphNormal` projects the positive time axis and proves it
never vanishes. `RoundedTraceTimeGraphFrame` joins its normalization to the
lifted old trace frame, with exact norm preservation and full normal range.
Its actual smooth range-frame object is checked. The boundary-frame comparison
is now also checked as described below. The actual collapse homotopy is now
constructed, but comparison of its end maps with earlier choices remains open.

`RoundedTraceBoundaryTimeSlope` proves that the actual boundary time covector
is the smooth outward slope times the old unit outward covector.
`RoundedTraceGraphBoundaryColumns` identifies both columns in the plane of
the time axis and the old outward normal, including genuine coorientation.
`RoundedTraceGraphBoundaryFrame` gives a full norm-preserving frame for every
real slope in that plane, always in the actual native boundary normal space.
`RoundedTraceGraphBoundaryFrameHomotopy` reduces the slope to zero by a genuine
continuous-map homotopy and identifies the final frame with the lifted old
induced frame plus the positive time axis. Its coordinate packing preserves
the column order explicitly; no permutation or sign is discarded.

The graph frame's boundary time components are now handled explicitly.
`RoundedTraceVerticalFrame` subtracts a smooth tangential correction, vertical
near both ends, without changing the normal projection. The resulting actual
displacement tube has a uniform closed embedded radius, stays in the slab,
has the exact end preimages, and has invertible differential throughout.
These are checked in `RoundedTraceVerticalTubeRegularity` using the genuine
boundary atlas and unchanged computational limits.

Relative openness is now proved for this actual tube, using the native chart
boundary signs and its time-preserving end neighborhoods.
`RoundedTraceOpenSlabTube` constructs the full open product embedding by
radial compression. `RoundedTraceCollapseHomotopy` constructs a continuous
homotopy on the compactified spatial domain, fixes infinity, and proves that
its zero fibers are exactly the native trace slices. Its endpoint zero fibers
are exactly the surgery and original ends. Smooth inverse regularity at the
boundary is not assumed.

The actual endpoint tube identities are now checked, not just their zero
fibers. Restriction to an exact time slice preserves an open product tube;
base reparametrization leaves its collapse unchanged. This identifies the
end maps with the actual open tubes on the original and canonical surgery
manifolds. The spatial boundary frames are smooth and full; their last
coefficient has the opposite sign to the outward time slope.

A checked frame homotopy normalizes that coefficient without crossing zero.
At the surgery end the result is the canonical induced frame. At the original
end it is the six-axis stabilization with both the last-column reflection
and fixed column permutation explicit. Every homotopy stage is injective
and spans the actual normal space.

The frame normalization now induces actual based collapse homotopies.
The positive ratio of the interpolated last-column scale to its original
scale gives an explicit linear fiber homeomorphism, with jointly continuous
inverse. The open tube over the compact parameter/base product gives a
collapse continuous at infinity. Its initial map is exactly the original
endpoint collapse. The exact fiber derivative is the radius times the
interpolated frame. The two endpoint normalizations concatenate with the
actual trace homotopy to compare the normalized collapses.

The tube-shape comparison is now also checked. Compactness gives `s > 0`
with `s ‖L v‖ ≤ ‖v‖`. The nonnegative quadratic defect
`Q(v) = ‖v‖² - s² ‖L v‖²` supplies the explicit radial deformation
`v ↦ ((1-t)+t*s) L(v / sqrt (1+t*Q(v)))`. It is an actual open embedding
jointly in the parameter and base, with the radial inverse proved explicitly.
After the original radius-`r` compression, its final map is exactly
`L` applied to radius-`r*s` compression. This constructs the actual round
signed-unit-frame tubes and their based collapse homotopies. The two round
endpoint collapses are now compared through the actual trace, and any two
admissible positive radii for the same core/frame give based homotopic collapses.

The selected smooth-collapse data and normal-coordinate comparison are now
checked. `FramedTubeData` retains the actual tube certificate, and the
canonical `framedCollapseData` is now built from it. Its global map and radius
are exactly those of the retained tube. The general `FramedCollapseData`
interface is unchanged; no tube formula is inferred for arbitrary records.
Exact fiber-coordinate equivariance and radial isometry naturality connect
these chosen maps to the round endpoint tubes. The original endpoint has
an actual embedding and signed normal framing in its unchanged atlas.

The constructed trace now gives a based homotopy between the chosen endpoint
maps in their common normal model and on the actual spheres. Relative
smoothing supplies ordinarily homotopic regular representatives, retaining
the exact endpoint fibers and local germs. It does not assert that smoothing
fixes infinity. The next obligations are the general geometric quadratic
refinement, dimension-six framed-bordism detection, an actual filling, and
the seven-dimensional surgery/classification arguments.

The partial normal-frame collar step is now checked. `SmoothDiskCollarFrame`
installs prescribed smooth frame data near the sphere and protects a closed
inner annulus during relative smoothing. `SmoothSphereRadialCollar` computes
the actual radial derivative range throughout the collar, and
`StabilizedDiskRadialNormal` proves that the prescribed normal columns remain
normal there. `DiskData.exists_normalFrame_collar`
replaces the normal extension while retaining its exact radial collar values.
The candidate-specific product theorem now includes this annulus explicitly.

The complementary three-frame is now also exactly radial on a smaller common
annulus. `SpanningDiskRadialComplement` and `ManifoldRadialComplement` prove the
actual combined-operator range comparison. `SmoothFullDiskCollarFrame` retains
full range during smoothing. `FramedProductCollarReplacement` rebuilds the
embedded product with precisely that frame and unchanged boundary columns.

`FramedDiskRadialCollar` proves the exact collar formula for every transverse
vector: the original ambient tube, normal height, and zero graph coordinates.
This gives interior collar avoidance for every transverse vector. On the
remaining compact inner subdisk, `CompactThickeningAvoidance` supplies a
uniform radius. `FramedDiskInteriorAvoidance` thus proves avoidance for the
whole open-disk product. `exists_radialAttachingData` constructs a common
positive radius for this product and the original-atlas attaching neighborhood.

The curved-face map correction is now checked. `SphereTubeDifference` proves
that the actual curved-minus-affine difference has zero core value and native
derivative. The radial pullback and outer cutoff are smooth, including at the
disk center, in `RadialCollarCorrection` and `RadialCollarCorrectionJet`.
`CurvedDiskProduct` preserves the actual core, derivative, and interior
avoidance. `CurvedDiskCollar` proves the exact whole-face and outer-collar
formulas. `EmbeddedCurvedDiskProduct` proves smaller-radius embedding and
immersion. `FramedCurvedDiskProduct` constructs a full normal frame retaining
the core values, and `exists_curvedAttachingProduct` assembles the actual
candidate data and original-atlas tube at a common radius.

The whole-collar framing step is now checked. `ClosedDiskCollarDerivative`
uses uniqueness of within-derivatives to compare actual derivatives on the
closed disk. `PrescribedCollarNormalFrame` supplies the original manifold
normal frame at the actual tube point, plus five graph axes, and proves its
normality. A global smooth extension and interpolation near the annular zero
section install it on a smaller whole collar. Relative smoothing in the
actual normal projections retains these prescribed values. Inner core values
may change; no equality with the old inner core frame is claimed.

`EuclideanEmbedding.nonempty_framedAttachingProduct` assembles
the actual embedded handle, original-atlas tube, whole-collar map and frame
equalities, and interior avoidance. This is attaching data, not a trace.

The compact unrounded attachment is now checked. `ManifoldHeightCylinder`
constructs the original cylinder in the same stabilized ambient space.
`AttachingCylinderIntersection` combines compact separation on an inner
subdisk with the signed-height collar formula to prove exact intersection
at the attaching face. Old height-zero ambient avoidance is not being used
as a substitute for cylinder avoidance.

`UnroundedSurgeryTrace` uses half the transverse radius, proves compactness
of the actual ambient union, and identifies its closed-attachment quotient.
`SmoothManifoldHeightCylinder` computes the actual native derivative and full
normal space. `UnroundedTraceFrame` descends the matching frames to a continuous
norm-preserving ambient field with exactly the correct normal range on each
piece. This does not assert a smooth boundary for the unrounded union.

The smooth collar sheet and supported rounding are now checked.
`RadialHeightCoordinates` gives the actual radius-height inverse pair.
`InjectiveLocalDiffeomorph` and `AttachingTubeCoordinates` provide the smooth
inverse of the original open tube. `AttachingCollarCoordinates` preserves
both actual map and frame formulas across the collar. `AttachingCollarSheet`
proves that the resulting sheet is embedded, smoothly immersed, and normally
framed with the exact actual derivative range.

`UnroundedCornerModel` identifies the original domain in a uniform band as
`t ≥ 0` or `‖v‖ ≤ r`, where `r` is the half-radius handle. For a constructed
bump `χ`, `SmoothCornerRounding` uses
`φ(u) = sqrt (u² + (χ.rIn * χ(u))²)` and `F(t,q) = t+q+φ(t-q)`.
The actual derivative of `F` on `(1,1)` is two. Outside the bump interval,
the original absolute value is retained. Added points are confined to a
bounded negative corner. `RoundedHandleCorner` substitutes `q = r²-‖v‖²`
and proves regularity at every zero without a derivative assumption.

`AttachingRoundingData` obtains the height band, bump, and radial bound from
the existing candidate data. `RoundedSurgeryTrace` adds a compact parameter
region in the actual sheet, proves compactness, proves the exact local
superlevel membership criterion, and leaves all positive-height points
unchanged. It does not assert a global boundary atlas or a framed bordism.

The actual open collar is now checked. `RoundedTraceInnerImage` and
`RoundedCylinderCoordinates` use the complement of the compact inner image
and the full cylinder embedding to obtain genuine relatively open coordinates.
`RoundedCollarHomeomorph` identifies the actual collar with its parameter
superlevel and proves that it contains every added point.

`SuperlevelNormalForm` constructs a boundary atlas from regularity at zero
without a new atlas assumption. Its boundary is exactly the zero set, its
inclusion is smooth with bijective differential, and its smooth-map criterion
uses the original ambient atlas. `RoundedCollarLevel` proves the required
native differential is surjective for the actual collar function.
`RoundedCollarAtlas` and `RoundedCollarDifferential` then give the concrete
open piece its boundary atlas, smooth immersive inclusion, and full smooth
normal frame.

The global assembly is now checked. `RoundedTraceOpenCover` removes the
other compact pieces to obtain the unchanged cylinder and handle regions.
Their exact open-window coordinates and regular superlevel atlases use the
same half-space model. `RoundedTraceCoordinateChanges` proves the actual
parameter identities on each overlap, and `RoundedTraceOverlaps` proves
smoothness in both directions. `RoundedTraceAtlas` applies `SmoothOpenCover`.

`RoundedTraceBoundary` identifies the whole native boundary as the union of
the three explicit local boundary sets. `RoundedTracePieceFrames` proves
exact frame agreement, `RoundedTraceSmoothFrame` gives smooth descent, and
`RoundedTraceDifferential` compares actual tangent images. Finally,
`RoundedTraceNormalFrame` identifies the full global normal range.

Next, identify the original positive-height end and the surgered end as
smooth boundary components, including their induced normal framings and the
outward height direction. The exact boundary-set formula alone is not a
boundary diffeomorphism or the required surgery/bordism theorem.

No framed-nullbordism, surgery, or h-cobordism theorem is postulated.
Stable normal framing is not being treated as framed nullbordism.
