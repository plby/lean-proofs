# Even boundary count: verified construction

The compact half-line-atlas even-boundary theorem is now **proved in Lean**.
It now applies to the actual manifold-valued perturbation as well as the earlier
Euclidean family. The manifold existence theorem chooses the generic parameter
and constructs compactness; the original exterior slices must be injective and
immersive. The six-sphere classification remains unproved.

## Checked geometric input

The actual unordered double-point quotient has a Hausdorff, second-countable
half-line atlas. In every selected chart, zero is exactly the actual diagonal
orbit boundary. This boundary is closed and discrete, and in bijection with
the original singular parameter set. In the manifold construction,
`CompactSphereDoublePoints` constructs the compact container,
`ManifoldAffineUnorderedAtlas` constructs the genuine atlas, and
`ManifoldAffineSingularBoundary` proves the intrinsic singular-boundary bijection.

For any compact space with such a half-line atlas, there is a finite cover by
actual compact interval neighborhoods. Their two distinct endpoint images
give a finite cut set `S` containing the boundary and all cover-region frontiers.
The type of each cut component uses the original complement subtype topology.

`cutComponent S x` is its actual image in the original space. Components are
open, their frontiers lie in `S`, and each closure stays in one selected chart.
The actual chart followed by the real subtype inclusion gives a homeomorphism
of every component closure with some nondegenerate real interval `[a,b]`.
`FamilyEmbedding.exists_finite_cuts_with_interval_components` in
`GenericFamilyFiniteCuts.lean` specializes this to the original quotient.

## Checked endpoint and incidence argument

1. `CutCurveEndpointCuts` proves that both interval endpoint images lie in `S`.
   If an endpoint were
   outside `S`, it would belong to the open component. An open half-line region
   cannot attain a maximum, or a positive minimum. A minimum at zero is already
   in the boundary and hence in `S`. The proof uses the exact coordinate
   identity in the interval homeomorphism.
2. `CutCurveOpenInterval` proves that the original component is exactly `(a,b)` and that
   the closure adds only these two endpoints. Connectedness and density of the
   component in its closure, together with the actual coordinate, exclude
   missing interior points. The known endpoints are excluded by `C ⊆ Sᶜ`.
3. `SmallCurveCutNeighborhood` shrinks an original chart to exclude all other cuts. Its
   punctured neighborhood has one component at boundary points and two at
   interior points. `CurveBranchComponentComparison` identifies these branches
   with global component incidences. An edge whose closure meets the cut enters one
   of these branches; a branch lies in only one global component.
4. `FiniteCurveEdges` proves the edge set finite from the finite cuts and their
   finite incident branches. The actual incidence count gives two distinct
   ends per edge, degree two at each interior cut, and degree one at each actual
   boundary point. `CurveIntervalEndpointInterior` excludes an interior cut
   from the interior of a component closure; this prevents its two branches
   from belonging to the same edge. `CurveCutIncidenceDegrees` proves the
   exact degrees. `FiniteIncidenceParity` and `CompactCurveBoundaryEven` prove
   evenness by double counting. Edges are actual component subsets, so parallel
   edges are not collapsed.
5. `CurveDecomposition.finite_even_boundary_of_compact_atlas` in
   `CompactHalfLineBoundary.lean` constructs the finite cover and all subsequent data
   from compactness and the atlas. No decomposition or endpoint pairing is an
   input. `FamilyEmbedding.finite_even_singular_parameters` in
   `GenericFamilyEvenSingularCount.lean` applies the singular-boundary bijection
   to the original Euclidean family and proves its actual singular set finite
   with even cardinality.

## Checked manifold application and remaining scope

Endpoint-relative Euclidean genericity is now checked: `RelativeThreeSixFamily`
uses one arbitrarily small cutoff perturbation for spatial jets and double
points and fixes all exterior-time maps. `RelativeThreeSixGlobal` extends the
genericity to all times if those unchanged exterior slices are injective and
immersive. The subsequent `ManifoldAffineGenericParameter` construction now
chooses one arbitrarily small generic parameter on genuine finite chart covers
in the original manifold. `CompactSphereDoublePoints` constructs the needed
compact container when the unchanged exterior slices are injective.

The local curve atlas and singular-boundary correspondence are now transferred
to the actual manifold quotient. `ManifoldAffineEvenSingularCount` proves its
finite even intrinsic singularity count and chooses one arbitrarily small
perturbation satisfying it. Evenness alone does not prove the requested sphere
classification. Homology descent of the geometric parity,
dimension-six framed-bordism detection, and surgery remain unproved.
The actual manifold local parity-one balls are now constructed in
`ManifoldAffineLocalContribution`. The global homology relation combining those
contributions remains to be proved. `InjectiveOperatorVaryingCoordinates` handles
changes extending over the four-ball, and `ManifoldChartLinkParity` constructs
the actual overlap comparison when both chart pairs cover the whole ball.
Neither result supplies the global geometric-parity relation.

The local construction now retains genuine partial-diffeomorphism charts and
can be confined to any prescribed neighborhood. `ManifoldParityBallSystem`
uses the finite actual singular set to choose disjoint closed balls.
`ManifoldAffineParityBallSystem` assembles this with the small generic family
and even count. `ManifoldPuncturedCylinder` proves that the actual complement
is compact and singularity-free, with frontier precisely the endpoint spheres
and linking spheres. The global homology boundary relation is now proved below;
the geometric-parity comparison is still unproved.

`ManifoldPuncturedBoundaryMaps` further identifies the actual frontier with
the finite disjoint union of its parametrized spheres and constructs their
continuous inclusions into the actual punctured cylinder. This supplies the
maps for the homology relation, which is proved by the later construction below.

`ManifoldPuncturedRetraction` now retracts the actual regular parameter space
onto this cylinder, fixing it pointwise and proving homology injectivity.
`ManifoldPuncturedBallHomotopy` identifies the local half-radius sphere map
with the actual linking map on homology. The global relation is now proved by
the construction described in `PuncturedHomologyPlan.md`.

The actual overlap decompositions and comparison-coordinate maps are now checked
in `ManifoldSpherePunctureCoordinates`. Every global connecting coordinate is
an actual isomorphism, and their inclusions into the complement sum to zero.
`ManifoldSphereBoundaryRelation` now assembles the actual sphere models, their
boundary comparisons, and unit coefficients into the signed boundary-map relation.
`ManifoldSphereBoundaryParity` applies it to any continuous frame map.
`ManifoldFamilyGlobalFrame` now constructs the relevant frame map from the
original derivative and normal framing, and `ManifoldFamilyFrameBoundary`
applies the sum-zero relation to it. `ManifoldFamilyLinkParity` now proves
every local linking value is one and hence the even-count endpoint equality.
`ManifoldAffineFrameBoundary` supplies all small-family and local data.
`ManifoldFamilyEndpointHomotopy` now proves the geometric normal-disk endpoint
comparison via actual operator homotopy and the common source twist.

The actual four-sphere cover, its neighborhood homology vanishing, the one-point
connecting isomorphisms, and the global naturality comparison are now checked
in `ManifoldSpherePunctureConnecting`. The intersection coordinates and
unit-coefficient calculation are now supplied by the later modules above.
