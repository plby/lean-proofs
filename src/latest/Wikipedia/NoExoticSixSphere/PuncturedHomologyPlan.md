# Actual boundary homology relation: verified

The checked result is an integral homology relation among the actual maps
`ParityBallSystem.sphereInclusion`, with coefficient `1` or `-1` for every
endpoint and linking sphere. `ManifoldSphereBoundaryRelation` proves the
relation for every third homology class and as an equality of induced maps.
The six-sphere theorem remains unproved.

## Checked inputs

The ball system is constructed from the actual small generic family. Its
closed regions are pairwise disjoint. The actual punctured cylinder is compact
and nonsingular, and its frontier is parametrized by the finite disjoint union
of the original endpoint spheres and one linking sphere per actual singularity.

`ManifoldPuncturedRetraction` constructs a continuous retraction from
`RegularParameters g`, the complement of the actual singular points in
`ℝ × Sphere 3`, onto the punctured cylinder. It fixes the entire cylinder.
Consequently the actual inclusion is injective on integral homology in every
degree. No homotopy-equivalence claim is needed or asserted for this retraction.

`ManifoldPuncturedBall.puncturedSphereEquiv` identifies the actual punctured open
ball with the three-sphere up to homotopy, using the half-radius sphere as
inverse. `ManifoldPuncturedBallHomotopy.smallLinkHomotopy` expands that sphere
to the actual linking sphere through the regular parameter space. The induced
homology maps are equal.

## Construction status

1. **Checked.** `SphereCylinder.chart 3` identifies time times the three-sphere
   with the four-sphere minus its two poles. `SphereCylinderPunctures` constructs
   the complement homeomorphism after adding the actual singular point images.
   `ManifoldSpherePunctureCover.sphereRegularHomeomorph` specializes it to the
   actual `RegularParameters g`.
2. **Checked.** The lower cap has negative head coordinate, and the upper cap
   has head greater than tail norm. `ManifoldSpherePunctureCover` builds `V`
   from these caps and actual disjoint ball interiors and proves `U ∪ V = S⁴`.
   `ManifoldSpherePunctureHomology` proves positive homology vanishing through
   the actual coproduct and component contractions.
3. **Checked.** `ManifoldSpherePunctureOverlaps` identifies `U ∩ V` with the
   actual coproduct of punctured pieces. `SphereCylinderPuncturedCaps` constructs
   the actual exterior-slice sphere models, and `ManifoldSpherePunctureModels`
   transports them and the original punctured-ball models to those components.
   `ManifoldSphereBoundaryComparison` gives genuine homotopies from these
   model sphere maps to the original endpoint and linking sphere maps.
4. **Checked, including unit coefficients.**
   `sum_componentConnectingEquiv_inclusion_zero` proves that the actual
   component isomorphisms sum to zero after inclusion into `H₃(U)`.
   `ManifoldSphereBoundaryCoefficients` uses the proved sphere homology markings
   to obtain actual integer automorphisms, so each coefficient is `1` or `-1`.
5. **Checked, including coordinate projection.**
   For each `cᵢ ∈ C`, use the comparison cover `(Uᵢ, V)`, where
   `Uᵢ = S⁴ \ {cᵢ}` and **the same entire set `V` is retained**. The inclusions
   `U ⊆ Uᵢ` and `V ⊆ V` give actual cover naturality. Stereographic coordinates
   make `Uᵢ` contractible. `singleConnectingEquiv` is the actual isomorphism,
   and `globalConnectingMap_to_single` is the proved naturality comparison.
   `ManifoldSpherePunctureOverlaps` identifies `Uᵢ ∩ V` as one punctured
   component and the other unpunctured components.
   `singleOverlapCoordinateEquiv_comparison` proves the actual coordinate
   projection formula. `componentConnectingEquiv_apply` then proves that
   every global connecting coordinate is an isomorphism. The actual sphere
   model comparison and unit-coefficient conclusion are now checked as well.
6. **Checked assembly.** `ManifoldSphereBoundaryRelation` transfers the relation
   through the actual regular-parameter homeomorphism, uses the homotopies to
   the actual boundary maps, and uses homology injectivity of the original
   punctured-cylinder inclusion. Every original boundary map occurs.

The relation is proved for every class of `H₃(S³)`, then applied to
`Stiefel.sphereThirdClass`. The proof uses only the established integral sphere
markings and does not require that this particular named cube cycle is primitive.
No such primitivity result is assumed or presently proved here.

`ManifoldSphereBoundaryParity` gives the unsigned mod-two relation for any
continuous partial-frame map on the actual cylinder. For a map whose linking
obstructions are all one, evenness of the actual singularity count implies
equality of endpoint obstructions. `ManifoldFamilyGlobalFrame` now constructs the
global map from the original family and given normal framing.
`ManifoldFamilyLinkParity` now proves all actual local values are one and gives
the even-count equality of constructed endpoint obstructions.
`ManifoldFamilyEndpointHomotopy` now derives an actual operator homotopy and
equal geometric normal-disk parity through the common source twist.

The cover comparison in step 5 must not replace `V` by a single small ball:
the other components of `V` would no longer map into that target cover piece.
This checked route does not require a four-dimensional smooth Schoenflies
theorem or an unproved general fundamental-class theorem for manifolds with boundary.

Useful existing APIs include `SingularMayerVietoris.connectingHomomorphism`,
`connectingHomomorphism_naturality`, `exact_at_ambient`, `exact_at_intersection`,
and `ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv` with its actual
component-inclusion and map-out formulas. All geometric hypotheses above must
be discharged for the original spaces. The global frame map and local comparison
and the geometric sphere-parity comparison are now checked. Framed-bordism
detection and surgery remain unproved.
