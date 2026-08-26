import ErdosProblems.Erdos633.Arithmetic
import ErdosProblems.Erdos633.AngleCounting
import ErdosProblems.Erdos633.Area
import ErdosProblems.Erdos633.Isosceles
import ErdosProblems.Erdos633.Refinement
import ErdosProblems.Erdos633.CommonRefinement
import ErdosProblems.Erdos633.VTiling
import ErdosProblems.Erdos633.UTiling
import ErdosProblems.Erdos633.RightCriteria
import ErdosProblems.Erdos633.GroupOneCriteria
import ErdosProblems.Erdos633.OneTwentyCriteria
import ErdosProblems.Erdos633.WTiling
import ErdosProblems.Erdos633.ZTiling
import ErdosProblems.Erdos633.UTwoTiling
import ErdosProblems.Erdos633.BoundarySigns
import ErdosProblems.Erdos633.SixtyTrigonometry
import ErdosProblems.Erdos633.OneTwentyAngleCriteria
import ErdosProblems.Erdos633.Sufficiency
import ErdosProblems.Erdos633.ActualAngleCounting
import ErdosProblems.Erdos633.ActualAngleClassification
import ErdosProblems.Erdos633.BoundarySideCounts
import ErdosProblems.Erdos633.BoundaryLongestEdge
import ErdosProblems.Erdos633.CharacterBoundary
import ErdosProblems.Erdos633.ExceptionalNecessity
import ErdosProblems.Erdos633.ActualRightReptileNecessity
import ErdosProblems.Erdos633.IrrationalReptileNecessity
import ErdosProblems.Erdos633.RationalConjugateObstructions
import ErdosProblems.Erdos633.RationalReptileNecessity
import ErdosProblems.Erdos633.FieldCoordinateMap
import ErdosProblems.Erdos633.RealCoordinateField
import ErdosProblems.Erdos633.CrossingDissection
import ErdosProblems.Erdos633.IntervalChain
import ErdosProblems.Erdos633.ActualFieldConjugation
import ErdosProblems.Erdos633.ConjugateCornerAngles
import ErdosProblems.Erdos633.CyclotomicTilingAngles
import ErdosProblems.Erdos633.Classification

/-!
# Erdős problem 633: complete unconditional classification

The problem asks which triangles admit only square numbers of congruent tiles.
The theorem `Erdos633.erdos_633` proves that these are exactly the triangles
outside the eight explicit families in `HasListedNonsquareShape`.
Equivalently, `Triangle.admitsNonsquareTiling_iff_listed` classifies all
triangles admitting a nonsquare congruent tiling. The development proves:

* a geometric definition of nondegenerate triangles and congruent tilings;
* transport of actual tilings under similarities and changes of vertex labels;
* a genuine two-piece congruent tiling of every isosceles triangle, without
  coordinate, orientation, or scale restrictions;
* positivity and finiteness of triangle area, and area additivity for tilings,
  with no edge-to-edge assumption;
* refinement of dissections with arbitrary parent shapes and varying tile
  counts, and composition of congruent tilings with multiplicative counts;
* the absolute-determinant formula for area under arbitrary affine equivalences;
* the general `n²`-piece congruent subdivision of every triangle for every positive `n`;
* common congruent refinement of any finite dissection into positive rational
  multiples of one triangle, allowing ambient reflections and exhibiting the count;
* ambient triangle congruence from the three squared side lengths;
* the four-region exceptional V construction, including exact coverage,
  pairwise interior disjointness, all piece congruences, and a parallelogram grid;
* actual V-family tilings with `d²(2d²-u²)` pieces for the parameter `s = u/d`,
  and nonsquare tilings whenever `2-s²` is not a rational square;
* a sufficient side-length criterion covering every position, orientation, and
  positive scale of this V family, with explicit 28- and 1225-tile examples;
* general vertex-to-side splitting with certified coverage, disjoint interiors,
  and gluing of component congruent tilings;
* actual U-family tilings with `(2d²-u²)(3d²-u²)` pieces, their nonsquareness for
  every rational parameter in `(0,1)`, a side criterion, and a 77-tile example;
* actual right-triangle tilings with `m²+n²` pieces, and the nonsquare sufficient
  condition stated directly with a right angle and integer leg ratio `m/n`;
* an actual three-piece tiling of the 30-60-90 triangle, transported to arbitrary
  triangles with a right angle and a 60-degree angle;
* positivity and the angle sum for the actual Euclidean angles of every triangle,
  sine-rule side ratios, and the equal-angle sufficient condition;
* the U sufficient condition directly from `B = 2A` and rational `sin(A/2)`;
* the V sufficient condition directly from `C = A/2+B` and
  `2 sin(A/4) = u/d`, with the exact nonsquare test `2d²-u²`;
* the three-piece 120-degree trapezoid template, its common congruent refinement,
  appended parallelogram grids, row assembly, and three rotated trapezoids;
* an actual equilateral tiling for every positive integer solution of
  `c² = a²+ab+b²`, with exactly `9c⁴(ab)³` congruent tiles of scale `1/(ab)`;
* the Euclidean 120-degree angle of the constructed tile, the equal side lengths
  of the outer triangle, the exact square test for this count, and a `3,5,7` example;
* the W-family split into an equilateral triangle and the reference triangle,
  actual tilings with `9c⁴a²b³(a+b)` pieces, the square test `b(a+b)`, and a sufficient
  side criterion under its nonsquareness, including the triangle with sides `3,7,8`;
* the Y-family split into reference and scaled W pieces, with count
  `9c⁴a²b²(a+b)(2a+b)` and exact square test `(a+b)(2a+b)`;
* the Z-family split into scaled W and Y pieces, with count
  `9c⁴a²b²(a+b)²(2a+b)(a+2b)` and exact square test `(2a+b)(a+2b)`;
* unconditional nonsquareness of that Z test, by descent modulo three without
  a primitivity assumption, and the resulting unconditional Z side criterion;
* unconditional nonsquareness of the W test, by descent for Pythagorean pairs
  with one doubled leg, and the resulting unconditional W side criterion;
* the full fourth-family sufficient condition from an actual 60-degree angle
  and rational `sqrt(3) * tan(A/2)`, with no separate nonsquareness input;
* unrestricted sufficient side criteria for Y and Z, with no separate nonsquare
  input, and checked concrete tilings from the `3,5,7` reference triangle;
* the U₂-family split into reference and scaled Z pieces, with count
  `27c⁴a²b²(a+b)³(a+2b)`, exact square test `3(a+b)(a+2b)`, and a sufficient
  unconditional side criterion and a concrete example;
* the two Euler quadratic descents, including all coprimality, sign, and
  divisibility conditions and the unique exceptional solution for the minus sign;
* the rational cubic obstructions: `y² = x³+1` forces `x = -1, 0, 2`, and
  `y² = x³-1` forces `(x,y) = (1,0)`;
* unconditional nonsquareness of the Y and U₂ tests through explicitly checked
  rational maps to those cubics, without elliptic-curve assumptions;
* the full fifth and eighth sufficient conditions from the actual Euclidean
  angle relations and rational `sqrt(3) * tan(A/2)`, without coordinate inputs;
* the complete sufficient direction of the eight-family classification, collected
  as `Triangle.admitsNonsquareTiling_of_listed_shape` and allowing vertex relabelling;
* actual labelled tile corners, outer-corner incidence, and conservation of every
  corner label across the finite geometric dissection;
* intrinsic local cones, their exact partition by incident tiles, null boundaries,
  and area additivity for their intersections with a unit disk;
* the unit circular-sector area formula from polar change of variables, and its
  identification with half the Euclidean angle at every triangle vertex;
* the outer-corner angle equations using actual tile counts, including reflected
  tiles and arbitrary partial edge contacts;
* the full local angle ledger: every nonouter dissection vertex has corner-angle
  sum pi or twice pi, and at most one tile passes through it along an open edge;
* the global identity that the nonouter local angle multipliers sum to `N - 1`,
  stated without truncated subtraction as `sum + 1 = N`;
* the coefficient bounds `p,q <= 2` for actual tilings under the precise angle
  independence and outer-count hypotheses, and the resulting missing-angle
  outer-count bounds by three;
* the single-type outer-corner case: the outer angles are all `pi / 3`;
* the all-positive outer-count case: the outer angles are a permutation of the
  reference angles;
* exhaustive classification of the seventeen sorted, distinct coefficient-row
  triples, with reduction to matching reference angles or the six exceptional
  outer-angle families;
* full irrational-angle necessity in actual Euclidean angles, including all
  reference-label permutations and the isosceles alternative, with independence
  derived from noncommensurability rather than assumed;
* arbitrary vertex relabelling with carrier and corner-angle preservation,
  geometric AA similarity allowing reflections, and the resulting actual
  isosceles/similar/exceptional shape alternatives for irrational-angle tiles;
* the identity that a geometric reptiling's positive similarity scale has square
  equal to its tile count, derived from actual area additivity;
* labelled closed edges as barycentric supporting faces, and the fact that an
  open tile-edge point on an outer side forces the full tile edge onto that side;
* uniqueness of the incident boundary tile away from the finite vertex set,
  derived from the local-sector area ledger;
* full boundary-edge coverage and disjointness away from finitely many vertices,
  followed by exact side-length additivity using one-dimensional Hausdorff measure;
* nonnegative integer boundary-side counts for every actual congruent tiling,
  and the nonnegative integer eigenvalue equation for the reptile angle case;
* the finite marked-interval obstruction, transported to planar segments with
  finite exceptional vertices and finite pairwise edge intersections;
* positive counts of edges opposite an obtuse tile angle on every outer side,
  whenever that angle is absent from the outer corners, with no boundary-count
  or edge-to-edge hypothesis;
* the positive longest-edge counts required by the V and W rationality arguments,
  derived directly from their actual Euclidean angle patterns;
* exact one-tile boundary incidence and two-tile interior-edge incidence away
  from the finite vertex set, with unique open-edge labels;
* common supporting lines and opposite inward half-planes at shared open edges,
  and cancellation of their counterclockwise unit directions;
* full signed-boundary additivity for every odd function on directions, obtained
  by integrating the pointwise cancellation against Hausdorff length measure;
* global angle-coordinate characters extended by zero, avoiding any need to
  assume or prove that all tile orientations belong to the generated subgroup;
* the integer boundary-sign identities extracted from actual congruent tilings
  and actual Euclidean angle coordinates, including arbitrary reflections;
* intrinsic normalized sides, a uniform sine-rule scale, and homogeneous
  normalized integer boundary equations extracted from actual tilings;
* the determinant formula for triangle coordinates, its transport through an
  isometric upper-half-plane model, and geometric side-and-sine area equations;
* the real side parameters and normalized outer side formulas in all six
  exceptional families, with no rationality or side equation assumed;
* commensurability of the reference and outer sides for every irrational-angle,
  non-isosceles, nonreptile congruent tiling, derived from the two characters,
  actual area additivity, and the actual positive boundary-edge counts;
* rational group-one scales and exact area equations from actual U and V tilings,
  and the necessary V integer test with the correct parameter `2 sin(A/4)`;
* reference relabelling with rebuilt congruence witnesses, and invariance of
  angle and side commensurability under arbitrary vertex permutations;
* the complete necessary direction for irrational-angle nonreptile nonsquare
  tilings, yielding the same eight-family predicate used by sufficiency;
* the negative similarity eigenvalue for every nonsquare geometric reptiling
  with matching angle labels, derived from the rational cubic determinant;
* propagation and sign reversal of maximal absolute eigenvector ratios across
  positive boundary-matrix entries, forcing two zero diagonal entries;
* closed boundary-edge coverage including all endpoints, and the two distinct
  adjacent boundary edges at every outer corner occupied by a single tile;
* the unsplit acute corners of irrational right reptilings and their actual
  side-label matching alternatives, with no assumed matrix-incidence data;
* the star form of the boundary matrix and exact necessity `N = p²+q²` with
  positive natural `p,q` and outer leg ratio `p/q` for irrational right reptilings;
* the complete necessary eight-family condition for every nonsquare tiling by
  an irrational-angle right tile, including all vertex labels and nonreptilings;
* equality of the chosen labelled isometries under reference-carrier equality,
  and transport of actual corner counts under outer and reference relabelling;
* the three-corner obstruction to nonsquare reptilings, using a triangle of
  boundary-matrix sign reversals instead of a checkerboard-coloring argument;
* the signed-boundary square-count obstruction for every aligned reptiling
  with a direction character that sends pi to minus one;
* the right-angle consequence of a missing outer label in every irrational
  nonsquare reptiling, from the actual count bound and character parity;
* the complete necessary eight-family condition for every nonsquare tiling
  with irrational reference angles, including nonright reptilings;
* preservation of commensurable angles from the tile to the outer triangle,
  and the full classification equivalence for every irrational-angle outer triangle;
* explicit coprime residues in the middle third, the denominator restrictions
  `4,6,10`, and the multiplicity bound by five for conjugate-angle inequalities;
* the five rational conjugate-angle obstructions, including the exhaustive
  three-two and five-two arithmetic exclusions, without assuming geometric conjugation;
* membership of every nonsquare reptile side ratio in any subfield containing
  its similarity scale, including the zero-minor boundary-matrix case;
* the quadratic field-degree bound for the similarity scale and all actual
  reptile angle cosines, derived from boundary counts and the cosine rule;
* the degree-four bound for the complex exponential of any quadratic cosine,
  and the resulting totient bound for a rational rotation denominator;
* the complete list of positive orders with totient at most four, proved by
  prime-divisor induction and kernel-checked finite cases;
* the eleven possible rational angles with quadratic cosines, and the fact
  that a scalene triangle with such angles must be a 30-60-90 triangle;
* complete necessary eight-family classification for every nonsquare reptiling,
  with no rational-angle or irrational-angle restriction on the reference tile;
* the remaining-case reduction: any nonsquare tiling outside the listed families
  must use rational-angle tiles not similar to the outer triangle;
* a linear functional simultaneously nonzero on finitely many nonzero vectors
  over an infinite field, using finite avoidance in the algebraic dual;
* a linear retraction of any infinite-field extension that fixes the base field
  and is injective on any prescribed finite set, without a density argument;
* coordinatewise real-subfield maps preserving supporting-line incidence,
  conjugation, coefficient-field edge vectors, and finite point distinctness;
* weighted boundary-area identities and propagation from boundary tiles across
  shared open edges, without an assumed adjacency-connectivity theorem;
* coefficient-field membership of every labelled unit direction and edge vector,
  derived from the outer base direction, tile rotations, and actual boundary counts;
* the exact directed crossing indicator of a triangle away from finitely many
  exceptional lines, including arbitrary vertex orientations;
* recovery of full coverage and pairwise disjoint interiors from an almost-everywhere
  oriented crossing identity, rather than merely an area identity;
* finite interval endpoint balance and cancellation against arbitrary endpoint
  potentials, with no continuity or order-preservation hypothesis;
* supporting-line cancellation and the full directed-edge boundary identity
  extracted from every actual dissection, including partial edge contacts;
* geometric transport through maps preserving marked edge lines, when all
  orientations change by one common sign;
* actual coefficient-field realizations by translated congruent tiles, with
  coverage and disjoint interiors proved from crossing cancellation;
* original-coordinate rigidity: boundedness of every field-retracted tiling
  forces all original tiling vertices into the coefficient field;
* preservation of supporting lines, squared distances, and signed area relations
  under arbitrary real field embeddings, with a common orientation change;
* actual conjugate congruent tilings constructed from the original isometries,
  retaining the tile count and injective labelled vertex images;
* invariance of every labelled outer-corner incidence count under field embeddings;
* sector and angle equations for explicitly labelled dissections, without choosing
  new congruence witnesses or permuting the retained labels;
* the full outer-angle equation after every real field embedding, using the actual
  corner counts of the original congruent tiling, and its strict multiplicity bound;
* transport of squared angle cosines as rational expressions in squared side
  lengths, with no unsupported positivity assumption on conjugated lengths;
* uniqueness of the three labelled triangle angles from their cosine squares,
  positivity, and angle sum, including all supplement choices;
* the explicit fractional-residue formula for conjugate angles, with positive
  residues and their sum of one or two proved from coprime denominator data;
* construction of embeddings sending a primitive complex root to each coprime
  power, and restriction to a real coefficient field by conjugation invariance;
* coefficient-field membership of integer-multiple sines and cosines, and the
  exact action of the constructed real embeddings on those cosines;
* the rational conjugate-corner identity for geometrically normalized tilings,
  with embeddings, denominator data, field-valued tile vertices, and preservation
  of the original corner counts derived rather than assumed;
* geometric normalization of every rational-angle tiling, preserving both angle
  triples and supplying actual corner data satisfying every conjugate equation;
* lifting every reduced angle residue to a unit of the common cyclotomic modulus,
  the four repeated-angle candidates, and the multiplicity bound by five;
* all single-type and two-type rational corner partitions, including the five
  exceptional conjugate contradictions and the 30-60-90 alternative;
* the full rational-angle tiling necessity, and the unrestricted equivalence
  between nonsquare congruent tilability and the eight listed families;
* the square-only formulation `erdos_633`, with no angle, side, normalization,
  field, or edge-to-edge restriction on the triangle or its tilings;
* invariance of rational square class under a nonzero rational square scale;
* the nonsquare obstruction `(2-s²)(3-s²)` for every rational `0 ≤ s < 1`;
* the exact `2*v²-u²` square criterion for the other group-one area equation;
* the finite angle-counting obstruction bounding the two relation coefficients;
* direction-sign invariance under full turns, both tile handednesses, and finite
  internal-edge cancellation;
* all six algebraic rationality consequences of the two boundary-sign identities,
  with the required area and boundary-count data stated explicitly;
* the square-count consequence of an explicit reptile signed-boundary identity.

All results are proved from Mathlib, without added axioms, admitted proofs, or
increased computational limits. In particular, an area equation for an actual
tiling is derived, not postulated in the definition of a tiling.

The complete classification includes irrational-angle tiles, rational-angle
tiles, all reptilings, and nonreptile tilings. Both necessity and actual tiling
constructions are unconditional. The formal definitions permit reflections and
partial edge contacts and require coverage of the entire closed triangle and
pairwise disjoint tile interiors. Every geometric conjugation and corner count
used in the rational-angle branch is derived from these definitions.
-/
