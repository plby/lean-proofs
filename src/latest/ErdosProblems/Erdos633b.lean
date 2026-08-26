import ErdosProblems.Erdos633b.Classification
import ErdosProblems.Erdos633b.FiniteOuterExhaustion
import ErdosProblems.Erdos633b.ActualFiniteAngleCandidates
import ErdosProblems.Erdos633b.GroupTwoFourthUnconditional
import ErdosProblems.Erdos633b.GroupTwoResidueExclusions1
import ErdosProblems.Erdos633b.GroupTwoResidueExclusions2
import ErdosProblems.Erdos633b.GroupTwoResidueExclusions3
import ErdosProblems.Erdos633b.Boundary48Exclusion
import ErdosProblems.Erdos633b.RationalPositiveSineParity
import ErdosProblems.Erdos633b.FiniteAngleCounterexamples
import ErdosProblems.Erdos633b.FiniteOrTwoPiThirds
import ErdosProblems.Erdos633b.LargeMiddleNecessity
import ErdosProblems.Erdos633b.CaseSevenUnconditional
import ErdosProblems.Erdos633b.NonrightLocalRelations
import ErdosProblems.Erdos633b.TilingResidueCondition
import ErdosProblems.Erdos633b.ConjugateBoundarySigns
import ErdosProblems.Erdos633b.IsoscelesTileNecessity
import ErdosProblems.Erdos633b.IrregularTriangle
import ErdosProblems.Erdos633b.OrderedSmallColumn
import ErdosProblems.Erdos633b.VeryObtuseNecessity
import ErdosProblems.Erdos633b.RightTileNecessity
import ErdosProblems.Erdos633b.NonouterMultiplicity
import ErdosProblems.Erdos633b.RationalAngleSides
import ErdosProblems.Erdos633b.IncommensurableNecessity
import ErdosProblems.Erdos633b.GroupTwoSixtyRationality
import ErdosProblems.Erdos633b.GroupTwoDoubleRationality
import ErdosProblems.Erdos633b.CaseSevenBranch
import ErdosProblems.Erdos633b.GroupOneSignedPerimeter
import ErdosProblems.Erdos633b.DirectionColorRules
import ErdosProblems.Erdos633b.GroupOneIncidenceParity
import ErdosProblems.Erdos633b.SixShapeNecessity
import ErdosProblems.Erdos633b.CornerPairOrdering
import ErdosProblems.Erdos633b.AngleCoefficientIndependence
import ErdosProblems.Erdos633b.NonouterInventory
import ErdosProblems.Erdos633b.AngleCountBound
import ErdosProblems.Erdos633b.ShapeNecessity
import ErdosProblems.Erdos633b.ReptilingNecessity
import ErdosProblems.Erdos633b.AngleRelations
import ErdosProblems.Erdos633b.BoundaryLength
import ErdosProblems.Erdos633b.CornerRays
import ErdosProblems.Erdos633b.Sufficiency
import ErdosProblems.Erdos633b.EulerFactors
import ErdosProblems.Erdos633b.CaseFive
import ErdosProblems.Erdos633b.CaseSix
import ErdosProblems.Erdos633b.DoubledTiling
import ErdosProblems.Erdos633b.DoubledAngles
import ErdosProblems.Erdos633b.CaseEight
import ErdosProblems.Erdos633b.CaseFour
import ErdosProblems.Erdos633b.CaseThree
import ErdosProblems.Erdos633b.CaseOne
import ErdosProblems.Erdos633b.Arithmetic
import ErdosProblems.Erdos633b.Area
import ErdosProblems.Erdos633b.Descent
import ErdosProblems.Erdos633b.PlanarMotions
import ErdosProblems.Erdos633b.Quadratic
import ErdosProblems.Erdos633b.Rectangle
import ErdosProblems.Erdos633b.Specification
import ErdosProblems.Erdos633b.Trigonometry
import ErdosProblems.Erdos633b.TriquadraticCase
import ErdosProblems.Erdos633b.TriquadraticCoordinates
import ErdosProblems.Erdos633b.TriquadraticRegions
import ErdosProblems.Erdos633b.TriquadraticTriangles

/-!
# Erdős problem 633: complete eight-case triangle-tiling classification

`erdos_633` proves the full necessary-and-sufficient classification of
nondegenerate Euclidean triangles admitting a nonsquare finite dissection
into congruent triangles. `erdos_633_only_square` gives its equivalent
all-square characterization. `EightCases` consists of eight independent
geometric/arithmetic conditions, exactly as in BLZ26 v2, Theorem 1.

`Tiling` requires actual closed coverage by affine-isometric copies of one
nondegenerate triangle and pairwise disjoint topological interiors.
No edge-to-edge assumption or classification axiom is used.

Sufficiency uses eight verified geometric constructions and integer
nonsquare proofs. Necessity uses actual boundaries, local angle sums,
vertex inventories, direction characters, cyclotomic identities, and
complete finite angle exhaustion. All 52 residual angle pairs are discharged
by explicit checked boundary/area certificates or the 30-60-90 outer case.
The needed arithmetic is proved by integer descents and exact certificates;
no elliptic-curve rank/torsion database or external computation is an oracle.
The unavailable Laczkovich 1995 source is not an assumed dependency.

Detailed proof and dependency audit: `tex/633.tex`.
Verification commands and results: `Erdos633b/PROGRESS.md`.
-/

namespace Erdos633b

/-- Complete eight-case classification of nonsquare congruent-triangle dissections. -/
theorem erdos_633 (T : Triangle) :
    (∃ n : ℕ, ¬ IsSquare n ∧ Nonempty (Tiling T n)) ↔ EightCases T :=
  hasNonsquareTiling_iff_eightCases T

/-- Triangles outside the eight cases have only square congruent-triangle dissections. -/
theorem erdos_633_only_square (T : Triangle) :
    (∀ n : ℕ, Nonempty (Tiling T n) → IsSquare n) ↔ ¬ EightCases T :=
  onlySquareTilings_iff_not_eightCases T

end Erdos633b
