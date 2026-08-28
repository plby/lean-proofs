import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticNativeMap
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticColumnFrames
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCanonicalCircle
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryWangComponents

/-!
# The actual elliptic boundary map respects the fixed slit cover

The normalized map is genuinely homotopic to the original attachment,
with its entire native logarithmic gauge retained.  Its actual projection
is the phased positive circle.  The real interval charts of the original
mapping torus therefore prove that it maps the two actual open cover
members into the upper and lower regular-family opens.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Elliptic Homology
open SpecialPeriods.Threefold.EllipticGeometry
open SingularMayerVietoris PeriodTorusHigherHomology
open MappingTorus.HomologyCover

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The homotopic actual boundary model with the fixed geometrically chosen slit phase. -/
def ellipticSlitBoundaryMap (j : Kind) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j, (Dsp).Space) :=
  normalizedEllipticBoundaryMap j (ellipticBoundaryPhase j)

/-- The actual projected point of every real-cylinder representative. -/
theorem ellipticSlitBoundaryMap_projection_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    (Dsp).projection
        (ellipticSlitBoundaryMap j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))) =
      triangleRegularProject (canonicalPhasedLift (attachingMeridianIndex j) t) := by
  rw [ellipticSlitBoundaryMap, normalizedEllipticBoundaryMap_mk,
    (Dsp).projection_quotient]
  change triangleRegularProject
    (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, t)) = _
  rw [nativeShiftedSquareLift_canonical, triangleRegularProject_covering.map_smul]

/-- Every point of the first actual mapping-torus open maps to the actual upper family open. -/
theorem ellipticSlitBoundaryMap_upper (j : Kind) :
    MapsTo (ellipticSlitBoundaryMap j) (U (flatTorusAffine j j.twist)) (upperFamily Dsp) := by
  intro q hq
  let p := chartU (flatTorusAffine j j.twist) ⟨q, hq⟩
  have hp : MappingTorus.mk (flatTorusAffine j j.twist) ((p.1 : ℝ), p.2) = q :=
    chartU_representation (flatTorusAffine j j.twist) ⟨q, hq⟩
  rw [← hp]
  change (Dsp).projection (ellipticSlitBoundaryMap j
    (MappingTorus.mk (flatTorusAffine j j.twist) ((p.1 : ℝ), p.2))) ∈ upperBase
  rw [ellipticSlitBoundaryMap_projection_mk]
  exact canonicalPhasedLift_mem_upperBase (attachingMeridianIndex j)
    p.1.property.1 p.1.property.2

/-- The second actual mapping-torus open maps to the actual lower family open. -/
theorem ellipticSlitBoundaryMap_lower (j : Kind) :
    MapsTo (ellipticSlitBoundaryMap j) (V (flatTorusAffine j j.twist)) (lowerFamily Dsp) := by
  intro q hq
  let p := chartV (flatTorusAffine j j.twist) ⟨q, hq⟩
  have hp : MappingTorus.mk (flatTorusAffine j j.twist) ((p.1 : ℝ), p.2) = q :=
    chartV_representation (flatTorusAffine j j.twist) ⟨q, hq⟩
  rw [← hp]
  change (Dsp).projection (ellipticSlitBoundaryMap j
    (MappingTorus.mk (flatTorusAffine j j.twist) ((p.1 : ℝ), p.2))) ∈ lowerBase
  rw [ellipticSlitBoundaryMap_projection_mk]
  exact canonicalPhasedLift_mem_lowerBase (attachingMeridianIndex j)
    p.1.property.1 p.1.property.2

/-- The literal original attaching coefficient is this actual slit-map
coefficient in all degrees. -/
theorem boundaryRegularHomologyMap_slit (j : Kind) (n : ℕ) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (some j) n =
      singularHomologyMap (ellipticSlitBoundaryMap j) n :=
  boundaryRegularHomologyMap_normalized j (ellipticBoundaryPhase j) n

/-- The first actual intersection column at real time one quarter. -/
def ellipticLowerColumn (j : Kind) : C(RealTorus₄, familyIntersection Dsp) :=
  lowerColumnMap (flatTorusAffine j j.twist) Dsp (ellipticSlitBoundaryMap j)
    (ellipticSlitBoundaryMap_upper j) (ellipticSlitBoundaryMap_lower j)

/-- The second actual intersection column at real time three quarters. -/
def ellipticUpperColumn (j : Kind) : C(RealTorus₄, familyIntersection Dsp) :=
  upperColumnMap (flatTorusAffine j j.twist) Dsp (ellipticSlitBoundaryMap j)
    (ellipticSlitBoundaryMap_upper j) (ellipticSlitBoundaryMap_lower j)

/-- The first column retains the actual native fibre coordinate without
any homological simplification. -/
theorem ellipticLowerColumn_coe (j : Kind) (x : RealTorus₄) :
    (ellipticLowerColumn j x).val = (Dsp).quotient
      (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4),
        nativeGaugeCylinder j (ellipticBoundaryPhase j) (1 / 4, x)) := by
  rw [ellipticLowerColumn, lowerColumnMap_coe]
  exact normalizedEllipticBoundaryMap_mk j (ellipticBoundaryPhase j) (1 / 4) x

/-- The second column likewise retains the full original fibre-coordinate formula. -/
theorem ellipticUpperColumn_coe (j : Kind) (x : RealTorus₄) :
    (ellipticUpperColumn j x).val = (Dsp).quotient
      (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4),
        nativeGaugeCylinder j (ellipticBoundaryPhase j) (3 / 4, x)) := by
  rw [ellipticUpperColumn, upperColumnMap_coe]
  exact normalizedEllipticBoundaryMap_mk j (ellipticBoundaryPhase j) (3 / 4) x

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
