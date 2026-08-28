import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationReal
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationHomotopy
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationSection
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticNativeMap

/-!
# Linearizing the actual full elliptic boundary map

The original native logarithmic gauge has the proved exact real recurrence.
Its equivariant straight-line interpolation therefore descends to a genuine
homotopy of the entire original boundary map.  At the linear endpoint the
actual cap section has the fixed zero-head-coordinate three-torus fibre.
All endpoint maps and identities retain the original regular family.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

open Elliptic Elliptic.HigherHomology SpecialPeriods SpecialPeriods.Triangle
open SpecialPeriods.EllipticFilling SpecialPeriods.Threefold.EllipticGeometry
open ThreefoldOverlapMappingTorus SingularMayerVietoris PeriodTorusHigherHomology
open EllipticCapProduct

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual regular-family boundary map with its proved time-linear gauge.
There is no additional phase constant in this gauge. -/
def linearRegularBoundaryMap (j : Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j, (Dsp).Space) :=
  gaugeBoundaryMap Dsp j j.twist (linearGauge j j.twist)
    (linearGauge_forward j j.twist j.matrix_fixes_twist)
    (nativeShiftedBase j τ) (nativeShiftedBase_translate j τ)

/-- Every original cylinder representative has the literal linear translation. -/
@[simp] theorem linearRegularBoundaryMap_mk (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    linearRegularBoundaryMap j τ (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (Dsp).quotient (nativeShiftedBase j τ t,
        x + standardLattice.mkQ ((t / (j.order : ℝ)) • realCast j.twist)) := rfl

/-- The original native boundary is exactly the descended real-lift map. -/
theorem nativeRegularBoundaryMap_realLift (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    nativeRegularBoundaryMap j τ (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (Dsp).quotient (nativeShiftedBase j τ t,
        x + standardLattice.mkQ (nativeGaugeRealLift j τ t)) := by
  rw [nativeRegularBoundaryMap_mk, nativeGaugeCylinder_realLift]

/-- A genuine jointly continuous homotopy of the entire original native boundary map. -/
def nativeRegularBoundaryGaugeLinearizationHomotopy (j : Kind) (τ : ℝ) :
    (nativeRegularBoundaryMap j τ).Homotopy (linearRegularBoundaryMap j τ) :=
  gaugeLinearizationHomotopyOfMk Dsp j j.twist j.matrix_fixes_twist
    (nativeGaugeRealLift j τ) (nativeGaugeRealLift_forward j τ)
    (nativeShiftedBase j τ) (nativeShiftedBase_translate j τ)
    (nativeRegularBoundaryMap j τ) (nativeRegularBoundaryMap_realLift j τ)

/-- The homotopy preserves its exact real interpolation at every original representative. -/
@[simp] theorem nativeRegularBoundaryGaugeLinearizationHomotopy_mk
    (j : Kind) (τ : ℝ) (s : unitInterval) (t : ℝ) (x : RealTorus₄) :
    nativeRegularBoundaryGaugeLinearizationHomotopy j τ
        (s, MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (Dsp).quotient (nativeShiftedBase j τ t, x + standardLattice.mkQ
        ((1 - (s : ℝ)) • nativeGaugeRealLift j τ t +
          (s : ℝ) • ((t / (j.order : ℝ)) • realCast j.twist))) := rfl

/-- The actual native gauge can be linearized on the whole mapping torus. -/
theorem nativeRegularBoundaryMap_homotopic_linear (j : Kind) (τ : ℝ) :
    (nativeRegularBoundaryMap j τ).Homotopic (linearRegularBoundaryMap j τ) :=
  ⟨nativeRegularBoundaryGaugeLinearizationHomotopy j τ⟩

/-- The original radius-and-phase boundary is genuinely homotopic to the linear endpoint. -/
theorem boundaryToRegularFamily_homotopic_linear (j : Kind) (τ : ℝ) :
    (boundaryToRegularFamily (some j)).Homotopic (linearRegularBoundaryMap j τ) :=
  (ThreefoldOverlapMappingTorus.Elliptic.boundaryToRegularFamily_homotopic_at j
    (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ)).trans
      (nativeRegularBoundaryMap_homotopic_linear j τ)

/-- Equality with the original global attachment coefficient in every actual homology degree. -/
theorem boundaryRegularHomologyMap_linear (j : Kind) (τ : ℝ) (n : ℕ) :
    boundaryRegularHomologyMap (some j) n =
      singularHomologyMap (linearRegularBoundaryMap j τ) n :=
  homotopic_homologyMap (boundaryToRegularFamily_homotopic_linear j τ) n

/-- On the actual cap section, the linear translation cancels the complete twist term. -/
theorem linearRegularBoundaryMap_capSectionFromModel_mk
    (j : Kind) (τ s : ℝ) (y : ProductTorus 3) :
    linearRegularBoundaryMap j τ
        (capSectionFromModel j (MappingTorus.mk (fibreTorusHomeomorph j).symm (s, y))) =
      (Dsp).quotient (nativeShiftedBase j τ (-s), capSectionFibre j 0 y) := by
  rw [capSectionFromModel_mk, linearRegularBoundaryMap_mk,
    capSectionFibre_linearGauge_cancel]

/-- The cap section has literal zero-head real coordinates after the proved linearization. -/
theorem linearRegularBoundaryMap_capSectionFromModel_coordinateProjection
    (j : Kind) (τ s : ℝ) (k : FibreCoordinates) :
    linearRegularBoundaryMap j τ
        (capSectionFromModel j
          (MappingTorus.mk (fibreTorusHomeomorph j).symm (s, coordinateProjection 3 k))) =
      (Dsp).quotient
        (nativeShiftedBase j τ (-s), standardLattice.mkQ (Fin.cons 0 k)) := by
  rw [linearRegularBoundaryMap_capSectionFromModel_mk,
    capSectionFibre_zero_coordinateProjection]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
