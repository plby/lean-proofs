import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeMap
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry

/-!
# Exact original boundary formulas in the global threefold

The native boundary is included through its original punctured elliptic
piece.  At time one the global diffeomorphism identifies this exact map
with the included linear-gauge boundary map in the original regular
family.  The statements concern these boundary maps, not an equality
on an unspecified larger overlap.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold ContinuousMap

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold GaugeIsotopy
open TrianglePeriodFamily.Boundary TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Elliptic

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace

/-- The boundary point with the original small-cap type made explicit. -/
def nativeBoundaryPoint (j : Kind) (τ : ℝ) (x : SpecialBoundary j) :
    SpecialEllipticPiece j := (nativeBoundaryInclusion j τ x).val

/-- The unchanged actual native boundary, included into the original global space. -/
def nativeGlobalBoundary (j : Kind) (τ : ℝ) : C(SpecialBoundary j, Threefold.Space) :=
  (Homology.originalPieceInclusion (some (some j))).comp
    ((puncturedPieceInclusion (some j)).comp (nativeBoundaryInclusion j τ))

@[simp] theorem nativeGlobalBoundary_apply (j : Kind) (τ : ℝ) (x : SpecialBoundary j) :
    nativeGlobalBoundary j τ x =
      EllipticGeometry.inclusion j (nativeBoundaryPoint j τ x) := rfl

/-- The two original gluing representatives give the same literal global boundary point. -/
theorem nativeGlobalBoundary_eq_regular (j : Kind) (τ : ℝ) (x : SpecialBoundary j) :
    nativeGlobalBoundary j τ x = regularFamilyInclusion (nativeRegularBoundaryMap j τ x) :=
  (puncturedPieceToRegular_inclusion (some j) (nativeBoundaryInclusion j τ x)).symm

theorem globalDiffeomorph_boundary (j : Kind) (τ s : ℝ) (x : SpecialBoundary j) :
    globalDiffeomorph j τ s (nativeGlobalBoundary j τ x) =
      nativeGlobalBoundary j τ (nativeBoundaryTranslation j τ s x) := by
  have h : nativeLocalizedCollarDiffeomorph j τ s (nativeBoundaryPoint j τ x) =
      nativeBoundaryPoint j τ (nativeBoundaryTranslation j τ s x) :=
    nativeLocalizedCollar_boundary j τ s x
  rw [nativeGlobalBoundary_apply, globalDiffeomorph_inclusion, h, nativeGlobalBoundary_apply]

/-- The full original boundary square holds as an equality of continuous maps. -/
theorem globalDiffeomorph_boundary_square (j : Kind) (τ s : ℝ) :
    ((globalDiffeomorph j τ s).toHomeomorph : C(_, _)).comp (nativeGlobalBoundary j τ) =
      (nativeGlobalBoundary j τ).comp (nativeBoundaryTranslation j τ s) := by
  apply ContinuousMap.ext
  exact globalDiffeomorph_boundary j τ s

/-- Time one gives the exact native-to-linear attaching-map normal form in the original space. -/
theorem globalDiffeomorph_boundary_one (j : Kind) (τ : ℝ) (x : SpecialBoundary j) :
    globalDiffeomorph j τ 1 (nativeGlobalBoundary j τ x) =
      regularFamilyInclusion (linearRegularBoundaryMap j τ x) := by
  rw [globalDiffeomorph_boundary, nativeGlobalBoundary_eq_regular]
  apply congrArg regularFamilyInclusion
  exact congrArg (fun f : C(SpecialBoundary j, SpecialRegularFamily) => f x)
    (nativeRegularBoundaryMap_comp_one j τ)

theorem globalDiffeomorph_attaching_normalForm (j : Kind) (τ : ℝ) :
    ((globalDiffeomorph j τ 1).toHomeomorph : C(_, _)).comp (nativeGlobalBoundary j τ) =
      Homology.originalRegularInclusion.comp (linearRegularBoundaryMap j τ) := by
  apply ContinuousMap.ext
  exact globalDiffeomorph_boundary_one j τ

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
