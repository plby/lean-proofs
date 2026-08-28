import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeBoundary
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeCombined

/-!
# Simultaneous exact normal forms for the two original boundary maps

The two disjoint supported corrections are one global smooth isotopy.
On each actual native boundary, its time-one map gives the original
linear-gauge regular-family map, followed by the unchanged inclusion in
the global threefold.  No equality on a larger overlap is inferred.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold ContinuousMap

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold GaugeIsotopy
open TrianglePeriodFamily.Boundary TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Elliptic

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace

/-- The independently specified original phases of the two elliptic boundaries. -/
def boundaryPhase (τ₃ τ₄ : ℝ) : Kind → ℝ
  | .three => τ₃
  | .four => τ₄

@[simp] theorem boundaryPhase_three (τ₃ τ₄ : ℝ) : boundaryPhase τ₃ τ₄ .three = τ₃ := rfl

@[simp] theorem boundaryPhase_four (τ₃ τ₄ : ℝ) : boundaryPhase τ₃ τ₄ .four = τ₄ := rfl

theorem combinedDiffeomorph_inclusion (τ₃ τ₄ s : ℝ) (j : Kind)
    (y : SpecialEllipticPiece j) :
    combinedDiffeomorph τ₃ τ₄ s (EllipticGeometry.inclusion j y) =
      EllipticGeometry.inclusion j
        (nativeLocalizedCollarDiffeomorph j (boundaryPhase τ₃ τ₄ j) s y) := by
  cases j with
  | three => exact combinedDiffeomorph_inclusion_three τ₃ τ₄ s y
  | four => exact combinedDiffeomorph_inclusion_four τ₃ τ₄ s y

/-- Every time slice retains each exact original boundary parametrization. -/
theorem combinedDiffeomorph_boundary (τ₃ τ₄ s : ℝ) (j : Kind) (x : SpecialBoundary j) :
    combinedDiffeomorph τ₃ τ₄ s (nativeGlobalBoundary j (boundaryPhase τ₃ τ₄ j) x) =
      nativeGlobalBoundary j (boundaryPhase τ₃ τ₄ j)
        (nativeBoundaryTranslation j (boundaryPhase τ₃ τ₄ j) s x) := by
  have h : nativeLocalizedCollarDiffeomorph j (boundaryPhase τ₃ τ₄ j) s
        (nativeBoundaryPoint j (boundaryPhase τ₃ τ₄ j) x) =
      nativeBoundaryPoint j (boundaryPhase τ₃ τ₄ j)
        (nativeBoundaryTranslation j (boundaryPhase τ₃ τ₄ j) s x) :=
    nativeLocalizedCollar_boundary j (boundaryPhase τ₃ τ₄ j) s x
  rw [nativeGlobalBoundary_apply, combinedDiffeomorph_inclusion, h, nativeGlobalBoundary_apply]

/-- Both original attaching maps are simultaneously linearized by one genuine global map. -/
theorem combinedDiffeomorph_boundary_one (τ₃ τ₄ : ℝ) (j : Kind) (x : SpecialBoundary j) :
    combinedDiffeomorph τ₃ τ₄ 1 (nativeGlobalBoundary j (boundaryPhase τ₃ τ₄ j) x) =
      regularFamilyInclusion (linearRegularBoundaryMap j (boundaryPhase τ₃ τ₄ j) x) := by
  rw [combinedDiffeomorph_boundary, nativeGlobalBoundary_eq_regular]
  apply congrArg regularFamilyInclusion
  exact congrArg (fun f : C(SpecialBoundary j, SpecialRegularFamily) => f x)
    (nativeRegularBoundaryMap_comp_one j (boundaryPhase τ₃ τ₄ j))

/-- The simultaneous normal form is an equality of the literal original continuous maps. -/
theorem combinedDiffeomorph_attaching_normalForm (τ₃ τ₄ : ℝ) (j : Kind) :
    ((combinedDiffeomorph τ₃ τ₄ 1).toHomeomorph : C(_, _)).comp
        (nativeGlobalBoundary j (boundaryPhase τ₃ τ₄ j)) =
      Homology.originalRegularInclusion.comp
        (linearRegularBoundaryMap j (boundaryPhase τ₃ τ₄ j)) := by
  apply ContinuousMap.ext
  exact combinedDiffeomorph_boundary_one τ₃ τ₄ j

theorem combinedIsotopy_boundary (τ₃ τ₄ : ℝ) (s : unitInterval) (j : Kind)
    (x : SpecialBoundary j) :
    combinedIsotopy τ₃ τ₄ (s, nativeGlobalBoundary j (boundaryPhase τ₃ τ₄ j) x) =
      nativeGlobalBoundary j (boundaryPhase τ₃ τ₄ j)
        (nativeBoundaryTranslation j (boundaryPhase τ₃ τ₄ j) s x) :=
  combinedDiffeomorph_boundary τ₃ τ₄ s j x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
