import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyFlowSmall
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyLocalizedBoundary

/-!
# Flow equivariance of the supported original collar isotopy

The additional cutoff depends only on the original squared root radius,
which the actual complex flow preserves. Thus the variable-time collar
translation, its inverse, and the final native supported isotopy all
commute with that same full complex flow. The smooth maps retain the
original inherited small-piece atlas.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Elliptic
open TrianglePeriodFamily.Boundary

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

/-- The actual scalar cutoff is invariant under every original complex flow time. -/
@[simp] theorem smallCollarCutoff_flow (j : Kind) (a b : CollarRadius j) (u : ℂ)
    (y : SpecialEllipticPiece j) :
    smallCollarCutoff j a b (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      smallCollarCutoff j a b y :=
  congrArg (outerRadialCutoff a b) (smallRootSquared_flow j u y)

/-- Invariance of the variable time preserves the exact native flow equivariance. -/
theorem localizedCollarTranslation_flow (j : Kind) (τ θ : ℝ) (a b : CollarRadius j)
    (s : ℝ) (u : ℂ) (y : SpecialEllipticPiece j) :
    localizedCollarTranslation j τ θ a b s
        (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        (localizedCollarTranslation j τ θ a b s y) := by
  simp only [localizedCollarTranslation, smallCollarCutoff_flow]
  exact smallCollarHomeomorph_flow j τ θ a (s * smallCollarCutoff j a b y) u y

theorem localizedCollarHomeomorph_flow (j : Kind) (τ θ : ℝ) (a b : CollarRadius j)
    (s : ℝ) (u : ℂ) (y : SpecialEllipticPiece j) :
    localizedCollarHomeomorph j τ θ a b s
        (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        (localizedCollarHomeomorph j τ θ a b s y) :=
  localizedCollarTranslation_flow j τ θ a b s u y

/-- The smooth supported map uses the unchanged original small-piece atlas. -/
theorem localizedCollarDiffeomorph_flow (j : Kind) (τ θ : ℝ) (a b : CollarRadius j)
    (s : ℝ) (u : ℂ) (y : SpecialEllipticPiece j) :
    localizedCollarDiffeomorph j τ θ a b s
        (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        (localizedCollarDiffeomorph j τ θ a b s y) :=
  localizedCollarTranslation_flow j τ θ a b s u y

theorem localizedCollarDiffeomorph_symm_flow (j : Kind) (τ θ : ℝ) (a b : CollarRadius j)
    (s : ℝ) (u : ℂ) (y : SpecialEllipticPiece j) :
    (localizedCollarDiffeomorph j τ θ a b s).symm
        (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        ((localizedCollarDiffeomorph j τ θ a b s).symm y) :=
  localizedCollarTranslation_flow j τ θ a b (-s) u y

/-- The actual native supported correction commutes with the full original complex flow. -/
theorem nativeLocalizedCollarDiffeomorph_flow (j : Kind) (τ s : ℝ) (u : ℂ)
    (y : SpecialEllipticPiece j) :
    nativeLocalizedCollarDiffeomorph j τ s
        (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        (nativeLocalizedCollarDiffeomorph j τ s y) :=
  localizedCollarDiffeomorph_flow j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j)) s u y

theorem nativeLocalizedCollarDiffeomorph_commute_flow (j : Kind) (τ s : ℝ) (u : ℂ) :
    Function.Commute (nativeLocalizedCollarDiffeomorph j τ s)
      (Threefold.VerticalAction.Elliptic.specialFlow j u) :=
  nativeLocalizedCollarDiffeomorph_flow j τ s u

theorem nativeLocalizedCollarDiffeomorph_symm_flow (j : Kind) (τ s : ℝ) (u : ℂ)
    (y : SpecialEllipticPiece j) :
    (nativeLocalizedCollarDiffeomorph j τ s).symm
        (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        ((nativeLocalizedCollarDiffeomorph j τ s).symm y) := by
  simp only [nativeLocalizedCollar_symm_apply]
  exact nativeLocalizedCollarDiffeomorph_flow j τ (-s) u y

/-- Every point of the supported native isotopy has this exact flow equivariance. -/
theorem nativeLocalizedCollarIsotopy_flow (j : Kind) (τ : ℝ) (s : unitInterval)
    (u : ℂ) (y : SpecialEllipticPiece j) :
    nativeLocalizedCollarIsotopy j τ (s, Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u (nativeLocalizedCollarIsotopy j τ (s, y)) :=
  nativeLocalizedCollarDiffeomorph_flow j τ (s : ℝ) u y

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
