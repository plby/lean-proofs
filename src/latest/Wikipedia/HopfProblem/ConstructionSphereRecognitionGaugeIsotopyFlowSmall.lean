import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyFlow
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyRadius
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyBoundary
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticSpecial

/-!
# Native vertical-flow equivariance on the original small elliptic pieces

The original complex flow preserves the actual root radius and commutes
with the cap translation before restriction. Passing to the literal
small-piece subtype retains these equalities, including at its core.
The smooth wrappers use the original inherited small-piece atlas.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Elliptic
open TrianglePeriodFamily.Boundary

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

/-- The original full complex flow fixes the actual squared root radius. -/
@[simp] theorem capRootSquared_flow {j : Kind} (D : Equivariant.Data j) (u : ℂ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    capRootSquared D
        (Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u y) =
      capRootSquared D y := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rw [Threefold.VerticalAction.Elliptic.flow_quotient]
  exact (capRootSquared_quotient D z _).trans (capRootSquared_quotient D z x).symm

/-- The actual restricted complex flow preserves the same native radius. -/
@[simp] theorem smallRootSquared_flow (j : Kind) (u : ℂ) (y : SpecialEllipticPiece j) :
    smallRootSquared j (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      smallRootSquared j y :=
  capRootSquared_flow (specialLocalData j) u y.val

/-- The constructed full collar correction commutes with every native complex flow time. -/
theorem collarTranslation_flow {j : Kind} (D : Equivariant.Data j)
    (τ θ a : ℝ) (ha : 0 < a) (s : ℝ) (u : ℂ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    collarTranslation D τ θ a ha s
        (Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u y) =
      Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u
        (collarTranslation D τ θ a ha s y) :=
  capTranslation_flow D (collarVector j τ θ a) (collarVector_contMDiff j τ θ ha)
    (collarVector_rotation j τ θ a) s u y

/-- Equivariance survives restriction to the actual original small piece. -/
theorem smallCollarHomeomorph_flow (j : Kind) (τ θ : ℝ) (a : CollarRadius j)
    (s : ℝ) (u : ℂ) (y : SpecialEllipticPiece j) :
    smallCollarHomeomorph j τ θ a s (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u (smallCollarHomeomorph j τ θ a s y) := by
  apply Subtype.ext
  exact collarTranslation_flow (specialLocalData j) τ θ a a.property.1 s u y.val

theorem smallCollarHomeomorph_commute_flow (j : Kind) (τ θ : ℝ) (a : CollarRadius j)
    (s : ℝ) (u : ℂ) :
    Function.Commute (smallCollarHomeomorph j τ θ a s)
      (Threefold.VerticalAction.Elliptic.specialFlow j u) :=
  smallCollarHomeomorph_flow j τ θ a s u

/-- The inverse restriction has the same exact native flow equivariance. -/
theorem smallCollarHomeomorph_symm_flow (j : Kind) (τ θ : ℝ) (a : CollarRadius j)
    (s : ℝ) (u : ℂ) (y : SpecialEllipticPiece j) :
    (smallCollarHomeomorph j τ θ a s).symm (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        ((smallCollarHomeomorph j τ θ a s).symm y) := by
  simp only [smallCollarHomeomorph_symm_apply]
  exact smallCollarHomeomorph_flow j τ θ a (-s) u y

/-- The smooth collar map keeps this equality in the original inherited atlas. -/
theorem smallCollarDiffeomorph_flow (j : Kind) (τ θ : ℝ) (a : CollarRadius j)
    (s : ℝ) (u : ℂ) (y : SpecialEllipticPiece j) :
    smallCollarDiffeomorph j τ θ a s (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u (smallCollarDiffeomorph j τ θ a s y) :=
  smallCollarHomeomorph_flow j τ θ a s u y

/-- The actual native radius and phase give unconditional small-collar equivariance. -/
theorem nativeSmallCollarDiffeomorph_flow (j : Kind) (τ s : ℝ) (u : ℂ)
    (y : SpecialEllipticPiece j) :
    nativeSmallCollarDiffeomorph j τ s (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u (nativeSmallCollarDiffeomorph j τ s y) :=
  smallCollarDiffeomorph_flow j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) s u y

theorem nativeSmallCollarDiffeomorph_symm_flow (j : Kind) (τ s : ℝ) (u : ℂ)
    (y : SpecialEllipticPiece j) :
    (nativeSmallCollarDiffeomorph j τ s).symm
        (Threefold.VerticalAction.Elliptic.specialFlow j u y) =
      Threefold.VerticalAction.Elliptic.specialFlow j u
        ((nativeSmallCollarDiffeomorph j τ s).symm y) := by
  simp only [nativeSmallCollar_symm_apply]
  exact nativeSmallCollarDiffeomorph_flow j τ (-s) u y

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
