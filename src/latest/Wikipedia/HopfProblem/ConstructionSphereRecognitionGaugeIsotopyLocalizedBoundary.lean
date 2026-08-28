import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyLocalized
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyBoundary

/-!
# The exact attaching-map isotopy supported in the original small collar

A larger radius is constructed inside the original admissible-radius
interval.  The localized diffeomorphisms are the identity near the cap
core and at or beyond this larger radius.  On the original boundary they
retain exactly the full native gauge correction.
-/

noncomputable section

open scoped ContDiff Manifold ContinuousMap

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Elliptic
open TrianglePeriodFamily.Boundary
open TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  smallCollarTimeChartedSpace

/-- The additional cutoff is identically one on the original boundary. -/
theorem localizedCollar_boundary_eq (j : Kind) (τ θ : ℝ) (a b : CollarRadius j)
    (hab : (a : ℝ) < b) (s : ℝ) (x : SpecialBoundary j) :
    localizedCollarTranslation j τ θ a b s (specialBoundaryToPieceAt j a θ x) =
      smallCollarDiffeomorph j τ θ a s (specialBoundaryToPieceAt j a θ x) := by
  rw [localizedCollarTranslation, smallCollarCutoff, smallRootSquared_boundaryToPieceAt,
    outerRadialCutoff_at_radius_sq a.property.1.le hab, mul_one]
  rfl

/-- The original radius-and-phase boundary is retained point for point. -/
theorem localizedCollar_boundary (j : Kind) (τ θ : ℝ) (a b : CollarRadius j)
    (hab : (a : ℝ) < b) (s : ℝ) (x : SpecialBoundary j) :
    localizedCollarDiffeomorph j τ θ a b s (specialBoundaryToPieceAt j a θ x) =
      specialBoundaryToPieceAt j a θ (nativeBoundaryTranslation j τ s x) :=
  (localizedCollar_boundary_eq j τ θ a b hab s x).trans
    (smallCollarDiffeomorph_boundaryToPieceAt j τ θ a s x)

/-- An unconditional smooth extension supported inside the actual small elliptic collar. -/
def nativeLocalizedCollarDiffeomorph (j : Kind) (τ s : ℝ) :
    Diffeomorph IR IR (SpecialEllipticPiece j) (SpecialEllipticPiece j) ∞ :=
  localizedCollarDiffeomorph j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j)) s

theorem nativeLocalizedCollar_boundary_eq (j : Kind) (τ s : ℝ) (x : SpecialBoundary j) :
    nativeLocalizedCollarDiffeomorph j τ s (nativeBoundaryInclusion j τ x).val =
      nativeSmallCollarDiffeomorph j τ s (nativeBoundaryInclusion j τ x).val :=
  localizedCollar_boundary_eq j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j))
    (lt_largerRadius _) s x

/-- The supported extension induces the exact original boundary isotopy. -/
theorem nativeLocalizedCollar_boundary (j : Kind) (τ s : ℝ) (x : SpecialBoundary j) :
    nativeLocalizedCollarDiffeomorph j τ s (nativeBoundaryInclusion j τ x).val =
      (nativeBoundaryInclusion j τ (nativeBoundaryTranslation j τ s x)).val :=
  (nativeLocalizedCollar_boundary_eq j τ s x).trans (nativeSmallCollar_boundary j τ s x)

/-- The exact full original attaching map is linearized by the supported cap diffeomorphism. -/
theorem nativeLocalizedCollar_regular_one (j : Kind) (τ : ℝ) (x : SpecialBoundary j) :
    specialEllipticOverlap j
        (nativeLocalizedCollarDiffeomorph j τ 1 (nativeBoundaryInclusion j τ x).val) =
      linearRegularBoundaryMap j τ x := by
  rw [nativeLocalizedCollar_boundary_eq]
  exact nativeSmallCollar_regular_one j τ x

theorem nativeLocalizedCollar_joint_contMDiff (j : Kind) (τ : ℝ) :
    ContMDiff IT IR ∞ (fun p : ℝ × SpecialEllipticPiece j =>
      nativeLocalizedCollarDiffeomorph j τ p.1 p.2) :=
  localizedCollarTranslation_joint_contMDiff j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j))

@[simp] theorem nativeLocalizedCollar_zero (j : Kind) (τ : ℝ) (y : SpecialEllipticPiece j) :
    nativeLocalizedCollarDiffeomorph j τ 0 y = y :=
  localizedCollarTranslation_zero j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j)) y

@[simp] theorem nativeLocalizedCollar_symm_apply (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j) :
    (nativeLocalizedCollarDiffeomorph j τ s).symm y =
      nativeLocalizedCollarDiffeomorph j τ (-s) y := rfl

theorem nativeLocalizedCollar_projectionToBase (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j) :
    specialEllipticPieceProjectionToBase j (nativeLocalizedCollarDiffeomorph j τ s y) =
      specialEllipticPieceProjectionToBase j y :=
  localizedCollarTranslation_projectionToBase j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j)) s y

/-- The actual inner neighborhood is fixed pointwise at every time. -/
theorem nativeLocalizedCollar_eq_self_inner (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j)
    (hy : smallRootSquared j y ≤ (nativeBoundaryRootRadius j : ℝ) ^ 2 / 4) :
    nativeLocalizedCollarDiffeomorph j τ s y = y :=
  localizedCollarTranslation_eq_self_inner j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j)) s y hy

/-- The larger radius still lies strictly inside the original small piece. -/
theorem nativeLocalizedCollar_outer_radius (j : Kind) :
    (largerRadius (nativeBoundaryRootRadius j) : ℝ) ^ j.order <
      specialBaseCover.radius (some j) :=
  (largerRadius (nativeBoundaryRootRadius j)).property.2.2

/-- All points at or beyond the permitted outer radius are fixed pointwise. -/
theorem nativeLocalizedCollar_eq_self_outer (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j)
    (hy : (largerRadius (nativeBoundaryRootRadius j) : ℝ) ^ 2 ≤ smallRootSquared j y) :
    nativeLocalizedCollarDiffeomorph j τ s y = y :=
  localizedCollarTranslation_eq_self_outer j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) (largerRadius (nativeBoundaryRootRadius j))
    (lt_largerRadius _) s y hy

/-- Every moved point is in the explicit inner/outer annular collar. -/
theorem nativeLocalizedCollar_ne_self_radius (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j) (hy : nativeLocalizedCollarDiffeomorph j τ s y ≠ y) :
    (nativeBoundaryRootRadius j : ℝ) ^ 2 / 4 < smallRootSquared j y ∧
      smallRootSquared j y < (largerRadius (nativeBoundaryRootRadius j) : ℝ) ^ 2 :=
  ⟨lt_of_not_ge (fun h => hy (nativeLocalizedCollar_eq_self_inner j τ s y h)),
    lt_of_not_ge (fun h => hy (nativeLocalizedCollar_eq_self_outer j τ s y h))⟩

private theorem nativeLocalizedCollar_unit_continuous (j : Kind) (τ : ℝ) :
    Continuous (fun p : unitInterval × SpecialEllipticPiece j =>
      nativeLocalizedCollarDiffeomorph j τ (p.1 : ℝ) p.2) := by
  have hi : Continuous (fun p : unitInterval × SpecialEllipticPiece j =>
      ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  change Continuous ((fun p : ℝ × SpecialEllipticPiece j =>
    nativeLocalizedCollarDiffeomorph j τ p.1 p.2) ∘
      (fun p : unitInterval × SpecialEllipticPiece j => ((p.1 : ℝ), p.2)))
  exact (nativeLocalizedCollar_joint_contMDiff j τ).continuous.comp hi

/-- A supported isotopy of the original small piece, with smooth slices and explicit inverses. -/
def nativeLocalizedCollarIsotopy (j : Kind) (τ : ℝ) :
    (ContinuousMap.id (SpecialEllipticPiece j)).Homotopy
      ((nativeLocalizedCollarDiffeomorph j τ 1).toHomeomorph : C(_, _)) where
  toFun p := nativeLocalizedCollarDiffeomorph j τ p.1 p.2
  continuous_toFun := nativeLocalizedCollar_unit_continuous j τ
  map_zero_left y := nativeLocalizedCollar_zero j τ y
  map_one_left _ := rfl

@[simp] theorem nativeLocalizedCollarIsotopy_apply (j : Kind) (τ : ℝ)
    (s : unitInterval) (y : SpecialEllipticPiece j) :
    nativeLocalizedCollarIsotopy j τ (s, y) = nativeLocalizedCollarDiffeomorph j τ s y := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
