import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopySmallCollar
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCircle

/-!
# Exact extension of the original attaching-map correction

The constructed small-cap diffeomorphism restricts to the literal original
boundary isotopy, at its unchanged radius and phase.  Consequently its
time-one correction changes the actual attaching map to the actual
linear-gauge map exactly, not merely on homology or up to homotopy.
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

/-- The exact original boundary inclusion intertwines the smooth cap extension
and the literal mapping-torus translation. -/
theorem smallCollarDiffeomorph_boundaryToPieceAt (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (x : SpecialBoundary j) :
    smallCollarDiffeomorph j τ θ a s (specialBoundaryToPieceAt j a θ x) =
      specialBoundaryToPieceAt j a θ (nativeBoundaryTranslation j τ s x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := MappingTorus.mk_surjective (flatTorusAffine j j.twist) x
  apply Subtype.ext
  rw [smallCollarDiffeomorph_apply, smallCollarHomeomorph_val]
  change collarTranslation (specialLocalData j) τ θ a a.property.1 s
      ((specialBoundaryInclusionAt j a θ
        (MappingTorus.mk (flatTorusAffine j j.twist) (t, u))).val :
          SpecialEllipticPiece j).val =
    ((specialBoundaryInclusionAt j a θ (nativeBoundaryTranslation j τ s
      (MappingTorus.mk (flatTorusAffine j j.twist) (t, u)))).val :
        SpecialEllipticPiece j).val
  rw [nativeBoundaryTranslation_mk, specialBoundaryInclusionAt_mk,
    specialBoundaryInclusionAt_mk]
  exact collarTranslation_boundary_quotient (specialLocalData j) τ θ
    (specialBaseCover.radius (some j)) a s t u

/-- The boundary square is an equality of the actual continuous maps. -/
theorem smallCollar_boundary_square (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) :
    ((smallCollarHomeomorph j τ θ a s : C(_, _)).comp
      (specialBoundaryToPieceAt j a θ)) =
    (specialBoundaryToPieceAt j a θ).comp (nativeBoundaryTranslation j τ s) := by
  apply ContinuousMap.ext
  intro x
  exact smallCollarDiffeomorph_boundaryToPieceAt j τ θ a s x

/-- The original native radius and phase determine an unconditional small-cap diffeomorphism. -/
def nativeSmallCollarDiffeomorph (j : Kind) (τ s : ℝ) :
    Diffeomorph IR IR (SpecialEllipticPiece j) (SpecialEllipticPiece j) ∞ :=
  smallCollarDiffeomorph j τ (nativeBoundaryRootPhase j + τ) (nativeBoundaryRootRadius j) s

/-- It preserves the native inclusion point for point throughout the isotopy. -/
theorem nativeSmallCollar_boundary (j : Kind) (τ s : ℝ) (x : SpecialBoundary j) :
    nativeSmallCollarDiffeomorph j τ s (nativeBoundaryInclusion j τ x).val =
      (nativeBoundaryInclusion j τ (nativeBoundaryTranslation j τ s x)).val :=
  smallCollarDiffeomorph_boundaryToPieceAt j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) s x

/-- The smooth extension gives the full exact original-to-linear attaching-map correction. -/
theorem nativeSmallCollar_regular_one (j : Kind) (τ : ℝ) (x : SpecialBoundary j) :
    specialEllipticOverlap j
        (nativeSmallCollarDiffeomorph j τ 1 (nativeBoundaryInclusion j τ x).val) =
      linearRegularBoundaryMap j τ x := by
  rw [nativeSmallCollar_boundary]
  have h := puncturedPieceToRegular_elliptic j
    (nativeBoundaryInclusion j τ (nativeBoundaryTranslation j τ 1 x))
  rw [← h]
  exact congrArg (fun f : C(SpecialBoundary j, SpecialRegularFamily) => f x)
    (nativeRegularBoundaryMap_comp_one j τ)

/-- Joint real smoothness in the unchanged original small-piece atlas. -/
theorem nativeSmallCollar_joint_contMDiff (j : Kind) (τ : ℝ) :
    ContMDiff IT IR ∞ (fun p : ℝ × SpecialEllipticPiece j =>
      nativeSmallCollarDiffeomorph j τ p.1 p.2) :=
  smallCollarHomeomorph_joint_contMDiff j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j)

@[simp] theorem nativeSmallCollar_zero (j : Kind) (τ : ℝ) (y : SpecialEllipticPiece j) :
    nativeSmallCollarDiffeomorph j τ 0 y = y :=
  smallCollarHomeomorph_zero j τ (nativeBoundaryRootPhase j + τ) (nativeBoundaryRootRadius j) y

/-- The inverse is the exact negative-time extension on the same original piece. -/
theorem nativeSmallCollar_symm_apply (j : Kind) (τ s : ℝ) (y : SpecialEllipticPiece j) :
    (nativeSmallCollarDiffeomorph j τ s).symm y = nativeSmallCollarDiffeomorph j τ (-s) y :=
  smallCollarHomeomorph_symm_apply j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) s y

/-- The original base point is fixed, not only its local coordinate. -/
theorem nativeSmallCollar_projectionToBase (j : Kind) (τ s : ℝ) (y : SpecialEllipticPiece j) :
    specialEllipticPieceProjectionToBase j (nativeSmallCollarDiffeomorph j τ s y) =
      specialEllipticPieceProjectionToBase j y :=
  smallCollarHomeomorph_projectionToBase j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) s y

/-- The actual neighborhood of the central fibre is fixed pointwise. -/
theorem nativeSmallCollar_eq_self_inner (j : Kind) (τ s : ℝ) (y : SpecialEllipticPiece j)
    (hy : ‖((EllipticFullProduct.specialFillingProductHomeomorph j y.val).1 : ℂ)‖ ^ 2 ≤
      (nativeBoundaryRootRadius j : ℝ) ^ 2 / 4) : nativeSmallCollarDiffeomorph j τ s y = y :=
  smallCollarHomeomorph_eq_self_inner j τ (nativeBoundaryRootPhase j + τ)
    (nativeBoundaryRootRadius j) s y hy

private theorem nativeSmallCollar_unit_continuous (j : Kind) (τ : ℝ) :
    Continuous (fun p : unitInterval × SpecialEllipticPiece j =>
      nativeSmallCollarDiffeomorph j τ (p.1 : ℝ) p.2) := by
  have hi : Continuous (fun p : unitInterval × SpecialEllipticPiece j =>
      ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  change Continuous ((fun p : ℝ × SpecialEllipticPiece j =>
    nativeSmallCollarDiffeomorph j τ p.1 p.2) ∘
      (fun p : unitInterval × SpecialEllipticPiece j => ((p.1 : ℝ), p.2)))
  exact (nativeSmallCollar_joint_contMDiff j τ).continuous.comp hi

/-- A genuine smooth-slice isotopy of the actual cap, with the boundary square proved above. -/
def nativeSmallCollarIsotopy (j : Kind) (τ : ℝ) :
    (ContinuousMap.id (SpecialEllipticPiece j)).Homotopy
      ((nativeSmallCollarDiffeomorph j τ 1).toHomeomorph : C(_, _)) where
  toFun p := nativeSmallCollarDiffeomorph j τ p.1 p.2
  continuous_toFun := nativeSmallCollar_unit_continuous j τ
  map_zero_left y := nativeSmallCollar_zero j τ y
  map_one_left _ := rfl

@[simp] theorem nativeSmallCollarIsotopy_apply (j : Kind) (τ : ℝ)
    (s : unitInterval) (y : SpecialEllipticPiece j) :
    nativeSmallCollarIsotopy j τ (s, y) = nativeSmallCollarDiffeomorph j τ s y := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
