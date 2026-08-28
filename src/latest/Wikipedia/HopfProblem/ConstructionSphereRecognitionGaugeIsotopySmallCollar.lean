import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCollar
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothSmallProduct

/-!
# The collar isotopy on the literal original small elliptic pieces

The base-preserving full-cap diffeomorphisms restrict to the actual open
small pieces.  All smoothness statements use their original inherited
atlases, and the restriction retains the negative-parameter inverse.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open ThreefoldOverlapMappingTorus

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  capTimeFillingChartedSpace

/-- An original root radius lying strictly inside the actual small piece. -/
abbrev CollarRadius (j : Kind) := Radius j.order (specialBaseCover.radius (some j))

local instance specialLocalFillingChartedSpace (j : Kind) :
    ChartedSpace FamilyModel
      ((specialLocalData j).Space j.twist (mainTwist_admissible j)) :=
  (specialLocalData j).chartedSpace j.twist (mainTwist_admissible j)

local instance specialFullTimeChartedSpace (j : Kind) :
    ChartedSpace (ℝ × FamilyModel) (ℝ × SpecialFullFilling j) :=
  capTimeFillingChartedSpace (specialLocalData j)

/-- Time times the original inherited small-piece atlas. -/
@[instance_reducible] def smallCollarTimeChartedSpace (j : Kind) :
    ChartedSpace (ℝ × FamilyModel) (ℝ × SpecialEllipticPiece j) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ FamilyModel) (ℝ × SpecialEllipticPiece j))

attribute [local instance] smallCollarTimeChartedSpace

/-- The proved full-cap translation for the unconditional special periods. -/
def specialFullCollarTranslation (j : Kind) (τ θ : ℝ) (a : CollarRadius j) (s : ℝ) :
    SpecialFullFilling j ≃ₜ SpecialFullFilling j :=
  collarTranslation (specialLocalData j) τ θ a a.property.1 s

theorem specialFullCollarTranslation_projection (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialFullFilling j) :
    specialFullFillingProjection j (specialFullCollarTranslation j τ θ a s y) =
      specialFullFillingProjection j y :=
  collarTranslation_projection (specialLocalData j) τ θ a a.property.1 s y

/-- Restriction to the literal full preimage of the original small coordinate ball. -/
def smallCollarHomeomorph (j : Kind) (τ θ : ℝ) (a : CollarRadius j) (s : ℝ) :
    SpecialEllipticPiece j ≃ₜ SpecialEllipticPiece j :=
  (specialFullCollarTranslation j τ θ a s).subtype (fun y => by
    change ‖(specialFullFillingProjection j y : ℂ)‖ < specialBaseCover.radius (some j) ↔
      ‖(specialFullFillingProjection j (specialFullCollarTranslation j τ θ a s y) : ℂ)‖ <
        specialBaseCover.radius (some j)
    rw [specialFullCollarTranslation_projection])

@[simp] theorem smallCollarHomeomorph_val (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    (smallCollarHomeomorph j τ θ a s y).val = specialFullCollarTranslation j τ θ a s y.val :=
  rfl

@[simp] theorem smallCollarHomeomorph_symm_val (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    ((smallCollarHomeomorph j τ θ a s).symm y).val =
      specialFullCollarTranslation j τ θ a (-s) y.val :=
  collarTranslation_symm_apply (specialLocalData j) τ θ a a.property.1 s y.val

@[simp] theorem smallCollarHomeomorph_symm_apply (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    (smallCollarHomeomorph j τ θ a s).symm y = smallCollarHomeomorph j τ θ a (-s) y := by
  apply Subtype.ext
  exact smallCollarHomeomorph_symm_val j τ θ a s y

@[simp] theorem smallCollarHomeomorph_zero (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (y : SpecialEllipticPiece j) :
    smallCollarHomeomorph j τ θ a 0 y = y := by
  apply Subtype.ext
  exact collarTranslation_zero (specialLocalData j) τ θ a a.property.1 y.val

theorem smallCollarHomeomorph_add (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s r : ℝ) (y : SpecialEllipticPiece j) :
    smallCollarHomeomorph j τ θ a (s + r) y =
      smallCollarHomeomorph j τ θ a s (smallCollarHomeomorph j τ θ a r y) := by
  apply Subtype.ext
  exact collarTranslation_add (specialLocalData j) τ θ a a.property.1 s r y.val

private theorem smallTimeInclusion_contMDiff (j : Kind) :
    ContMDiff IT IT ∞ (fun p : ℝ × SpecialEllipticPiece j => (p.1, p.2.val)) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst.prodMk
    ((EllipticSmooth.smallPiece_inclusion_contMDiff j).comp contMDiff_snd)

/-- Joint smoothness of the actual restricted map in the unchanged small-piece atlas. -/
theorem smallCollarHomeomorph_joint_contMDiff (j : Kind) (τ θ : ℝ) (a : CollarRadius j) :
    ContMDiff IT IR ∞ (fun p : ℝ × SpecialEllipticPiece j =>
      smallCollarHomeomorph j τ θ a p.1 p.2) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      specialBaseCover j) _).mp
  exact (collarTranslation_joint_contMDiff (specialLocalData j) τ θ a a.property.1).comp
    (smallTimeInclusion_contMDiff j)

theorem smallCollarHomeomorph_contMDiff (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) : ContMDiff IR IR ∞ (smallCollarHomeomorph j τ θ a s) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      specialBaseCover j) _).mp
  have hfull : ContMDiff IR IR ∞ (specialFullCollarTranslation j τ θ a s) :=
    (collarDiffeomorph (specialLocalData j) τ θ a a.property.1 s).contMDiff_toFun
  exact hfull.comp (EllipticSmooth.smallPiece_inclusion_contMDiff j)

theorem smallCollarHomeomorph_symm_contMDiff (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) :
    ContMDiff IR IR ∞ (smallCollarHomeomorph j τ θ a s).symm := by
  have he : ((smallCollarHomeomorph j τ θ a s).symm : SpecialEllipticPiece j → _) =
      smallCollarHomeomorph j τ θ a (-s) :=
    funext (smallCollarHomeomorph_symm_apply j τ θ a s)
  rw [he]
  exact smallCollarHomeomorph_contMDiff j τ θ a (-s)

/-- The restricted extension is a genuine diffeomorphism, not a transported smooth structure. -/
def smallCollarDiffeomorph (j : Kind) (τ θ : ℝ) (a : CollarRadius j) (s : ℝ) :
    Diffeomorph IR IR (SpecialEllipticPiece j) (SpecialEllipticPiece j) ∞ where
  toEquiv := (smallCollarHomeomorph j τ θ a s).toEquiv
  contMDiff_toFun := smallCollarHomeomorph_contMDiff j τ θ a s
  contMDiff_invFun := smallCollarHomeomorph_symm_contMDiff j τ θ a s

@[simp] theorem smallCollarDiffeomorph_apply (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    smallCollarDiffeomorph j τ θ a s y = smallCollarHomeomorph j τ θ a s y := rfl

@[simp] theorem smallCollarDiffeomorph_symm_apply (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    (smallCollarDiffeomorph j τ θ a s).symm y = smallCollarHomeomorph j τ θ a (-s) y :=
  smallCollarHomeomorph_symm_apply j τ θ a s y

/-- The original compact-base projection is unchanged by every slice. -/
theorem smallCollarHomeomorph_projectionToBase (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    specialEllipticPieceProjectionToBase j (smallCollarHomeomorph j τ θ a s y) =
      specialEllipticPieceProjectionToBase j y := by
  change (punctureChart (some j)).symm
      (specialFullFillingProjection j (smallCollarHomeomorph j τ θ a s y).val : ℂ) =
    (punctureChart (some j)).symm (specialFullFillingProjection j y.val : ℂ)
  rw [smallCollarHomeomorph_val, specialFullCollarTranslation_projection]

/-- An actual root-radius neighborhood of the central fibre is fixed pointwise. -/
theorem smallCollarHomeomorph_eq_self_inner (j : Kind) (τ θ : ℝ)
    (a : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j)
    (hy : ‖((EllipticFullProduct.specialFillingProductHomeomorph j y.val).1 : ℂ)‖ ^ 2 ≤
      (a : ℝ) ^ 2 / 4) : smallCollarHomeomorph j τ θ a s y = y := by
  apply Subtype.ext
  exact collarTranslation_eq_self_inner (specialLocalData j) τ θ a a.property.1 s y.val hy

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
