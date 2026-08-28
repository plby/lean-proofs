import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyRadius
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyOuterCutoff

/-!
# Localizing the smooth isotopy inside the actual small collar

The squared root radius is smooth and invariant under every constructed
translation.  Multiplying the translation time by an explicit outer
cutoff therefore retains the negative-time inverse and joint smoothness.
The cutoff can vanish before the boundary of the original small piece.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods SpecialPeriods.Threefold

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)

attribute [local instance] specialEllipticPieceChartedSpace smallCollarTimeChartedSpace

/-- The outer cutoff evaluated on the actual smooth invariant radius. -/
def smallCollarCutoff (j : Kind) (a b : CollarRadius j) (y : SpecialEllipticPiece j) : ℝ :=
  outerRadialCutoff a b (smallRootSquared j y)

theorem smallCollarCutoff_contMDiff (j : Kind) (a b : CollarRadius j) :
    ContMDiff IR 𝓘(ℝ, ℝ) ∞ (smallCollarCutoff j a b) :=
  (outerRadialCutoff_contDiff a b).contMDiff.comp (smallRootSquared_contMDiff j)

theorem smallCollarCutoff_invariant (j : Kind) (τ θ : ℝ) (a b : CollarRadius j)
    (s : ℝ) (y : SpecialEllipticPiece j) :
    smallCollarCutoff j a b (smallCollarHomeomorph j τ θ a s y) = smallCollarCutoff j a b y := by
  rw [smallCollarCutoff, smallRootSquared_collar]
  rfl

/-- A literal variable-time translation, with time constant on every translation orbit. -/
def localizedCollarTranslation (j : Kind) (τ θ : ℝ) (a b : CollarRadius j) (s : ℝ)
    (y : SpecialEllipticPiece j) : SpecialEllipticPiece j :=
  smallCollarHomeomorph j τ θ a (s * smallCollarCutoff j a b y) y

@[simp] theorem localizedCollarTranslation_zero (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (y : SpecialEllipticPiece j) :
    localizedCollarTranslation j τ θ a b 0 y = y := by
  rw [localizedCollarTranslation, zero_mul, smallCollarHomeomorph_zero]

theorem localizedCollarTranslation_rootSquared (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    smallRootSquared j (localizedCollarTranslation j τ θ a b s y) = smallRootSquared j y :=
  smallRootSquared_collar j τ θ a _ y

/-- Invariance of the radius makes the localized parameter an exact additive action. -/
theorem localizedCollarTranslation_add (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (s r : ℝ) (y : SpecialEllipticPiece j) :
    localizedCollarTranslation j τ θ a b (s + r) y =
      localizedCollarTranslation j τ θ a b s (localizedCollarTranslation j τ θ a b r y) := by
  simp only [localizedCollarTranslation, smallCollarCutoff_invariant]
  rw [← smallCollarHomeomorph_add, add_mul]

private theorem smallTime_first_contMDiff (j : Kind) :
    ContMDiff IT 𝓘(ℝ, ℝ) ∞ (Prod.fst : ℝ × SpecialEllipticPiece j → ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

private theorem smallTime_second_contMDiff (j : Kind) :
    ContMDiff IT IR ∞ (Prod.snd : ℝ × SpecialEllipticPiece j → SpecialEllipticPiece j) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

/-- The literal cutoff change of time, leaving the original point unchanged. -/
def localizedTimeRescale (j : Kind) (a b : CollarRadius j)
    (p : ℝ × SpecialEllipticPiece j) : ℝ × SpecialEllipticPiece j :=
  (p.1 * smallCollarCutoff j a b p.2, p.2)

theorem localizedTimeRescale_contMDiff (j : Kind) (a b : CollarRadius j) :
    ContMDiff IT IT ∞ (localizedTimeRescale j a b) := by
  have ht : ContMDiff IT 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × SpecialEllipticPiece j => p.1 * smallCollarCutoff j a b p.2) :=
    (smallTime_first_contMDiff j).mul
      ((smallCollarCutoff_contMDiff j a b).comp (smallTime_second_contMDiff j))
  rw [modelWithCornersSelf_prod]
  exact ht.prodMk (smallTime_second_contMDiff j)

theorem localizedCollarTranslation_eq_comp (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) :
    (fun p : ℝ × SpecialEllipticPiece j => localizedCollarTranslation j τ θ a b p.1 p.2) =
      (fun p : ℝ × SpecialEllipticPiece j => smallCollarHomeomorph j τ θ a p.1 p.2) ∘
        localizedTimeRescale j a b := rfl

/-- The localized translation is jointly smooth in the original inherited atlas. -/
theorem localizedCollarTranslation_joint_contMDiff (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) :
    ContMDiff IT IR ∞ (fun p : ℝ × SpecialEllipticPiece j =>
      localizedCollarTranslation j τ θ a b p.1 p.2) := by
  rw [localizedCollarTranslation_eq_comp]
  exact (smallCollarHomeomorph_joint_contMDiff j τ θ a).comp
    (localizedTimeRescale_contMDiff j a b)

theorem localizedCollarTranslation_joint_continuous (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) :
    Continuous (fun p : ℝ × SpecialEllipticPiece j =>
      localizedCollarTranslation j τ θ a b p.1 p.2) :=
  (localizedCollarTranslation_joint_contMDiff j τ θ a b).continuous

private def smallTimeInsert (j : Kind) (s : ℝ) (y : SpecialEllipticPiece j) :
    ℝ × SpecialEllipticPiece j := (s, y)

private theorem smallTimeInsert_contMDiff (j : Kind) (s : ℝ) :
    ContMDiff IR IT ∞ (smallTimeInsert j s) := by
  have hs : ContMDiff IR 𝓘(ℝ, ℝ) ∞ (fun _ : SpecialEllipticPiece j => s) := contMDiff_const
  have hi : ContMDiff IR IR ∞ (fun y : SpecialEllipticPiece j => y) := contMDiff_id
  rw [modelWithCornersSelf_prod]
  exact hs.prodMk hi

theorem localizedCollarTranslation_contMDiff (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (s : ℝ) :
    ContMDiff IR IR ∞ (localizedCollarTranslation j τ θ a b s) := by
  change ContMDiff IR IR ∞
    ((fun p : ℝ × SpecialEllipticPiece j => localizedCollarTranslation j τ θ a b p.1 p.2) ∘
      smallTimeInsert j s)
  exact (localizedCollarTranslation_joint_contMDiff j τ θ a b).comp
    (smallTimeInsert_contMDiff j s)

/-- A genuine homeomorphism with the explicit negative-time inverse. -/
def localizedCollarHomeomorph (j : Kind) (τ θ : ℝ) (a b : CollarRadius j) (s : ℝ) :
    SpecialEllipticPiece j ≃ₜ SpecialEllipticPiece j where
  toFun := localizedCollarTranslation j τ θ a b s
  invFun := localizedCollarTranslation j τ θ a b (-s)
  left_inv y := by
    rw [← localizedCollarTranslation_add, neg_add_cancel, localizedCollarTranslation_zero]
  right_inv y := by
    rw [← localizedCollarTranslation_add, add_neg_cancel, localizedCollarTranslation_zero]
  continuous_toFun := (localizedCollarTranslation_contMDiff j τ θ a b s).continuous
  continuous_invFun := (localizedCollarTranslation_contMDiff j τ θ a b (-s)).continuous

/-- The localized map is a real smooth diffeomorphism of the unchanged small piece. -/
def localizedCollarDiffeomorph (j : Kind) (τ θ : ℝ) (a b : CollarRadius j) (s : ℝ) :
    Diffeomorph IR IR (SpecialEllipticPiece j) (SpecialEllipticPiece j) ∞ where
  toEquiv := (localizedCollarHomeomorph j τ θ a b s).toEquiv
  contMDiff_toFun := localizedCollarTranslation_contMDiff j τ θ a b s
  contMDiff_invFun := localizedCollarTranslation_contMDiff j τ θ a b (-s)

@[simp] theorem localizedCollarDiffeomorph_apply (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    localizedCollarDiffeomorph j τ θ a b s y = localizedCollarTranslation j τ θ a b s y :=
  rfl

@[simp] theorem localizedCollarDiffeomorph_symm_apply (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    (localizedCollarDiffeomorph j τ θ a b s).symm y =
      localizedCollarTranslation j τ θ a b (-s) y := rfl

/-- The entire inner neighborhood remains fixed after the additional localization. -/
theorem localizedCollarTranslation_eq_self_inner (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j)
    (hy : smallRootSquared j y ≤ (a : ℝ) ^ 2 / 4) :
    localizedCollarTranslation j τ θ a b s y = y :=
  smallCollarHomeomorph_eq_self_inner j τ θ a _ y hy

/-- The localized map is the identity at and beyond the permitted outer radius. -/
theorem localizedCollarTranslation_eq_self_outer (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (hab : (a : ℝ) < b) (s : ℝ) (y : SpecialEllipticPiece j)
    (hy : (b : ℝ) ^ 2 ≤ smallRootSquared j y) :
    localizedCollarTranslation j τ θ a b s y = y := by
  rw [localizedCollarTranslation, smallCollarCutoff,
    outerRadialCutoff_eq_zero_of_ge a.property.1.le hab hy, mul_zero,
    smallCollarHomeomorph_zero]

theorem localizedCollarTranslation_projectionToBase (j : Kind) (τ θ : ℝ)
    (a b : CollarRadius j) (s : ℝ) (y : SpecialEllipticPiece j) :
    specialEllipticPieceProjectionToBase j (localizedCollarTranslation j τ θ a b s y) =
      specialEllipticPieceProjectionToBase j y :=
  smallCollarHomeomorph_projectionToBase j τ θ a _ y

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
