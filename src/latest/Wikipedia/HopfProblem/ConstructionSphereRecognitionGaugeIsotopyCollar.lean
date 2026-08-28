import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCollarVector
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCapSmooth

/-!
# An explicit smooth extension of the boundary isotopy across the cap

The extension is constructed on the original period-vector cover and then
descended to the original finite quotient.  It uses the explicit smooth
cutoff vector, fixes the base, and is the identity on an actual
neighborhood of the cap core.  Its negative-time inverse is literal.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods ThreefoldOverlapMappingTorus

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)
local notation "AC" => ThreefoldOverlapMappingTorus.Circle

variable {j : Kind} (D : Equivariant.Data j) (τ θ a : ℝ) (ha : 0 < a)

local instance collarFillingChartedSpace :
    ChartedSpace FamilyModel (D.Space j.twist (mainTwist_admissible j)) :=
  D.chartedSpace j.twist (mainTwist_admissible j)

attribute [local instance] capTimeFillingChartedSpace

/-- The explicit extension on the original full cap. -/
def collarTranslation (s : ℝ) :
    D.Space j.twist (mainTwist_admissible j) ≃ₜ D.Space j.twist (mainTwist_admissible j) :=
  capTranslation D (collarVector j τ θ a) (collarVector_contMDiff j τ θ ha)
    (collarVector_rotation j τ θ a) s

@[simp] theorem collarTranslation_quotient (s : ℝ) (z : Disc) (x : RealTorus₄) :
    collarTranslation D τ θ a ha s (D.quotient j.twist (mainTwist_admissible j) (z, x)) =
      D.quotient j.twist (mainTwist_admissible j)
        (z, x + standardLattice.mkQ (s • collarVector j τ θ a z)) := rfl

@[simp] theorem collarTranslation_symm_apply (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    (collarTranslation D τ θ a ha s).symm y = collarTranslation D τ θ a ha (-s) y :=
  capTranslation_symm_apply D _ _ _ s y

@[simp] theorem collarTranslation_zero (y : D.Space j.twist (mainTwist_admissible j)) :
    collarTranslation D τ θ a ha 0 y = y := capTranslation_zero D _ _ _ y

theorem collarTranslation_add (s r : ℝ) (y : D.Space j.twist (mainTwist_admissible j)) :
    collarTranslation D τ θ a ha (s + r) y =
      collarTranslation D τ θ a ha s (collarTranslation D τ θ a ha r y) :=
  capTranslation_add D _ _ _ s r y

theorem collarTranslation_projection (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    D.projection j.twist (mainTwist_admissible j) (collarTranslation D τ θ a ha s y) =
      D.projection j.twist (mainTwist_admissible j) y :=
  capTranslation_projection D _ _ _ s y

theorem collarTranslation_root_norm (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    ‖((EllipticFullProduct.fillingProductHomeomorph D
      (collarTranslation D τ θ a ha s y)).1 : ℂ)‖ =
      ‖((EllipticFullProduct.fillingProductHomeomorph D y).1 : ℂ)‖ :=
  capTranslation_root_norm D _ _ _ s y

/-- Joint real smoothness uses the unchanged original finite-quotient atlas. -/
theorem collarTranslation_joint_contMDiff :
    ContMDiff IT IR ∞ (fun p : ℝ × D.Space j.twist (mainTwist_admissible j) =>
      collarTranslation D τ θ a ha p.1 p.2) :=
  capTranslation_joint_contMDiff D _ _ _

/-- Each time slice is a genuine diffeomorphism of the original cap. -/
def collarDiffeomorph (s : ℝ) :
    Diffeomorph IR IR (D.Space j.twist (mainTwist_admissible j))
      (D.Space j.twist (mainTwist_admissible j)) ∞ :=
  capTranslationDiffeomorph D (collarVector j τ θ a) (collarVector_contMDiff j τ θ ha)
    (collarVector_rotation j τ θ a) s

@[simp] theorem collarDiffeomorph_apply (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    collarDiffeomorph D τ θ a ha s y = collarTranslation D τ θ a ha s y := rfl

@[simp] theorem collarDiffeomorph_symm_apply (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    (collarDiffeomorph D τ θ a ha s).symm y = collarTranslation D τ θ a ha (-s) y :=
  collarTranslation_symm_apply D τ θ a ha s y

/-- The explicit inner neighborhood of the actual cap core is fixed pointwise. -/
theorem collarTranslation_eq_self_inner (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j))
    (hy : ‖((EllipticFullProduct.fillingProductHomeomorph D y).1 : ℂ)‖ ^ 2 ≤ a ^ 2 / 4) :
    collarTranslation D τ θ a ha s y = y := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rw [EllipticFullProduct.fillingProductHomeomorph_quotient_norm] at hy
  rw [collarTranslation_quotient, collarVector_eq_zero_inner j τ θ a z hy,
    smul_zero, map_zero, add_zero]

/-- The extension also fixes the outer part of the original full cap. -/
theorem collarTranslation_eq_self_outer (ha1 : a < 1) (s : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j))
    (hy : (3 + a ^ 2) / 4 ≤
      ‖((EllipticFullProduct.fillingProductHomeomorph D y).1 : ℂ)‖ ^ 2) :
    collarTranslation D τ θ a ha s y = y := by
  obtain ⟨⟨z, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rw [EllipticFullProduct.fillingProductHomeomorph_quotient_norm] at hy
  rw [collarTranslation_quotient, collarVector_eq_zero_outer j τ θ ha ha1 z hy,
    smul_zero, map_zero, add_zero]

/-- The original boundary representatives carry exactly the original boundary correction. -/
theorem collarTranslation_boundary_quotient (r : ℝ) (b : Radius j.order r)
    (s t : ℝ) (x : RealTorus₄) :
    collarTranslation D τ θ b b.property.1 s
        (D.quotient j.twist (mainTwist_admissible j)
          (root j.order r b (((t + θ) / j.order : ℝ) : AC), x)) =
      D.quotient j.twist (mainTwist_admissible j)
        (root j.order r b (((t + θ) / j.order : ℝ) : AC),
          x + standardLattice.mkQ (s • correction j τ t)) := by
  rw [collarTranslation_quotient, collarVector_boundary]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
