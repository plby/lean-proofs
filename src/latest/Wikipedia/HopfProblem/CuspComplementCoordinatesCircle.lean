import Wikipedia.HopfProblem.CuspComplementCoordinates

/-!
# The original circle action on the finite cusp-cap coordinates

The literal diagonal action of weights `(-1, 0, 1)` preserves each closed
coordinate polydisc and the original cubic time. It therefore acts on the
finite compact coordinate domain and intertwines its map to the unchanged
threefold with the original multiplicative action.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspComplement.Coordinates

open ToricCharts ToricFan
open SpecialPeriods SpecialPeriods.Threefold VerticalAction

local notation "CD" => CuspGeometry.data
local notation "E₃" => CoordinateSpace 3

/-- The actual circle diagonal preserves each original coordinate's norm. -/
theorem diagonal_coordinate_norm (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : E₃) (j : Fin 3) : ‖FixedCoordinates.diagonal u z j‖ = ‖z j‖ := by
  rw [FixedCoordinates.diagonal_apply]
  fin_cases j
  · change ‖(u : ℂ)⁻¹ * z 0‖ = ‖z 0‖
    rw [norm_mul, norm_inv, hu, inv_one, one_mul]
  · rfl
  · change ‖(u : ℂ) * z 2‖ = ‖z 2‖
    rw [norm_mul, hu, one_mul]

/-- This is the native supremum norm of the original closed polydisc. -/
theorem diagonal_norm (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : E₃) :
    ‖FixedCoordinates.diagonal u z‖ = ‖z‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro j
    rw [diagonal_coordinate_norm u hu]
    exact norm_le_pi_norm z j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (FixedCoordinates.diagonal u z))).mpr
    intro j
    rw [← diagonal_coordinate_norm u hu z j]
    exact norm_le_pi_norm (FixedCoordinates.diagonal u z) j

/-- The literal native diagonal on each closed coordinate cap. -/
def coordinateAction (η : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : CoordinateCap η) : CoordinateCap η :=
  ⟨FixedCoordinates.diagonal u z, by
    constructor
    · rw [diagonal_norm u hu]
      exact z.property.1
    · rw [FixedCoordinates.time_diagonal]
      exact z.property.2⟩

@[simp] theorem coordinateAction_coe (η : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : CoordinateCap η) :
    (coordinateAction η u hu z : E₃) = FixedCoordinates.diagonal u z := rfl

@[simp] theorem coordinateAction_time (η : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : CoordinateCap η) :
    Triangle.time (coordinateAction η u hu z) = Triangle.time z :=
  FixedCoordinates.time_diagonal u z

theorem coordinateAction_continuous (η : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    Continuous (coordinateAction η u hu) :=
  ((FixedCoordinates.diagonal u).continuous.comp continuous_subtype_val).subtype_mk
    (fun z => (coordinateAction η u hu z).property)

/-- The action keeps the original finite triangle index unchanged. -/
def capAction (η : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : Index × CoordinateCap η) : Index × CoordinateCap η :=
  (p.1, coordinateAction η u hu p.2)

@[simp] theorem capAction_index (η : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : Index × CoordinateCap η) : (capAction η u hu p).1 = p.1 := rfl

theorem capAction_continuous (η : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    Continuous (capAction η u hu) :=
  continuous_fst.prodMk ((coordinateAction_continuous η u hu).comp continuous_snd)

/-- Inclusion into the open coordinate domain commutes literally with the native action. -/
theorem coordinateIntoDomain_coordinateAction (η : ℝ) (hη : η < (CD).radius)
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : CoordinateCap η) :
    coordinateIntoDomain η hη (coordinateAction η u hu z) =
      FixedCoordinates.coordinateAction u (coordinateIntoDomain η hη z) := rfl

/-- Exact equivariance through the actual cusp quotient and the original global gluing. -/
theorem toGlobal_capAction (η : ℝ) (hη : η < (CD).radius)
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (p : Index × CoordinateCap η) :
    toGlobal η hη (capAction η u hu p) = actionBiholomorph u (toGlobal η hη p) := by
  change FixedCoordinates.globalMap (triangle p.1)
    (coordinateIntoDomain η hη (coordinateAction η u hu p.2)) = _
  rw [coordinateIntoDomain_coordinateAction]
  exact (FixedCoordinates.globalMap_coordinateAction u (triangle p.1)
    (coordinateIntoDomain η hη p.2)).symm

end Wikipedia.HopfProblem.CuspComplement.Coordinates
