import Wikipedia.HopfProblem.DegreeCollapseTimeCollarClamp

/-!
# The literal nonnegative half is a deformation retract of its open enlargement

The collar clamp at zero fixes the entire original nonnegative half.
Its endpoint is the actual retraction, and the inverse of the resulting
homotopy equivalence is the literal half inclusion.
-/

noncomputable section

open Set Function ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

abbrev NonnegativeHalf (t : M → ℝ) := {p : M // 0 ≤ t p}

def halfInclusion (t : M → ℝ) : C(NonnegativeHalf t, M) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def halfToPositive : C(NonnegativeHalf t, C.positiveOpen) :=
  ⟨fun p ↦ ⟨p.val, (show -C.width / 2 < 0 by linarith [C.width_pos]).trans_le p.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem clampSlide_one_nonneg (p : C.positiveOpen) :
    0 ≤ t (C.clampSlide 0 C.width_pos (1, p)).val := by
  rw [C.clampSlide_one_time]
  exact le_max_right _ _

def positiveHalfRetraction : C(C.positiveOpen, NonnegativeHalf t) where
  toFun p := ⟨(C.clampSlide 0 C.width_pos (1, p)).val, C.clampSlide_one_nonneg p⟩
  continuous_toFun :=
    (continuous_subtype_val.comp ((C.clampSlide 0 C.width_pos).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _

theorem positiveHalfRetraction_halfToPositive (p : NonnegativeHalf t) :
    C.positiveHalfRetraction (C.halfToPositive p) = p := by
  apply Subtype.ext
  exact congrArg (fun z : C.positiveOpen ↦ z.val)
    (C.clampSlide_fixed 0 C.width_pos 1 (C.halfToPositive p) p.property)

def positiveHalfSlide : (ContinuousMap.id C.positiveOpen).Homotopy
    (C.halfToPositive.comp C.positiveHalfRetraction) where
  toContinuousMap := C.clampSlide 0 C.width_pos
  map_zero_left := C.clampSlide_zero 0 C.width_pos
  map_one_left _ := rfl

def positiveHalfHomotopyEquiv : C.positiveOpen ≃ₕ NonnegativeHalf t where
  toFun := C.positiveHalfRetraction
  invFun := C.halfToPositive
  left_inv := ⟨C.positiveHalfSlide.symm⟩
  right_inv := by
    have he : C.positiveHalfRetraction.comp C.halfToPositive =
        ContinuousMap.id (NonnegativeHalf t) :=
      ContinuousMap.ext C.positiveHalfRetraction_halfToPositive
    rw [he]

theorem positiveHalf_inverse_inclusion :
    (SingularMayerVietoris.subtypeInclusion (C.positiveOpen : Set M)).comp
      C.positiveHalfHomotopyEquiv.invFun = halfInclusion t := rfl

theorem halfToPositive_homology_bijective (k : ℕ) :
    Bijective (SingularMayerVietoris.singularHomologyMap C.halfToPositive k) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
    C.positiveHalfHomotopyEquiv.symm k).bijective

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
