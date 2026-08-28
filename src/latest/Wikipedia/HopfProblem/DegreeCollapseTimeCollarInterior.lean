import Wikipedia.HopfProblem.DegreeCollapseTimeCollarHalf

/-!
# The actual interior and half have the same homotopy type for any time collar

Clamp toward half the collar width. Time never decreases, so the homotopy
stays in the half and preserves its strict interior. At the endpoint all
half points have positive time. Both inverse homotopies use this one map.
-/

noncomputable section

open Set Function ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open ReflectedCylinder (interiorSlideTime interiorSlideTime_bounds)
open SingularMayerVietoris PeriodTorusHigherHomology

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def positiveInterior : TopologicalSpace.Opens M :=
  ⟨{p | 0 < t p}, isOpen_lt continuous_const C.continuous_time⟩

def interiorToHalf : C(C.positiveInterior, NonnegativeHalf t) :=
  ⟨fun p ↦ ⟨p.val, p.property.le⟩, continuous_subtype_val.subtype_mk _⟩

theorem interiorToHalf_inclusion :
    (halfInclusion t).comp C.interiorToHalf =
      subtypeInclusion (C.positiveInterior : Set M) := rfl

def halfInteriorClamp : C(unitInterval × NonnegativeHalf t, C.positiveOpen) :=
  ⟨fun q ↦ C.clampSlide (C.width / 2) (half_lt_self C.width_pos)
      (q.1, C.halfToPositive q.2),
    (C.clampSlide (C.width / 2) (half_lt_self C.width_pos)).continuous.comp
      (continuous_fst.prodMk (C.halfToPositive.continuous.comp continuous_snd))⟩

theorem halfInteriorClamp_time (s : unitInterval) (p : NonnegativeHalf t) :
    t (C.halfInteriorClamp (s, p)).val = interiorSlideTime (C.width / 2) s (t p.val) :=
  C.clampSlide_time (C.width / 2) (half_lt_self C.width_pos) s (C.halfToPositive p)

theorem halfInteriorClamp_nonneg (s : unitInterval) (p : NonnegativeHalf t) :
    0 ≤ t (C.halfInteriorClamp (s, p)).val := by
  rw [C.halfInteriorClamp_time]
  exact p.property.trans (interiorSlideTime_bounds (C.width / 2) s (t p.val)).1

theorem halfInteriorClamp_positive (s : unitInterval) (p : C.positiveInterior) :
    0 < t (C.halfInteriorClamp (s, C.interiorToHalf p)).val := by
  rw [C.halfInteriorClamp_time]
  exact p.property.trans_le (interiorSlideTime_bounds (C.width / 2) s (t p.val)).1

theorem halfInteriorClamp_one_positive (p : NonnegativeHalf t) :
    0 < t (C.halfInteriorClamp (1, p)).val := by
  change 0 < t (C.clampSlide (C.width / 2) (half_lt_self C.width_pos)
    (1, C.halfToPositive p)).val
  rw [C.clampSlide_one_time]
  exact (half_pos C.width_pos).trans_le (le_max_right _ _)

theorem halfInteriorClamp_zero (p : NonnegativeHalf t) :
    C.halfInteriorClamp (0, p) = C.halfToPositive p :=
  C.clampSlide_zero (C.width / 2) (half_lt_self C.width_pos) (C.halfToPositive p)

def halfInteriorSlideMap : C(unitInterval × NonnegativeHalf t, NonnegativeHalf t) :=
  ⟨fun q ↦ ⟨(C.halfInteriorClamp q).val, C.halfInteriorClamp_nonneg q.1 q.2⟩,
    (continuous_subtype_val.comp C.halfInteriorClamp.continuous).subtype_mk _⟩

def halfToInterior : C(NonnegativeHalf t, C.positiveInterior) :=
  ⟨fun p ↦ ⟨(C.halfInteriorClamp (1, p)).val, C.halfInteriorClamp_one_positive p⟩,
    (continuous_subtype_val.comp (C.halfInteriorClamp.continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _⟩

def halfInteriorSlide : (ContinuousMap.id (NonnegativeHalf t)).Homotopy
    (C.interiorToHalf.comp C.halfToInterior) where
  toContinuousMap := C.halfInteriorSlideMap
  map_zero_left p :=
    Subtype.ext (congrArg (fun z : C.positiveOpen ↦ z.val) (C.halfInteriorClamp_zero p))
  map_one_left _ := rfl

def interiorHalfSlide : (ContinuousMap.id C.positiveInterior).Homotopy
    (C.halfToInterior.comp C.interiorToHalf) where
  toFun q := ⟨(C.halfInteriorClamp (q.1, C.interiorToHalf q.2)).val,
    C.halfInteriorClamp_positive q.1 q.2⟩
  continuous_toFun :=
    (continuous_subtype_val.comp (C.halfInteriorClamp.continuous.comp
      (continuous_fst.prodMk (C.interiorToHalf.continuous.comp continuous_snd)))).subtype_mk _
  map_zero_left p :=
    Subtype.ext (congrArg (fun z : C.positiveOpen ↦ z.val)
      (C.halfInteriorClamp_zero (C.interiorToHalf p)))
  map_one_left _ := rfl

def interiorHalfHomotopyEquiv : C.positiveInterior ≃ₕ NonnegativeHalf t where
  toFun := C.interiorToHalf
  invFun := C.halfToInterior
  left_inv := ⟨C.interiorHalfSlide.symm⟩
  right_inv := ⟨C.halfInteriorSlide.symm⟩

theorem interiorToHalf_homology_bijective (k : ℕ) :
    Bijective (singularHomologyMap C.interiorToHalf k) :=
  (homotopyEquivHomologyEquiv C.interiorHalfHomotopyEquiv k).bijective

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
