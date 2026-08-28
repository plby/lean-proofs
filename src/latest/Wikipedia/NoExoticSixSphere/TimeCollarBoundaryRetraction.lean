import Wikipedia.NoExoticSixSphere.TimeCollarCompactCores

/-!
# The actual positive boundary collar retracts onto the literal zero boundary

In the supplied time coordinates, multiply time by `1 - s` and retain the
boundary coordinate. Time stays nonnegative and below the collar cutoff.
This gives a genuine deformation that fixes every zero-boundary point.
-/

noncomputable section

open Set Function ContinuousMap
open scoped unitInterval

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B) (δ : ℝ) (hδw : δ ≤ C.width)

def collarToBand : C(collarRegion C δ, TimeBand t C.width) :=
  ⟨fun p ↦ ⟨p.val.val, (neg_lt_zero.mpr C.width_pos).trans_le p.val.property,
    p.property.trans_le hδw⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def collarSlideBand : C(unitInterval × collarRegion C δ, TimeBand t C.width) where
  toFun p := C.coordinates.symm
    (⟨(1 - (p.1 : ℝ)) * t p.2.val.val,
      (neg_lt_zero.mpr C.width_pos).trans_le
        (mul_nonneg (sub_nonneg.mpr p.1.property.2) p.2.val.property),
      (show (1 - (p.1 : ℝ)) * t p.2.val.val ≤ t p.2.val.val by
        nlinarith [p.1.property.1, p.2.val.property]).trans_lt (p.2.property.trans_le hδw)⟩,
      (C.coordinates (collarToBand C δ hδw p.2)).2)
  continuous_toFun := C.coordinates.symm.continuous.comp
    ((((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (C.continuous_time.comp
        (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_snd)))).subtype_mk _).prodMk
      (continuous_snd.comp (C.coordinates.continuous.comp
        ((collarToBand C δ hδw).continuous.comp continuous_snd))))

theorem collarSlideBand_time (s : unitInterval) (p : collarRegion C δ) :
    t (collarSlideBand C δ hδw (s, p)).val = (1 - (s : ℝ)) * t p.val.val :=
  C.inverse_time _

theorem collarSlideBand_zero (p : collarRegion C δ) :
    collarSlideBand C δ hδw (0, p) = collarToBand C δ hδw p := by
  apply C.coordinates.injective
  change C.coordinates (C.coordinates.symm _) = _
  rw [C.coordinates.apply_symm_apply]
  apply Prod.ext
  · apply Subtype.ext
    change (1 - (0 : ℝ)) * t p.val.val = (C.coordinates (collarToBand C δ hδw p)).1.val
    rw [C.coordinate_time]
    simp only [sub_zero, one_mul]
    rfl
  · rfl

theorem collarSlideBand_fixed (s : unitInterval) (p : collarRegion C δ)
    (hp : p.val ∈ boundary t) : collarSlideBand C δ hδw (s, p) = collarToBand C δ hδw p := by
  apply C.coordinates.injective
  change C.coordinates (C.coordinates.symm _) = _
  rw [C.coordinates.apply_symm_apply]
  apply Prod.ext
  · apply Subtype.ext
    change (1 - (s : ℝ)) * t p.val.val = (C.coordinates (collarToBand C δ hδw p)).1.val
    rw [C.coordinate_time]
    change (1 - (s : ℝ)) * t p.val.val = t p.val.val
    change t p.val.val = 0 at hp
    rw [hp, mul_zero]
  · rfl

theorem collarSlideBand_nonneg (s : unitInterval) (p : collarRegion C δ) :
    0 ≤ t (collarSlideBand C δ hδw (s, p)).val := by
  rw [collarSlideBand_time C δ hδw s p]
  exact mul_nonneg (sub_nonneg.mpr s.property.2) p.val.property

theorem collarSlideBand_lt (s : unitInterval) (p : collarRegion C δ) :
    t (collarSlideBand C δ hδw (s, p)).val < δ := by
  rw [collarSlideBand_time C δ hδw s p]
  exact (show (1 - (s : ℝ)) * t p.val.val ≤ t p.val.val by
    nlinarith [s.property.1, p.val.property]).trans_lt p.property

def collarSlide : C(unitInterval × collarRegion C δ, collarRegion C δ) where
  toFun p := ⟨⟨(collarSlideBand C δ hδw p).val, collarSlideBand_nonneg C δ hδw p.1 p.2⟩,
    collarSlideBand_lt C δ hδw p.1 p.2⟩
  continuous_toFun := ((continuous_subtype_val.comp
    (collarSlideBand C δ hδw).continuous).subtype_mk _).subtype_mk _

theorem collarSlide_zero (p : collarRegion C δ) : collarSlide C δ hδw (0, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : TimeBand t C.width ↦ q.val) (collarSlideBand_zero C δ hδw p)

theorem collarSlide_one_boundary (p : collarRegion C δ) :
    (collarSlide C δ hδw (1, p)).val ∈ boundary t := by
  change t (collarSlideBand C δ hδw (1, p)).val = 0
  rw [collarSlideBand_time C δ hδw 1 p]
  change (1 - (1 : ℝ)) * t p.val.val = 0
  rw [sub_self, zero_mul]

theorem collarSlide_fixed (p : collarRegion C δ) (hp : p.val ∈ boundary t) (s : unitInterval) :
    collarSlide C δ hδw (s, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : TimeBand t C.width ↦ q.val) (collarSlideBand_fixed C δ hδw s p hp)

def collarRetraction : C(collarRegion C δ, boundary t) where
  toFun p := ⟨(collarSlide C δ hδw (1, p)).val, collarSlide_one_boundary C δ hδw p⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((collarSlide C δ hδw).continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _

variable (hδ : 0 < δ)

def collarBoundaryInclusion : C(boundary t, collarRegion C δ) :=
  ⟨fun p ↦ ⟨p.val, boundary_subset_collar C δ hδ p.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem collarRetraction_inclusion :
    (collarRetraction C δ hδw).comp (collarBoundaryInclusion C δ hδ) =
      ContinuousMap.id (boundary t) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun q : collarRegion C δ ↦ q.val)
    (collarSlide_fixed C δ hδw (collarBoundaryInclusion C δ hδ p) p.property 1)

def collarDeformation : (ContinuousMap.id (collarRegion C δ)).Homotopy
    ((collarBoundaryInclusion C δ hδ).comp (collarRetraction C δ hδw)) where
  toContinuousMap := collarSlide C δ hδw
  map_zero_left := collarSlide_zero C δ hδw
  map_one_left _ := rfl

def boundaryCollarHomotopyEquiv : boundary t ≃ₕ collarRegion C δ where
  toFun := collarBoundaryInclusion C δ hδ
  invFun := collarRetraction C δ hδw
  left_inv := by rw [collarRetraction_inclusion]
  right_inv := ⟨(collarDeformation C δ hδw hδ).symm⟩

end NoExoticSixSphere.TimeCollarDuality
