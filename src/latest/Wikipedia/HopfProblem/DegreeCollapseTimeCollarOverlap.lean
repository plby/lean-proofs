import Wikipedia.HopfProblem.DegreeCollapseTimeCollarHalf

/-!
# Both open halves cover the space and their actual overlap retracts to the boundary

Reverse the time coordinate to obtain the negative half's collar. The
intersection of the two original open enlargements is a smaller literal
time band. Contracting its interval factor gives the required boundary
homotopy type, without using a reflection of the ambient manifold.
-/

noncomputable section

open Set Function ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem neg_mem_symmetric_band_iff (ρ u : ℝ) :
    -u ∈ Ioo (-ρ) ρ ↔ u ∈ Ioo (-ρ) ρ := by
  constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩

def reverseBandHomeomorph : TimeBand (fun p ↦ -t p) C.width ≃ₜ TimeBand t C.width where
  toFun p := ⟨p.val, (neg_mem_symmetric_band_iff C.width (t p.val)).mp p.property⟩
  invFun p := ⟨p.val, (neg_mem_symmetric_band_iff C.width (t p.val)).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def reverseIntervalHomeomorph : Ioo (-C.width) C.width ≃ₜ Ioo (-C.width) C.width where
  toFun p := ⟨-p.val, (neg_mem_symmetric_band_iff C.width p.val).mpr p.property⟩
  invFun p := ⟨-p.val, (neg_mem_symmetric_band_iff C.width p.val).mpr p.property⟩
  left_inv p := Subtype.ext (neg_neg p.val)
  right_inv p := Subtype.ext (neg_neg p.val)
  continuous_toFun := continuous_subtype_val.neg.subtype_mk _
  continuous_invFun := continuous_subtype_val.neg.subtype_mk _

def reverse : TimeCollar (fun p ↦ -t p) B where
  width := C.width
  width_pos := C.width_pos
  continuous_time := C.continuous_time.neg
  coordinates := C.reverseBandHomeomorph.trans
    (C.coordinates.trans (C.reverseIntervalHomeomorph.prodCongr (Homeomorph.refl B)))
  coordinate_time p := by
    change -(C.coordinates (C.reverseBandHomeomorph p)).1.val = -t p.val
    rw [C.coordinate_time]
    rfl

def bandProjection : C(TimeBand t C.width, B) :=
  ⟨fun p ↦ (C.coordinates p).2, continuous_snd.comp C.coordinates.continuous⟩

def bandSection : C(B, TimeBand t C.width) :=
  ⟨C.zeroPoint, C.coordinates.symm.continuous.comp (continuous_const.prodMk continuous_id)⟩

theorem contractTime_mem (s : unitInterval) (p : TimeBand t C.width) :
    (1 - s.val) * t p.val ∈ Ioo (-C.width) C.width := by
  have hs0 : 0 ≤ 1 - s.val := sub_nonneg.mpr s.property.2
  have hs1 : 1 - s.val ≤ 1 := by linarith [s.property.1]
  apply abs_lt.mp
  calc
    |(1 - s.val) * t p.val| = (1 - s.val) * |t p.val| := by
      rw [abs_mul, abs_of_nonneg hs0]
    _ ≤ |t p.val| := mul_le_of_le_one_left (abs_nonneg _) hs1
    _ < C.width := abs_lt.mpr p.property

def bandContract : (ContinuousMap.id (TimeBand t C.width)).Homotopy
    (C.bandSection.comp C.bandProjection) where
  toFun q := C.coordinates.symm
    (⟨(1 - q.1.val) * t q.2.val, C.contractTime_mem q.1 q.2⟩, (C.coordinates q.2).2)
  continuous_toFun := by
    apply C.coordinates.symm.continuous.comp
    apply Continuous.prodMk
    · exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (C.continuous_time.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
    · exact continuous_snd.comp (C.coordinates.continuous.comp continuous_snd)
  map_zero_left p := by
    apply C.coordinates.injective
    change C.coordinates (C.coordinates.symm _) = C.coordinates p
    rw [C.coordinates.apply_symm_apply]
    apply Prod.ext
    · apply Subtype.ext
      simpa using (C.coordinate_time p).symm
    · rfl
  map_one_left p := by
    apply C.coordinates.injective
    change C.coordinates (C.coordinates.symm _) = C.coordinates (C.coordinates.symm _)
    rw [C.coordinates.apply_symm_apply, C.coordinates.apply_symm_apply]
    apply Prod.ext
    · exact Subtype.ext (by simp)
    · rfl

def bandHomotopyEquiv : TimeBand t C.width ≃ₕ B where
  toFun := C.bandProjection
  invFun := C.bandSection
  left_inv := ⟨C.bandContract.symm⟩
  right_inv := by
    have he : C.bandProjection.comp C.bandSection = ContinuousMap.id B := by
      apply ContinuousMap.ext
      intro b
      change (C.coordinates (C.coordinates.symm _)).2 = b
      rw [C.coordinates.apply_symm_apply]
    rw [he]

abbrev overlap := (C.positiveOpen : Set M) ∩ (C.reverse.positiveOpen : Set M)

theorem overlap_iff_band (p : M) :
    p ∈ C.overlap ↔ t p ∈ Ioo (-(C.width / 2)) (C.width / 2) := by
  change (-C.width / 2 < t p ∧ -C.width / 2 < -t p) ↔ _
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

def overlapBandHomeomorph : C.overlap ≃ₜ TimeBand t (C.width / 2) where
  toFun p := ⟨p.val, (C.overlap_iff_band p.val).mp p.property⟩
  invFun p := ⟨p.val, (C.overlap_iff_band p.val).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def overlapHomotopyEquiv : C.overlap ≃ₕ B :=
  C.overlapBandHomeomorph.toHomotopyEquiv.trans
    (C.restrict (C.width / 2) (half_pos C.width_pos)
      (half_lt_self C.width_pos).le).bandHomotopyEquiv

theorem open_halves_cover : (C.positiveOpen : Set M) ∪ (C.reverse.positiveOpen : Set M) = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  change -C.width / 2 < t p ∨ -C.width / 2 < -t p
  by_cases hp : -C.width / 2 < t p
  · exact Or.inl hp
  · exact Or.inr (by linarith [C.width_pos])

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
