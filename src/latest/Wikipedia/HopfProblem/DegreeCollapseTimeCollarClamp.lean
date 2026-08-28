import Wikipedia.HopfProblem.DegreeCollapseTimeCollar
import Wikipedia.HopfProblem.DegreeCollapseReflectedInteriorHalf

/-!
# A continuous clamp homotopy in an arbitrary explicit time collar

The scalar clamp is the already proved straight interpolation to max(t,c).
Inside the actual collar it changes only time. Outside the part of the
collar where it can change a point, it is the identity. Agreement on an
open cover supplies a global continuous homotopy on the enlarged half.
No reflected presentation of the ambient space is used.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open ReflectedCylinder (interiorSlideTime interiorSlideTime_bounds interiorSlideTime_of_ge)

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def positiveOpen : TopologicalSpace.Opens M :=
  ⟨{p | -C.width / 2 < t p}, isOpen_lt continuous_const C.continuous_time⟩

theorem bandSlideTime_mem (c : ℝ) (hc : c < C.width)
    (s : unitInterval) (p : TimeBand t C.width) :
    interiorSlideTime c s (t p.val) ∈ Ioo (-C.width) C.width :=
  ⟨p.property.1.trans_le (interiorSlideTime_bounds c s (t p.val)).1,
    (interiorSlideTime_bounds c s (t p.val)).2.trans_lt (max_lt p.property.2 hc)⟩

def bandSlide (c : ℝ) (hc : c < C.width) :
    C(unitInterval × TimeBand t C.width, TimeBand t C.width) where
  toFun q := C.coordinates.symm
    (⟨interiorSlideTime c q.1 (t q.2.val), C.bandSlideTime_mem c hc q.1 q.2⟩,
      (C.coordinates q.2).2)
  continuous_toFun := by
    apply C.coordinates.symm.continuous.comp
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      have ht : Continuous (fun q : unitInterval × TimeBand t C.width ↦ t q.2.val) :=
        C.continuous_time.comp (continuous_subtype_val.comp continuous_snd)
      have hs : Continuous (fun q : unitInterval × TimeBand t C.width ↦ q.1.val) :=
        continuous_subtype_val.comp continuous_fst
      exact ((continuous_const.sub hs).mul ht).add (hs.mul (ht.max continuous_const))
    · exact continuous_snd.comp (C.coordinates.continuous.comp continuous_snd)

theorem bandSlide_time (c : ℝ) (hc : c < C.width)
    (s : unitInterval) (p : TimeBand t C.width) :
    t (C.bandSlide c hc (s, p)).val = interiorSlideTime c s (t p.val) :=
  C.inverse_time _

theorem bandSlide_fixed (c : ℝ) (hc : c < C.width)
    (s : unitInterval) (p : TimeBand t C.width) (hp : c ≤ t p.val) :
    C.bandSlide c hc (s, p) = p := by
  apply C.coordinates.injective
  change C.coordinates (C.coordinates.symm _) = C.coordinates p
  rw [C.coordinates.apply_symm_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (interiorSlideTime_of_ge c s (t p.val) hp).trans (C.coordinate_time p).symm
  · rfl

theorem bandSlide_zero (c : ℝ) (hc : c < C.width) (p : TimeBand t C.width) :
    C.bandSlide c hc (0, p) = p := by
  apply C.coordinates.injective
  change C.coordinates (C.coordinates.symm _) = C.coordinates p
  rw [C.coordinates.apply_symm_apply]
  apply Prod.ext
  · apply Subtype.ext
    simpa [interiorSlideTime] using (C.coordinate_time p).symm
  · rfl

def clampRegion (c : ℝ) : Bool → Set (unitInterval × C.positiveOpen)
  | false => {q | c < t q.2.val}
  | true => {q | t q.2.val < C.width}

def clampBandPoint (c : ℝ) (q : C.clampRegion c true) : TimeBand t C.width :=
  ⟨q.val.2.val, by
    have hp : -C.width / 2 < t q.val.2.val := q.val.2.property
    exact ⟨by linarith [C.width_pos], q.property⟩⟩

def clampBandLocal (c : ℝ) (hc : c < C.width) :
    C(C.clampRegion c true, C.positiveOpen) where
  toFun q := ⟨(C.bandSlide c hc (q.val.1, C.clampBandPoint c q)).val, by
    change -C.width / 2 < t (C.bandSlide c hc (q.val.1, C.clampBandPoint c q)).val
    rw [C.bandSlide_time]
    exact q.val.2.property.trans_le (interiorSlideTime_bounds c q.val.1 _).1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp ((C.bandSlide c hc).continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp
          continuous_subtype_val)).subtype_mk _)))

theorem clampBandLocal_fixed (c : ℝ) (hc : c < C.width)
    (q : C.clampRegion c true) (hq : c ≤ t q.val.2.val) :
    C.clampBandLocal c hc q = q.val.2 :=
  Subtype.ext (congrArg (fun z : TimeBand t C.width ↦ z.val)
    (C.bandSlide_fixed c hc q.val.1 (C.clampBandPoint c q) hq))

def clampLocal (c : ℝ) (hc : c < C.width) (i : Bool) :
    C(C.clampRegion c i, C.positiveOpen) := match i with
  | false => ⟨fun q ↦ q.val.2, continuous_snd.comp continuous_subtype_val⟩
  | true => C.clampBandLocal c hc

theorem clampLocal_agree (c : ℝ) (hc : c < C.width)
    (i j : Bool) (q : unitInterval × C.positiveOpen)
    (hi : q ∈ C.clampRegion c i) (hj : q ∈ C.clampRegion c j) :
    C.clampLocal c hc i ⟨q, hi⟩ = C.clampLocal c hc j ⟨q, hj⟩ := by
  cases i <;> cases j
  · rfl
  · exact (C.clampBandLocal_fixed c hc ⟨q, hj⟩ hi.le).symm
  · exact C.clampBandLocal_fixed c hc ⟨q, hi⟩ hj.le
  · rfl

theorem clampRegion_nhds (c : ℝ) (hc : c < C.width) (q : unitInterval × C.positiveOpen) :
    ∃ i, C.clampRegion c i ∈ nhds q := by
  have ht : Continuous (fun x : unitInterval × C.positiveOpen ↦ t x.2.val) :=
    C.continuous_time.comp (continuous_subtype_val.comp continuous_snd)
  by_cases hq : t q.2.val < C.width
  · exact ⟨true, (isOpen_lt ht continuous_const).mem_nhds hq⟩
  · exact ⟨false, (isOpen_lt continuous_const ht).mem_nhds
      (hc.trans_le (le_of_not_gt hq))⟩

def clampSlide (c : ℝ) (hc : c < C.width) :
    C(unitInterval × C.positiveOpen, C.positiveOpen) :=
  ContinuousMap.liftCover (C.clampRegion c) (C.clampLocal c hc)
    (C.clampLocal_agree c hc) (C.clampRegion_nhds c hc)

theorem clampSlide_of_lt (c : ℝ) (hc : c < C.width) (q : unitInterval × C.positiveOpen)
    (hq : t q.2.val < C.width) :
    C.clampSlide c hc q = C.clampBandLocal c hc ⟨q, hq⟩ :=
  ContinuousMap.liftCover_coe (i := true) (hφ := C.clampLocal_agree c hc)
    (hS := C.clampRegion_nhds c hc) ⟨q, hq⟩

theorem clampSlide_of_gt (c : ℝ) (hc : c < C.width) (q : unitInterval × C.positiveOpen)
    (hq : c < t q.2.val) : C.clampSlide c hc q = q.2 :=
  ContinuousMap.liftCover_coe (i := false) (hφ := C.clampLocal_agree c hc)
    (hS := C.clampRegion_nhds c hc) ⟨q, hq⟩

theorem clampSlide_time (c : ℝ) (hc : c < C.width) (s : unitInterval) (p : C.positiveOpen) :
    t (C.clampSlide c hc (s, p)).val = interiorSlideTime c s (t p.val) := by
  by_cases hp : t p.val < C.width
  · rw [C.clampSlide_of_lt c hc (s, p) hp]
    exact C.bandSlide_time c hc s (C.clampBandPoint c ⟨(s, p), hp⟩)
  · have hp' := hc.trans_le (le_of_not_gt hp)
    rw [C.clampSlide_of_gt c hc (s, p) hp']
    exact (interiorSlideTime_of_ge c s (t p.val) hp'.le).symm

theorem clampSlide_fixed (c : ℝ) (hc : c < C.width)
    (s : unitInterval) (p : C.positiveOpen) (hp : c ≤ t p.val) :
    C.clampSlide c hc (s, p) = p := by
  by_cases hp' : t p.val < C.width
  · rw [C.clampSlide_of_lt c hc (s, p) hp']
    exact C.clampBandLocal_fixed c hc ⟨(s, p), hp'⟩ hp
  · exact C.clampSlide_of_gt c hc (s, p) (hc.trans_le (le_of_not_gt hp'))

theorem clampSlide_zero (c : ℝ) (hc : c < C.width) (p : C.positiveOpen) :
    C.clampSlide c hc (0, p) = p := by
  by_cases hp : t p.val < C.width
  · rw [C.clampSlide_of_lt c hc (0, p) hp]
    exact Subtype.ext (congrArg (fun z : TimeBand t C.width ↦ z.val)
      (C.bandSlide_zero c hc (C.clampBandPoint c ⟨(0, p), hp⟩)))
  · exact C.clampSlide_of_gt c hc (0, p) (hc.trans_le (le_of_not_gt hp))

theorem clampSlide_one_time (c : ℝ) (hc : c < C.width) (p : C.positiveOpen) :
    t (C.clampSlide c hc (1, p)).val = max (t p.val) c := by
  rw [C.clampSlide_time]
  simp [interiorSlideTime]

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
