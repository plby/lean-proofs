import StackExchange.Puzzling139335.RectangularHull.Frames
import StackExchange.Puzzling139335.RectangularHull.AxisAlignment

/-!
# Coordinate boxes for axis-aligned rectangle frames

The bounds are the coordinatewise minima and maxima of two opposite frame
vertices.  Nonzero axis edges make both coordinate intervals nondegenerate.
-/

open Set

namespace Puzzling139335.RectangularHull

def closedAxisBox (l r b t : ℝ) : Set Plane :=
  {p | p 0 ∈ Icc l r ∧ p 1 ∈ Icc b t}

lemma convex_closedAxisBox (l r b t : ℝ) : Convex ℝ (closedAxisBox l r b t) :=
  ((convex_Icc l r).linear_preimage (EuclideanSpace.proj (0 : Fin 2)).toLinearMap).inter
    ((convex_Icc b t).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap)

lemma isClosed_closedAxisBox (l r b t : ℝ) : IsClosed (closedAxisBox l r b t) :=
  (isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).inter
    (isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1))

noncomputable def Frame.boxLeft (R : Frame) : ℝ :=
  min (R.origin 0) ((R.origin + R.first + R.second) 0)

noncomputable def Frame.boxRight (R : Frame) : ℝ :=
  max (R.origin 0) ((R.origin + R.first + R.second) 0)

noncomputable def Frame.boxBottom (R : Frame) : ℝ :=
  min (R.origin 1) ((R.origin + R.first + R.second) 1)

noncomputable def Frame.boxTop (R : Frame) : ℝ :=
  max (R.origin 1) ((R.origin + R.first + R.second) 1)

private lemma mem_interval_iff_affine (o d x : ℝ) :
    x ∈ Icc (min o (o + d)) (max o (o + d)) ↔
      ∃ t ∈ Icc (0 : ℝ) 1, x = o + t * d := by
  rw [← segment_eq_Icc']
  constructor
  · rintro ⟨a, b, ha, hb, hab, heq⟩
    refine ⟨b, ⟨hb, by linarith⟩, ?_⟩
    change a * o + b * (o + d) = x at heq
    calc
      x = a * o + b * (o + d) := heq.symm
      _ = (a + b) * o + b * d := by ring
      _ = o + b * d := by rw [hab, one_mul]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
    change (1 - t) * o + t * (o + d) = o + t * d
    ring

lemma Frame.carrier_eq_closedAxisBox (R : Frame) (hAxis : R.AxisAligned) :
    R.carrier = closedAxisBox R.boxLeft R.boxRight R.boxBottom R.boxTop := by
  ext x
  rw [R.mem_carrier_iff]
  rcases hAxis with ⟨hf0, hs1⟩ | ⟨hf1, hs0⟩
  · simp only [closedAxisBox, mem_ofPred_eq, boxLeft, boxRight, boxBottom, boxTop,
      PiLp.add_apply, hf0, hs1, add_zero]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hf0, hs1, mul_zero,
        add_zero]
      exact ⟨(mem_interval_iff_affine _ _ _).mpr ⟨b, hb, rfl⟩,
        (mem_interval_iff_affine _ _ _).mpr ⟨a, ha, rfl⟩⟩
    · intro hx
      obtain ⟨b, hb, hxb⟩ := (mem_interval_iff_affine _ _ _).mp hx.1
      obtain ⟨a, ha, hxa⟩ := (mem_interval_iff_affine _ _ _).mp hx.2
      refine ⟨a, ha, b, hb, ?_⟩
      ext i
      fin_cases i
      · change x 0 = R.origin 0 + a * R.first 0 + b * R.second 0
        simpa only [hf0, mul_zero, add_zero] using hxb
      · change x 1 = R.origin 1 + a * R.first 1 + b * R.second 1
        simpa only [hs1, mul_zero, add_zero] using hxa
  · simp only [closedAxisBox, mem_ofPred_eq, boxLeft, boxRight, boxBottom, boxTop,
      PiLp.add_apply, hf1, hs0, add_zero]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hf1, hs0, mul_zero,
        add_zero]
      exact ⟨(mem_interval_iff_affine _ _ _).mpr ⟨a, ha, rfl⟩,
        (mem_interval_iff_affine _ _ _).mpr ⟨b, hb, rfl⟩⟩
    · intro hx
      obtain ⟨a, ha, hxa⟩ := (mem_interval_iff_affine _ _ _).mp hx.1
      obtain ⟨b, hb, hxb⟩ := (mem_interval_iff_affine _ _ _).mp hx.2
      refine ⟨a, ha, b, hb, ?_⟩
      ext i
      fin_cases i
      · change x 0 = R.origin 0 + a * R.first 0 + b * R.second 0
        simpa only [hs0, mul_zero, add_zero] using hxa
      · change x 1 = R.origin 1 + a * R.first 1 + b * R.second 1
        simpa only [hf1, mul_zero, add_zero] using hxb

lemma norm_eq_abs_coord_zero {v : Plane} (hv : v 1 = 0) : ‖v‖ = |v 0| := by
  have hs : ‖v‖ ^ 2 = (v 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two, hv]
  nlinarith only [hs, sq_abs (v 0), norm_nonneg v, abs_nonneg (v 0)]

lemma norm_eq_abs_coord_one {v : Plane} (hv : v 0 = 0) : ‖v‖ = |v 1| := by
  have hs : ‖v‖ ^ 2 = (v 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two, hv]
  nlinarith only [hs, sq_abs (v 1), norm_nonneg v, abs_nonneg (v 1)]

lemma Frame.box_width_eq_abs (R : Frame) :
    R.boxRight - R.boxLeft = |R.first 0 + R.second 0| := by
  rw [boxRight, boxLeft, max_sub_min_eq_abs]
  congr 1
  simp only [PiLp.add_apply]
  ring

lemma Frame.box_height_eq_abs (R : Frame) :
    R.boxTop - R.boxBottom = |R.first 1 + R.second 1| := by
  rw [boxTop, boxBottom, max_sub_min_eq_abs]
  congr 1
  simp only [PiLp.add_apply]
  ring

lemma Frame.axisBox_side_lengths (R : Frame) (hAxis : R.AxisAligned) :
    (R.boxRight - R.boxLeft = ‖R.first‖ ∧ R.boxTop - R.boxBottom = ‖R.second‖) ∨
      (R.boxRight - R.boxLeft = ‖R.second‖ ∧ R.boxTop - R.boxBottom = ‖R.first‖) := by
  rw [R.box_width_eq_abs, R.box_height_eq_abs]
  rcases hAxis with ⟨hf0, hs1⟩ | ⟨hf1, hs0⟩
  · right
    simp only [hf0, hs1, zero_add, add_zero]
    exact ⟨(norm_eq_abs_coord_zero hs1).symm, (norm_eq_abs_coord_one hf0).symm⟩
  · left
    simp only [hf1, hs0, zero_add, add_zero]
    exact ⟨(norm_eq_abs_coord_zero hf1).symm, (norm_eq_abs_coord_one hs0).symm⟩

lemma Frame.box_bounds_lt (R : Frame) (hAxis : R.AxisAligned) :
    R.boxLeft < R.boxRight ∧ R.boxBottom < R.boxTop := by
  have hf : 0 < ‖R.first‖ := norm_pos_iff.mpr R.first_ne_zero
  have hs : 0 < ‖R.second‖ := norm_pos_iff.mpr R.second_ne_zero
  rcases R.axisBox_side_lengths hAxis with ⟨hw, hh⟩ | ⟨hw, hh⟩
  all_goals constructor <;> linarith

theorem Frame.exists_axisBox (R : Frame) (hAxis : R.AxisAligned) :
    ∃ l r b t : ℝ, l < r ∧ b < t ∧ R.carrier = closedAxisBox l r b t ∧
      ((r - l = ‖R.first‖ ∧ t - b = ‖R.second‖) ∨
        (r - l = ‖R.second‖ ∧ t - b = ‖R.first‖)) :=
  ⟨R.boxLeft, R.boxRight, R.boxBottom, R.boxTop, (R.box_bounds_lt hAxis).1,
    (R.box_bounds_lt hAxis).2, R.carrier_eq_closedAxisBox hAxis, R.axisBox_side_lengths hAxis⟩

lemma interior_closedAxisBox (l r b t : ℝ) :
    interior (closedAxisBox l r b t) = {p : Plane | p 0 ∈ Ioo l r ∧ p 1 ∈ Ioo b t} := by
  have hzero : (fun p : Plane => p 0) ⁻¹' interior (Icc l r) =
      interior ((fun p : Plane => p 0) ⁻¹' Icc l r) :=
    IsOpenMap.preimage_interior_eq_interior_preimage
      (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0) (Icc l r)
  have hone : (fun p : Plane => p 1) ⁻¹' interior (Icc b t) =
      interior ((fun p : Plane => p 1) ⁻¹' Icc b t) :=
    IsOpenMap.preimage_interior_eq_interior_preimage
      (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1)
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) (Icc b t)
  change interior (((fun p : Plane => p 0) ⁻¹' Icc l r) ∩
    ((fun p : Plane => p 1) ⁻¹' Icc b t)) = _
  rw [interior_inter, ← hzero, ← hone, interior_Icc, interior_Icc]
  rfl

lemma mem_interior_closedAxisBox {l r b t : ℝ} {p : Plane} :
    p ∈ interior (closedAxisBox l r b t) ↔ l < p 0 ∧ p 0 < r ∧ b < p 1 ∧ p 1 < t := by
  rw [interior_closedAxisBox]
  simp only [mem_ofPred_eq, mem_Ioo, and_assoc]

lemma Frame.mem_interior_carrier_iff (R : Frame) (hAxis : R.AxisAligned) {p : Plane} :
    p ∈ interior R.carrier ↔ R.boxLeft < p 0 ∧ p 0 < R.boxRight ∧
      R.boxBottom < p 1 ∧ p 1 < R.boxTop := by
  rw [R.carrier_eq_closedAxisBox hAxis, mem_interior_closedAxisBox]

def axisBoxVertices (l r b t : ℝ) : Set Plane :=
  {!₂[l, b], !₂[r, b], !₂[r, t], !₂[l, t]}

lemma mem_extremePoints_closedAxisBox_of_endpoints {l r b t : ℝ} (hlr : l ≤ r)
    (hbt : b ≤ t) {p : Plane} (hp0 : p 0 = l ∨ p 0 = r) (hp1 : p 1 = b ∨ p 1 = t) :
    p ∈ (closedAxisBox l r b t).extremePoints ℝ := by
  have hzero : p 0 ∈ (Icc l r).extremePoints ℝ := by
    rw [Set.extremePoints_Icc hlr]
    simpa only [mem_insert_iff, mem_singleton_iff] using hp0
  have hone : p 1 ∈ (Icc b t).extremePoints ℝ := by
    rw [Set.extremePoints_Icc hbt]
    simpa only [mem_insert_iff, mem_singleton_iff] using hp1
  refine ⟨⟨hzero.1, hone.1⟩, ?_⟩
  intro x hx y hy hseg
  obtain ⟨a, c, ha, hc, hac, heq⟩ := hseg
  have heq0 : a * x 0 + c * y 0 = p 0 := congrArg (fun z : Plane => z 0) heq
  have heq1 : a * x 1 + c * y 1 = p 1 := congrArg (fun z : Plane => z 1) heq
  have hx0 : x 0 = p 0 := hzero.2 hx.1 hy.1 ⟨a, c, ha, hc, hac, heq0⟩
  have hx1 : x 1 = p 1 := hone.2 hx.2 hy.2 ⟨a, c, ha, hc, hac, heq1⟩
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

lemma axisBoxVertices_subset_extremePoints {l r b t : ℝ} (hlr : l ≤ r) (hbt : b ≤ t) :
    axisBoxVertices l r b t ⊆ (closedAxisBox l r b t).extremePoints ℝ := by
  intro p hp
  simp only [axisBoxVertices, mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals apply mem_extremePoints_closedAxisBox_of_endpoints hlr hbt <;> simp

lemma Frame.axisBoxVertices_subset_vertices (R : Frame) (hAxis : R.AxisAligned) :
    axisBoxVertices R.boxLeft R.boxRight R.boxBottom R.boxTop ⊆ R.vertices := by
  obtain ⟨hlr, hbt⟩ := R.box_bounds_lt hAxis
  have h := axisBoxVertices_subset_extremePoints hlr.le hbt.le
  rw [← R.carrier_eq_closedAxisBox hAxis, R.extremePoints_carrier] at h
  exact h

lemma Frame.axisBoxVertices_subset_of_convexHull_eq (R : Frame) (hAxis : R.AxisAligned)
    {P : Set Plane} (hP : convexHull ℝ P = R.carrier) :
    axisBoxVertices R.boxLeft R.boxRight R.boxBottom R.boxTop ⊆ P :=
  (R.axisBoxVertices_subset_vertices hAxis).trans (R.vertices_subset_of_convexHull_eq hP)

end Puzzling139335.RectangularHull
