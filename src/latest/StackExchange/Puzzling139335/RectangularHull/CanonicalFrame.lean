import StackExchange.Puzzling139335.RectangularHull.AxisBox
import StackExchange.Puzzling139335.RectangularHull.SideContact
import StackExchange.Puzzling139335.RectangularHull.Transport.Isometry

/-!
# The canonical unit-by-height rectangle frame

This frame represents the normalized source box directly.  Its affine-isometry
image has the same edge lengths, and the row-axis matrix test makes that actual
mapped frame axis aligned.
-/

namespace Puzzling139335.RectangularHull

open Set PlaneIsometries

noncomputable def unitFrame {h : ℝ} (hh : 0 < h) : Frame where
  origin := 0
  first := !₂[1, 0]
  second := !₂[0, h]
  first_ne_zero := by
    intro hz
    have hcoord := congrArg (fun p : Plane => p 0) hz
    norm_num at hcoord
  second_ne_zero := by
    intro hz
    have hcoord : h = 0 := by simpa using congrArg (fun p : Plane => p 1) hz
    exact (ne_of_gt hh) hcoord
  orthogonal := by
    rw [Schoenflies.Plane.inner_eq]
    simp

theorem unitFrame_axisAligned {h : ℝ} (hh : 0 < h) : (unitFrame hh).AxisAligned :=
  Or.inr ⟨rfl, rfl⟩

@[simp] theorem unitFrame_norm_first {h : ℝ} (hh : 0 < h) :
    ‖(unitFrame hh).first‖ = 1 := by
  simpa [unitFrame] using
    norm_eq_abs_coord_zero (v := (unitFrame hh).first) (by rfl)

@[simp] theorem unitFrame_norm_second {h : ℝ} (hh : 0 < h) :
    ‖(unitFrame hh).second‖ = h := by
  simpa [unitFrame, abs_of_pos hh] using
    norm_eq_abs_coord_one (v := (unitFrame hh).second) (by rfl)

theorem unitFrame_carrier {h : ℝ} (hh : 0 < h) :
    (unitFrame hh).carrier = axisBox h := by
  rw [(unitFrame hh).carrier_eq_closedAxisBox (unitFrame_axisAligned hh)]
  simp [Frame.boxLeft, Frame.boxRight, Frame.boxBottom, Frame.boxTop, unitFrame,
    min_eq_left hh.le, max_eq_right hh.le, closedAxisBox, axisBox]

theorem mapped_unitFrame_carrier (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ} (hh : 0 < h) :
    ((unitFrame hh).map e).carrier = e '' axisBox h := by
  rw [(unitFrame hh).map_carrier e, unitFrame_carrier hh]

@[simp] theorem mapped_unitFrame_norm_first (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hh : 0 < h) : ‖((unitFrame hh).map e).first‖ = 1 := by
  simpa only [Frame.map_first, LinearIsometryEquiv.norm_map] using unitFrame_norm_first hh

@[simp] theorem mapped_unitFrame_norm_second (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hh : 0 < h) : ‖((unitFrame hh).map e).second‖ = h := by
  simpa only [Frame.map_second, LinearIsometryEquiv.norm_map] using unitFrame_norm_second hh

@[simp] theorem mapped_unitFrame_first_apply (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hh : 0 < h) (i : Fin 2) :
    ((unitFrame hh).map e).first i = linearMatrix e i 0 := by
  have hfirst : (!₂[1, 0] : Plane) = EuclideanSpace.single 0 1 := by
    apply plane_ext <;> simp
  change e.linearIsometryEquiv !₂[1, 0] i = _
  rw [hfirst]
  rfl

@[simp] theorem mapped_unitFrame_second_apply (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hh : 0 < h) (i : Fin 2) :
    ((unitFrame hh).map e).second i = h * linearMatrix e i 1 := by
  have hsecond : (!₂[0, h] : Plane) = h • EuclideanSpace.single 1 1 := by
    apply plane_ext <;> simp
  change e.linearIsometryEquiv !₂[0, h] i = _
  rw [hsecond]
  simp [linearMatrix]

/-- The matrix-row condition from gap coverage makes the canonical mapped
rectangle itself axis aligned, for either orientation of the isometry. -/
theorem mapped_unitFrame_axisAligned (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hh : 0 < h) (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0) :
    ((unitFrame hh).map e).AxisAligned := by
  unfold Frame.AxisAligned
  rw [mapped_unitFrame_first_apply e hh 0, mapped_unitFrame_second_apply e hh 1,
    mapped_unitFrame_first_apply e hh 1, mapped_unitFrame_second_apply e hh 0]
  obtain ⟨c, s, _hcs, he | he⟩ := linearMatrix_classification e
  all_goals
    have hcs : c = 0 ∨ s = 0 := by simpa [he] using hAxis
    rcases hcs with hc | hs
    · exact Or.inl ⟨by simp [he, hc], by simp [he, hc]⟩
    · exact Or.inr ⟨by simp [he, hs], by simp [he, hs]⟩

end Puzzling139335.RectangularHull
