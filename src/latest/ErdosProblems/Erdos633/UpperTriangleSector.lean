import ErdosProblems.Erdos633.CornerConeCoordinates
import ErdosProblems.Erdos633.WedgeArguments
import ErdosProblems.Erdos633.LabelledTiling

/-!
# Corner sector area for an upper-half-plane triangle

With the first vertex at zero and the second on the positive real axis,
the two active barycentric inequalities are precisely the argument wedge.
The unit-sector area is therefore half the actual Euclidean corner angle.
-/

namespace Erdos633

def upperTriangle (l : ℝ) (z : ℂ) (hl : 0 < l) (hz : 0 < z.im) : Triangle where
  a := 0
  b := (l : ℂ)
  c := z
  nondegenerate := by
    simpa only [sub_zero, Complex.ofReal_re, Complex.ofReal_im, zero_mul] using
      mul_ne_zero (ne_of_gt hl) (ne_of_gt hz)

theorem upperTriangle_coordinateEquiv (l : ℝ) (z : ℂ) (hl : 0 < l) (hz : 0 < z.im)
    (w : ℂ) : (upperTriangle l z hl hz).coordinateEquiv w =
      ⟨l * w.re + z.re * w.im, z.im * w.im⟩ := by
  rw [Triangle.coordinateEquiv_apply]
  apply Complex.ext
  all_goals simp only [upperTriangle, Complex.add_re, Complex.add_im,
    sub_zero, Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.zero_im, smul_eq_mul]
  all_goals ring

theorem upperTriangle_mem_openCone (l : ℝ) (z : ℂ) (hl : 0 < l) (hz : 0 < z.im)
    (x : ℂ) : x ∈ (upperTriangle l z hl hz).localOpenConeAt 0 ↔
      0 < x.im ∧ 0 < x.re * z.im - x.im * z.re := by
  let P := upperTriangle l z hl hz
  change x ∈ P.localOpenConeAt P.a ↔ _
  rw [P.mem_localOpenConeAt_a]
  obtain ⟨w, rfl⟩ := P.coordinateEquiv.surjective x
  rw [P.coordinateEquiv.symm_apply_apply]
  change (0 < w.re ∧ 0 < w.im) ↔
    0 < ((upperTriangle l z hl hz).coordinateEquiv w).im ∧
      0 < ((upperTriangle l z hl hz).coordinateEquiv w).re * z.im -
        ((upperTriangle l z hl hz).coordinateEquiv w).im * z.re
  rw [upperTriangle_coordinateEquiv]
  change (0 < w.re ∧ 0 < w.im) ↔
    0 < z.im * w.im ∧ 0 < (l * w.re + z.re * w.im) * z.im - z.im * w.im * z.re
  have hd : (l * w.re + z.re * w.im) * z.im - z.im * w.im * z.re =
      (l * z.im) * w.re := by ring
  rw [hd]
  constructor
  · intro h
    exact ⟨mul_pos hz h.2, mul_pos (mul_pos hl hz) h.1⟩
  · intro h
    exact ⟨(mul_pos_iff_of_pos_left (mul_pos hl hz)).mp h.2,
      (mul_pos_iff_of_pos_left hz).mp h.1⟩

theorem upperTriangle_angleA (l : ℝ) (z : ℂ) (hl : 0 < l) (hz : 0 < z.im) :
    (upperTriangle l z hl hz).angleA = z.arg := by
  change InnerProductGeometry.angle ((l : ℂ) - 0) (z - 0) = z.arg
  simp only [sub_zero]
  rw [show (l : ℂ) = l • (1 : ℂ) by simp,
    InnerProductGeometry.angle_smul_left_of_pos (1 : ℂ) z hl,
    InnerProductGeometry.angle, Complex.inner]
  simp only [map_one, mul_one, norm_one, one_mul]
  exact (Complex.arg_of_im_pos hz).symm

theorem upperTriangle_openSector (l : ℝ) (z : ℂ) (hl : 0 < l) (hz : 0 < z.im) :
    (upperTriangle l z hl hz).localOpenConeAt 0 ∩ Metric.ball 0 1 =
      unitAngularSector z.arg := by
  ext x
  rw [Set.mem_inter_iff, upperTriangle_mem_openCone, upper_wedge_iff_arg x z hz]
  simp only [Metric.mem_ball, dist_zero_right]
  change ((0 < x.arg ∧ x.arg < z.arg) ∧ ‖x‖ < 1) ↔
    (0 < ‖x‖ ∧ ‖x‖ < 1) ∧ 0 < x.arg ∧ x.arg < z.arg
  constructor
  · intro h
    have hx : x ≠ 0 := by intro hx; simp [hx] at h
    exact ⟨⟨norm_pos_iff.mpr hx, h.2⟩, h.1⟩
  · intro h
    exact ⟨h.2, h.1.2⟩

theorem upperTriangle_sectorArea (l : ℝ) (z : ℂ) (hl : 0 < l) (hz : 0 < z.im) :
    (upperTriangle l z hl hz).localSectorArea 0 =
      (upperTriangle l z hl hz).angleA / 2 := by
  rw [Triangle.localSectorArea_eq_openConeArea, upperTriangle_openSector,
    upperTriangle_angleA]
  have ha := (arg_mem_upper_iff z).mpr hz
  exact volume_unitAngularSector_toReal z.arg ha.1.le ha.2.le

end Erdos633
