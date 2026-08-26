import ErdosProblems.Erdos633.PolarSectorArea

/-!
# Arguments and oriented wedges in the upper half-plane

A determinant test for lying between two rays is converted to an interval
of complex arguments. All inequalities are strict, so the boundary rays
can subsequently be handled by their zero area.
-/

namespace Erdos633

theorem arg_mem_upper_iff (z : ℂ) :
    0 < z.arg ∧ z.arg < Real.pi ↔ 0 < z.im := by
  constructor
  · intro h
    have hz : z ≠ 0 := by
      intro hz
      simpa [hz] using h.1
    rw [← Complex.norm_mul_sin_arg z]
    exact mul_pos (norm_pos_iff.mpr hz) (Real.sin_pos_of_pos_of_lt_pi h.1 h.2)
  · intro h
    refine ⟨?_, Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt h))⟩
    apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le)
    intro heq
    have him := (Complex.arg_eq_zero_iff.mp heq.symm).2
    linarith

theorem arg_lt_iff_det_pos (x z : ℂ) (hx : 0 < x.im) (hz : 0 < z.im) :
    x.arg < z.arg ↔ 0 < x.re * z.im - x.im * z.re := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hnx := norm_pos_iff.mpr hx0
  have hnz := norm_pos_iff.mpr hz0
  have hxa := (arg_mem_upper_iff x).mpr hx
  have hza := (arg_mem_upper_iff z).mpr hz
  have hid : ‖x‖ * ‖z‖ * Real.sin (z.arg - x.arg) =
      x.re * z.im - x.im * z.re := by
    rw [Real.sin_sub, Complex.sin_arg, Complex.cos_arg hx0,
      Complex.cos_arg hz0, Complex.sin_arg]
    field_simp
  constructor
  · intro h
    have hs := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr h)
      (show z.arg - x.arg < Real.pi by linarith [hxa.1, hza.2])
    rw [← hid]
    exact mul_pos (mul_pos hnx hnz) hs
  · intro h
    by_contra hn
    have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (show z.arg - x.arg ≤ 0 by linarith)
      (show -Real.pi ≤ z.arg - x.arg by linarith [hza.1, hxa.2])
    have hp := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hnx.le hnz.le) hs
    linarith

theorem upper_wedge_iff_arg (x z : ℂ) (hz : 0 < z.im) :
    (0 < x.im ∧ 0 < x.re * z.im - x.im * z.re) ↔
      0 < x.arg ∧ x.arg < z.arg := by
  constructor
  · intro h
    exact ⟨((arg_mem_upper_iff x).mpr h.1).1, (arg_lt_iff_det_pos x z h.1 hz).mpr h.2⟩
  · intro h
    have hx : 0 < x.im := (arg_mem_upper_iff x).mp
      ⟨h.1, h.2.trans ((arg_mem_upper_iff z).mpr hz).2⟩
    exact ⟨hx, (arg_lt_iff_det_pos x z hx hz).mp h.2⟩

end Erdos633
