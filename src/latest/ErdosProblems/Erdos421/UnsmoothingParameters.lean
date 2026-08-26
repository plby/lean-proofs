import ErdosProblems.Erdos421.StretchedLogDecay

/-! # Uniform parameter bounds for removing the triangular cutoff -/

namespace Erdos421

open Filter Topology

theorem log_power_le_self_eventually (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ D ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop D (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have he : (Real.log x) ^ D / x ≤ 1 := by simpa only [Real.rpow_one] using hx.le
  exact (div_le_one hx0).mp he

theorem unsmoothing_step_bounds {x A : ℝ} (hA : 0 ≤ A) (hlog : 1 ≤ Real.log x)
    (hsize : (Real.log x) ^ (A + 3) ≤ x) :
    1 ≤ x / (Real.log x) ^ (A + 3) ∧ x / (Real.log x) ^ (A + 3) ≤ x := by
  have hp : 1 ≤ (Real.log x) ^ (A + 3) := Real.one_le_rpow hlog (by linarith)
  have hp0 : 0 < (Real.log x) ^ (A + 3) := by linarith
  have hx : 0 ≤ x := by linarith
  exact ⟨(one_le_div hp0).mpr hsize, div_le_self hx hp⟩

theorem unsmoothing_log_bounds {x h : ℝ} (hx : 2 ≤ x) (hh : 0 ≤ h) (hhx : h ≤ x) :
    Real.log x ≤ Real.log (x + h) ∧ Real.log (x + h) ≤ 2 * Real.log x := by
  have hxp : 0 < x := by linarith
  refine ⟨Real.log_le_log hxp (by linarith), ?_⟩
  have h := Real.log_le_log (by linarith : 0 < x + h) (by linarith : x + h ≤ 2 * x)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxp.ne'] at h
  have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  linarith

theorem unsmoothing_frequency_bound {x h A : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x)
    (hh : 0 ≤ h) (hhx : h ≤ x) (hlarge : (2 : ℝ) ^ (2 * A + 7) ≤ Real.log x) :
    (Real.log (x + h)) ^ ((2 * A + 3) + 4) ≤ (Real.log x) ^ (2 * A + 8) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogh : 0 ≤ Real.log (x + h) := Real.log_nonneg (by linarith)
  have hlogupper := (unsmoothing_log_bounds hx hh hhx).2
  calc
    _ = (Real.log (x + h)) ^ (2 * A + 7) := by congr 1; ring
    _ ≤ (2 * Real.log x) ^ (2 * A + 7) := Real.rpow_le_rpow hlogh hlogupper (by linarith)
    _ = (2 : ℝ) ^ (2 * A + 7) * (Real.log x) ^ (2 * A + 7) :=
      Real.mul_rpow (by norm_num) hlog
    _ ≤ Real.log x * (Real.log x) ^ (2 * A + 7) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hlog _)
    _ = (Real.log x) ^ (2 * A + 8) := by
      have hlogp : 0 < Real.log x := Real.log_pos (by linarith)
      rw [show 2 * A + 8 = 1 + (2 * A + 7) by ring,
        Real.rpow_add hlogp 1 (2 * A + 7), Real.rpow_one]

theorem unsmoothing_main_term_identity {x L A η : ℝ} (hx : 0 < x) (hL : 0 < L) :
    (5 * η * x ^ 2 / L ^ (2 * A + 3)) / (x / L ^ (A + 3)) = 5 * η * x / L ^ A := by
  have hsplit : L ^ (2 * A + 3) = L ^ A * L ^ (A + 3) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  rw [hsplit]
  have hp : L ^ (A + 3) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  field_simp

theorem unsmoothing_boundary_identity {x L A : ℝ} (hL : 0 < L) :
    4 * (x / L ^ (A + 3)) * L = (4 / L ^ 2) * (x / L ^ A) := by
  have hsplit : L ^ (A + 3) = L ^ A * L ^ 2 * L := by
    rw [show A + 3 = (A + 2) + 1 by ring, Real.rpow_add hL, Real.rpow_one,
      Real.rpow_add hL, Real.rpow_two]
  rw [hsplit]
  field_simp

end Erdos421
