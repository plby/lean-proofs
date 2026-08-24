import ErdosProblems.Erdos587.FiberReduction

/-! The thick unit-step fiber follows from the homogeneous rank-one square lemma. -/

namespace Erdos587

lemma thick_fiber_rank_one_length {u H T : ℕ} (hT : 0 < T)
    (hwidth : u * H ≤ T) (hthick : 4 * Real.sqrt T ≤ H) :
    2 * Nat.sqrt T + u ≤ H := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTR
  have hrootSq := Real.sq_sqrt hTR.le
  have hwidthR : (u : ℝ) * H ≤ T := by exact_mod_cast hwidth
  have hscaled := mul_le_mul_of_nonneg_left hthick (Nat.cast_nonneg u)
  have hu : (u : ℝ) ≤ Real.sqrt T := by
    apply (mul_le_mul_iff_left₀ hroot).mp
    have hnonneg : (0 : ℝ) ≤ u * Real.sqrt T := by positivity
    nlinarith
  have hnatroot : (Nat.sqrt T : ℝ) ≤ Real.sqrt T := by
    have hsq : (Nat.sqrt T : ℝ) ^ 2 ≤ T := by exact_mod_cast Nat.sqrt_le' T
    have hh := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at hh
  have hh : 2 * (Nat.sqrt T : ℝ) + u ≤ H := by linarith
  exact_mod_cast hh

theorem exists_square_in_thick_unit_fiber {u t H T : ℕ} (hu : 0 < u) (hT : 0 < T)
    (hstart : u * t ≤ T) (hwidth : u * H ≤ T) (hthick : 4 * Real.sqrt T ≤ H) :
    ∃ x ≤ H, ∃ z : ℕ, 0 < z ∧ z ^ 2 = u * (t + x) := by
  obtain ⟨m, hm, hmpos, hmsq⟩ := exists_square_mem_homogeneous_natAP_of_start_le u t H T
    hu hstart (thick_fiber_rank_one_length hT hwidth hthick)
  obtain ⟨x, hx, hxm⟩ := mem_natAP_iff.mp hm
  obtain ⟨z, hz⟩ := hmsq
  refine ⟨x, hx, z, ?_, ?_⟩
  · nlinarith
  · nlinarith

end Erdos587
