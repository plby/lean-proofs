import ErdosProblems.Erdos964.ScalarPowerLogLimits
import ErdosProblems.Erdos964.PrimeMertensCumulative

/-!
# Bounded normalized prime-log mass on the actual smaller-prime support
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem exists_scalar_prime_log_mass_bound (β : ℝ) (hβ : 0 < β) :
    ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ (t K : ℕ) (η : ℝ), T₀ ≤ t →
      (∑ p ∈ scalarSmallPrimeSupport η K t,
        (Real.log p / (p : ℝ)) / Real.log (modulusCutoff β t)) ≤ 2 / β := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogHarmonicSum_sub_log
  have hR : Tendsto (fun t : ℕ => Real.log (modulusCutoff β t)) atTop atTop :=
    tendsto_log_scalar_power_radius β hβ
  have hratio : Tendsto (fun t : ℕ => Real.log t / Real.log (modulusCutoff β t))
      atTop (𝓝 (1 / β)) := by
    simpa only [inv_div, one_div] using
      (tendsto_log_scalar_power_radius_div_log β hβ).inv₀ hβ.ne'
  have hmain : Tendsto (fun t : ℕ => (Real.log t + C) / Real.log (modulusCutoff β t))
      atTop (𝓝 (1 / β)) := by
    have h := hratio.add (hR.const_div_atTop C)
    simpa only [add_zero, ← add_div] using h
  have hmargin : 1 / β < 2 / β := div_lt_div_of_pos_right (by norm_num) hβ
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (((tendsto_order.mp hmain).2 (2 / β) hmargin).and
      (hR.eventually (eventually_gt_atTop 0)))
  refine ⟨max T₁ 2, le_max_right _ _, ?_⟩
  intro t K η ht
  have hT := hT₁ t ((le_max_left T₁ 2).trans ht)
  rw [← Finset.sum_div]
  calc
    _ ≤ primeLogHarmonicSum t / Real.log (modulusCutoff β t) := by
      apply div_le_div_of_nonneg_right _ hT.2.le
      unfold primeLogHarmonicSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hs := scalarSmallPrimeSupport_spec η K t p hp
        exact Nat.mem_primesLE.mpr ⟨hs.2.1.trans (Nat.div_le_self _ _), hs.1⟩
      · intro p hp hnot
        exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Real.log t + C) / Real.log (modulusCutoff β t) :=
      div_le_div_of_nonneg_right (by linarith [(abs_le.mp (hC t)).2]) hT.2.le
    _ ≤ 2 / β := hT.1.le

end Erdos964
