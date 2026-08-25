import ErdosProblems.Erdos964.ScalarSupportLogLimits

/-!
# Compact logarithmic windows for the actual prime support
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem eventually_scalar_support_log_windows (K : ℕ) (hK : 0 < K)
    (η β : ℝ) (hη : 0 < η) (hηβ : η < β) (hβ1 : β < 1) :
    ∀ᶠ t : ℕ in atTop,
      let R := modulusCutoff β t
      let x := Real.rpow (K * t : ℕ) η
      let y := (t / (K + 1) : ℕ)
      2 ≤ R ∧ 1 ≤ x ∧ x ≤ (R : ℝ) ∧ (R : ℝ) ≤ y ∧
        Real.log x / Real.log R ∈ Set.Icc (0 : ℝ) 1 ∧
        Real.log y / Real.log R ∈ Set.Icc (1 : ℝ) (3 / (2 * β)) := by
  have hβ : 0 < β := hη.trans hηβ
  have hlo0 : 0 < η / β := div_pos hη hβ
  have hlo1 : η / β < 1 := (div_lt_one hβ).mpr hηβ
  have hhi1 : 1 < 1 / β := (one_lt_div hβ).mpr hβ1
  have hhiB : 1 / β < 3 / (2 * β) := by
    apply (div_lt_div_iff₀ hβ (by positivity)).mpr
    nlinarith
  have hlo := (tendsto_scalar_support_lower_log_ratio K hK η β hβ).eventually
    (Ioo_mem_nhds hlo0 hlo1)
  have hhi := (tendsto_scalar_support_upper_log_ratio K β hβ).eventually
    (Ioo_mem_nhds hhi1 hhiB)
  filter_upwards [hlo, hhi, (tendsto_scalar_power_radius β hβ).eventually
    (eventually_ge_atTop 2), eventually_ge_atTop (K + 1)] with t htlo hthi hR ht
  dsimp only
  let R := modulusCutoff β t
  let x := Real.rpow (K * t : ℕ) η
  let y : ℕ := t / (K + 1)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by dsimp only [R]; omega)
  have hL : 0 < Real.log R := Real.log_pos
    (by exact_mod_cast (show 1 < R by dsimp only [R]; omega))
  have htpos : 0 < t := by omega
  have hKt : (1 : ℝ) ≤ (K * t : ℕ) := by exact_mod_cast Nat.mul_pos hK htpos
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    rw [Real.rpow_eq_pow]
    exact Real.one_le_rpow hKt hη.le
  have hypos : 0 < y := Nat.div_pos ht (Nat.succ_pos K)
  have hxR : x ≤ (R : ℝ) := by
    apply (Real.log_le_log_iff (by linarith : 0 < x) hRpos).mp
    exact (div_le_one hL).mp htlo.2.le
  have hRy : (R : ℝ) ≤ y := by
    apply (Real.log_le_log_iff hRpos (by exact_mod_cast hypos)).mp
    exact (one_le_div hL).mp hthi.1.le
  exact ⟨hR, hx1, hxR, hRy, ⟨htlo.1.le, htlo.2.le⟩, ⟨hthi.1.le, hthi.2.le⟩⟩

end Erdos964
