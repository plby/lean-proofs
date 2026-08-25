import ErdosProblems.Erdos964.PrimeLogMovingWindow
import ErdosProblems.Erdos964.ScalarSupportLogWindows
import ErdosProblems.Erdos964.ScalarPrimeSumSplit
import ErdosProblems.Erdos964.ScalarLargePrimeIntegral

/-!
# The fixed-parameter prime integral on the actual sieve support
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_scalar_prime_support_integral (K : ℕ) (hK : 0 < K)
    (η β : ℝ) (hη : 0 < η) (hηβ : η < β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => ∑ p ∈ scalarSmallPrimeSupport η K t,
        (Real.log p / (p : ℝ)) *
          scalarPrimeIntegrand (β / 2) (Real.log p / Real.log (modulusCutoff β t)) /
            Real.log (modulusCutoff β t)) atTop
      (𝓝 ((∫ z in (η / β)..1, scalarSmallPrimeIntegrand (β / 2) z) +
        Real.log ((1 - β / 2) / (β / 2)) * truncatedSieveFace 1)) := by
  have hβ : 0 < β := hη.trans hηβ
  let R := modulusCutoff β
  let L : ℕ → ℝ := fun t => Real.log (R t)
  let x : ℕ → ℝ := fun t => Real.rpow (K * t : ℕ) η
  let y : ℕ → ℝ := fun t => (t / (K + 1) : ℕ)
  have hL : Tendsto L atTop atTop := tendsto_log_scalar_power_radius β hβ
  have hwindow := eventually_scalar_support_log_windows K hK η β hη hηβ hβ1
  have hself : Tendsto (fun t : ℕ => Real.log (R t) / L t) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hL.eventually (eventually_gt_atTop 0)] with t ht
    dsimp only [L] at ht ⊢
    rw [div_self ht.ne']
  have hsmallSmooth := scalarSmallPrimeIntegrand_smooth_on (β / 2) (Set.Icc (0 : ℝ) 1)
    (fun z hz => by
      have hzlt : β / 2 * z < 1 := by nlinarith [hz.1, hz.2]
      linarith)
  have hsmallWindow : ∀ᶠ t : ℕ in atTop, 1 ≤ x t ∧ x t ≤ (R t : ℝ) ∧
      Real.log (x t) / L t ∈ Set.Icc (0 : ℝ) 1 ∧
      Real.log (R t) / L t ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hwindow, hL.eventually (eventually_gt_atTop 0)] with t ht hLt
    refine ⟨ht.2.1, ht.2.2.1, ht.2.2.2.2.1, ?_⟩
    dsimp only [L] at hLt ⊢
    rw [div_self hLt.ne']
    norm_num
  have hloMem : η / β ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(div_pos hη hβ).le, ((div_lt_one hβ).mpr hηβ).le⟩
  have hsmall := tendsto_primeLogScaleSum_moving_window 0 1 (η / β) 1 (by norm_num)
    (scalarSmallPrimeIntegrand (β / 2)) L x (fun t => (R t : ℝ))
    hsmallSmooth.1 hsmallSmooth.2 hloMem (by norm_num) hL
    (tendsto_scalar_support_lower_log_ratio K hK η β hβ) hself hsmallWindow
  let B := 3 / (2 * β)
  have hB : 1 ≤ B := by
    dsimp only [B]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hhiMem : 1 / β ∈ Set.Icc (1 : ℝ) B := by
    constructor
    · exact (one_le_div hβ).mpr hβ1.le
    · dsimp only [B]
      apply (div_le_div_iff₀ hβ (by positivity)).mpr
      nlinarith
  have hlargeSmooth := scalarLargePrimeIntegrand_smooth_on (β / 2) (Set.Icc (1 : ℝ) B)
    (fun z hz => by linarith [hz.1]) (fun z hz => by
      have hb : β / 2 * B = 3 / 4 := by dsimp only [B]; field_simp; norm_num
      have hmul := mul_le_mul_of_nonneg_left hz.2 (show 0 ≤ β / 2 by positivity)
      rw [hb] at hmul
      linarith)
  have hlargeWindow : ∀ᶠ t : ℕ in atTop, 1 ≤ (R t : ℝ) ∧ (R t : ℝ) ≤ y t ∧
      Real.log (R t) / L t ∈ Set.Icc (1 : ℝ) B ∧
      Real.log (y t) / L t ∈ Set.Icc (1 : ℝ) B := by
    filter_upwards [hwindow, hL.eventually (eventually_gt_atTop 0)] with t ht hLt
    refine ⟨?_, ht.2.2.2.1, ?_, ht.2.2.2.2.2⟩
    · exact_mod_cast (show 1 ≤ R t by have := ht.1; dsimp only [R]; omega)
    · dsimp only [L] at hLt ⊢
      rw [div_self hLt.ne']
      exact ⟨le_rfl, hB⟩
  have hlarge := tendsto_primeLogScaleSum_moving_window 1 B 1 (1 / β) hB
    (scalarLargePrimeIntegrand (β / 2)) L (fun t => (R t : ℝ)) y
    hlargeSmooth.1 hlargeSmooth.2 ⟨le_rfl, hB⟩ hhiMem hL hself
    (tendsto_scalar_support_upper_log_ratio K β hβ) hlargeWindow
  have hlargeIntegral : (∫ z in (1 : ℝ)..(1 / β), scalarLargePrimeIntegrand (β / 2) z) =
      Real.log ((1 - β / 2) / (β / 2)) * truncatedSieveFace 1 := by
    have heq : 2 * (β / 2) = β := by ring
    simpa only [heq] using
      integral_scalarLargePrimeIntegrand (β / 2) (by positivity) (by linarith)
  rw [hlargeIntegral] at hlarge
  have h := hsmall.add hlarge
  apply h.congr'
  filter_upwards [hwindow] with t ht
  rw [scalarSmallPrimeSupport_sum_eq_primeLogScaleSum]
  exact (scalarPrimeLogScaleSum_split (β / 2) (x t) (y t) (R t)
    ht.1 ht.2.2.1 ht.2.2.2.1).symm

end Erdos964
