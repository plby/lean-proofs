import ErdosProblems.Erdos964.ScalarSecondMainFaceError
import ErdosProblems.Erdos964.ScalarSliceFaceLimit

/-!
# The asymptotic of the concrete second scalar main term
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_scalarSecondMainAtScale (M m c K : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hK : 1 ≤ K) (hKsize : 2 * m + c ≤ K ^ 2)
    (η β : ℝ) (hη : 0 < η) (hηβ : η < β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => scalarSecondMainAtScale M m c K η β t /
      (((t ^ 2 : ℕ) : ℝ) * (Real.log (modulusCutoff β t)) ^ 3)) atTop
      (𝓝 ((scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) *
        (m : ℝ) * (β / 2) * scalarPrimeIntegral η β)) := by
  have hβ : 0 < β := hη.trans hηβ
  let A := scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4
  let L : ℕ → ℝ := fun t => Real.log (modulusCutoff β t)
  let H : ℕ → ℝ := fun t => scalarSecondMainAtScale M m c K η β t / (L t) ^ 4 -
    A * scalarSliceFaceSum η β m c K t
  let s : ℕ → ℝ := fun t => ((t ^ 2 : ℕ) : ℝ) / Real.log t
  obtain ⟨D, hD, herror⟩ :=
    exists_scalar_second_main_face_error M m c K hM h2M h3M hm hc hK hKsize η β hη hβ
  have hs : ∀ᶠ t : ℕ in atTop, 0 < s t := by
    filter_upwards [eventually_ge_atTop 2] with t ht
    have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    dsimp only [s]
    positivity
  have hsmall : Tendsto (fun t : ℕ => H t / s t) atTop (𝓝 0) := by
    apply tendsto_normalized_uniform_small_error H s D hD hs
    intro ε hε
    obtain ⟨T₀, hT₀, hT⟩ := herror ε hε
    exact eventually_atTop.mpr ⟨T₀, hT⟩
  have hratio₁ := tendsto_log_scalar_power_radius_div_log β hβ
  have hratio₂ := tendsto_log_scalar_power_radius_div_log_square β hβ
  have hslice := tendsto_scalarSliceFaceSum m c K hm hc hK hKsize η β hη hηβ hβ1
  have h := (hsmall.mul hratio₁).add ((hslice.const_mul A).mul hratio₂)
  simp only [zero_mul, zero_add] at h
  have hlim : (A * ((m : ℝ) * scalarPrimeIntegral η β)) * (β / 2) =
      A * (m : ℝ) * (β / 2) * scalarPrimeIntegral η β := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_log_scalar_power_radius β hβ).eventually (eventually_gt_atTop 0)] with t ht hL
  have hN : ((t ^ 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show (t ^ 2 : ℕ) ≠ 0 by positivity)
  have hlogt : Real.log t ≠ 0 := (Real.log_pos
    (by exact_mod_cast (show 1 < t by omega))).ne'
  have hlogN : Real.log (t ^ 2 : ℕ) ≠ 0 := (Real.log_pos
    (by exact_mod_cast (show 1 < t ^ 2 by nlinarith))).ne'
  change (H t / s t) * (L t / Real.log t) +
    (A * (scalarSliceFaceSum η β m c K t * Real.log (t ^ 2 : ℕ) / (t ^ 2 : ℕ))) *
      (L t / Real.log (t ^ 2 : ℕ)) = _
  dsimp only [H, s, L]
  field_simp
  ring

end Erdos964
