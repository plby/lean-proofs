import ErdosProblems.Erdos421.PrimeBlockLogSaving
import ErdosProblems.Erdos421.ZetaScaleSaving

/-! # Prime factors of polynomial length at an ambient scale -/

namespace Erdos421

open Filter Topology

theorem primeDirichletBlock_ambient_log_saving {δ : ℝ} (hδ : 0 < δ)
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M N : ℕ, (X : ℝ) ^ δ ≤ M → M ≤ X → N ≤ M →
      ∀ s : ℂ, 1 ≤ s.re → (Real.log X) ^ (2 * A + 9) ≤ |s.im| → |s.im| ≤ X →
        ‖primeDirichletBlock M N s‖ ≤ ε / (Real.log X) ^ A := by
  let R := ⌈δ⁻¹⌉₊
  have hR : 1 ≤ δ * ((R : ℝ) + 1) := by
    have hr : δ⁻¹ ≤ (R : ℝ) := Nat.le_ceil _
    have hm := mul_le_mul_of_nonneg_left hr hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at hm
    linarith
  have hε' : 0 < ε * δ ^ A := mul_pos hε (Real.rpow_pos_of_pos hδ A)
  obtain ⟨M₀, hM₀, hsave⟩ := primeDirichletBlock_log_saving (R + 1) hA hε'
  have hxlim : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hxlim.eventually_ge_atTop (M₀ : ℝ), eventually_ge_atTop (2 : ℕ)]
    with X hlarge hX
  intro M N hXM hMX hNM s hs hlo hhi
  have hM₀M : M₀ ≤ M := by exact_mod_cast hlarge.trans hXM
  have hM : 2 ≤ M := hM₀.trans hM₀M
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlMX : Real.log (M : ℝ) ≤ Real.log X :=
    Real.log_le_log hMp (by exact_mod_cast hMX)
  have hlower : δ * Real.log (X : ℝ) ≤ Real.log M := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXp δ) hXM
    rwa [Real.log_rpow hXp] at h
  have hlo' : (Real.log M) ^ (2 * A + 9) ≤ |s.im| :=
    (Real.rpow_le_rpow hlM.le hlMX (by linarith)).trans hlo
  have hhi' : |s.im| ≤ (M : ℝ) ^ (R + 1) :=
    hhi.trans (power_length_frequency_upper (by exact_mod_cast (show 1 ≤ X by omega)) hXM hR)
  have hb := hsave M N hM₀M hNM s hs hlo' hhi'
  apply hb.trans
  have hLMpow : 0 < (Real.log M) ^ A := Real.rpow_pos_of_pos hlM A
  have hLXpow : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hlX A
  apply (div_le_div_iff₀ hLMpow hLXpow).mpr
  have hlogpow := Real.rpow_le_rpow (mul_nonneg hδ.le hlX.le) hlower hA
  rw [Real.mul_rpow hδ.le hlX.le] at hlogpow
  have hm := mul_le_mul_of_nonneg_left hlogpow hε.le
  nlinarith

end Erdos421
