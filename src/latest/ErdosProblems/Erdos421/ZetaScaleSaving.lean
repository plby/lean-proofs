import ErdosProblems.Erdos421.ZetaLogSaving

/-! # Zeta factors whose length is a fixed power of the ambient scale -/

namespace Erdos421

open Filter Topology

theorem power_length_frequency_upper {X M : ℝ} (hX : 1 ≤ X) {δ : ℝ}
    (hXM : X ^ δ ≤ M) {R : ℕ} (hR : 1 ≤ δ * (R + 1)) :
    X ≤ M ^ (R + 1) := by
  have hXp : 0 < X := by linarith
  calc
    X = X ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ X ^ (δ * (R + 1)) := Real.rpow_le_rpow_of_exponent_le hX hR
    _ = (X ^ δ) ^ (R + 1) := by
      rw [Real.rpow_mul hXp.le, show (R : ℝ) + 1 = ((R + 1 : ℕ) : ℝ) by simp,
        Real.rpow_natCast]
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hXM _

/-- Uniform cancellation for ordinary zeta factors at the ambient scale
used in the sieve argument. No prime-distribution statement is assumed. -/
theorem zetaBlock_ambient_log_saving {δ : ℝ} (hδ : 0 < δ)
    {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M N : ℕ, (X : ℝ) ^ δ ≤ M → M ≤ X → N ≤ M →
      ∀ s : ℂ, 1 ≤ s.re → (Real.log X) ^ (A + 1) ≤ |s.im| → |s.im| ≤ X →
        ‖zetaBlock M N s‖ ≤ ε / (Real.log X) ^ A := by
  let R := ⌈δ⁻¹⌉₊
  let K := 2 * R + 4
  have hR : 1 ≤ δ * ((R : ℝ) + 1) := by
    have hr : δ⁻¹ ≤ (R : ℝ) := Nat.le_ceil _
    have hm := mul_le_mul_of_nonneg_left hr hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at hm
    linarith
  have hε' : 0 < ε * δ ^ A := mul_pos hε (Real.rpow_pos_of_pos hδ A)
  obtain ⟨M₀, hM₀⟩ := (eventually_atTop.1
    (zetaBlock_eventually_log_saving R K le_rfl A hε'))
  have hxlim : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hxlim.eventually_ge_atTop (max (M₀ : ℝ) 2), eventually_ge_atTop 2]
    with X hlarge hX
  intro M N hXM hMX hNM s hs hlo hhi
  have hM₀M : M₀ ≤ M := by
    exact_mod_cast (le_max_left (M₀ : ℝ) 2).trans (hlarge.trans hXM)
  have hM : 2 ≤ M := by
    exact_mod_cast (le_max_right (M₀ : ℝ) 2).trans (hlarge.trans hXM)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlMX : Real.log (M : ℝ) ≤ Real.log X :=
    Real.log_le_log hMp (by exact_mod_cast hMX)
  have hlower : δ * Real.log (X : ℝ) ≤ Real.log M := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXp δ) hXM
    rwa [Real.log_rpow hXp] at h
  have hlo' : (Real.log M) ^ (A + 1) ≤ |s.im| :=
    (Real.rpow_le_rpow hlM.le hlMX (by linarith)).trans hlo
  have hhi' : |s.im| ≤ (M : ℝ) ^ (R + 1) :=
    hhi.trans (power_length_frequency_upper (by exact_mod_cast (show 1 ≤ X by omega)) hXM hR)
  have hb := hM₀ M hM₀M N hNM s hs hlo' hhi'
  apply hb.trans
  have hLMpow : 0 < (Real.log M) ^ A := Real.rpow_pos_of_pos hlM A
  have hLXpow : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hlX A
  apply (div_le_div_iff₀ hLMpow hLXpow).mpr
  have hlogpow := Real.rpow_le_rpow (mul_nonneg hδ.le hlX.le) hlower hA
  rw [Real.mul_rpow hδ.le hlX.le] at hlogpow
  have hm := mul_le_mul_of_nonneg_left hlogpow hε.le
  nlinarith

end Erdos421
