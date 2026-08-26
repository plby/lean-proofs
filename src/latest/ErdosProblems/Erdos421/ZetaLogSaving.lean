import ErdosProblems.Erdos421.ZetaFrequencyBounds
import ErdosProblems.Erdos421.PowerSavingAsymptotics

/-! # Uniform logarithmic savings for finite zeta factors -/

namespace Erdos421

open Filter Topology

noncomputable def zetaLogError (M R K : ℕ) (A : ℝ) : ℝ :=
  24 / Real.log M + 4 * logarithmicPowerSaving M R K * (Real.log M) ^ A

theorem zetaLogError_tendsto (R : ℕ) {K : ℕ} (hK : 0 < K) (A : ℝ) :
    Tendsto (fun M : ℕ ↦ zetaLogError M R K A) atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ ↦ Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun M : ℕ ↦ 24 / Real.log M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlarge := (logarithmicPowerSaving_mul_log_tendsto R hK A).const_mul 4
  simpa only [zetaLogError, mul_zero, add_zero, ← mul_assoc] using hsmall.add hlarge

/-- The error is uniform in the block endpoint, the real part, and all
imaginary parts in the indicated range. -/
theorem zetaBlock_mul_log_bound {M N : ℕ} (hM : 2 ≤ M) (hN : N ≤ M)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) (A : ℝ) (s : ℂ) (hs : 1 ≤ s.re)
    (hlo : (Real.log M) ^ (A + 1) ≤ |s.im|) (hhi : |s.im| ≤ (M : ℝ) ^ (R + 1)) :
    ‖zetaBlock M N s‖ * (Real.log M) ^ A ≤ zetaLogError M R K A := by
  have hMp : 0 < M := by omega
  have hl : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hpow : 0 < (Real.log M) ^ (A + 1) := Real.rpow_pos_of_pos hl _
  have ht : s.im ≠ 0 := abs_pos.mp (hpow.trans_le hlo)
  have hb := zetaBlock_all_frequency_bound_of_one_le_re hMp hN R K hK s hs ht hhi
  have hweight : 0 < (Real.log M) ^ A := Real.rpow_pos_of_pos hl _
  have hfrac : 24 / |s.im| * (Real.log M) ^ A ≤ 24 / Real.log M := by
    calc
      _ ≤ (24 / (Real.log M) ^ (A + 1)) * (Real.log M) ^ A :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hpow hlo) hweight.le
      _ = _ := by
        rw [Real.rpow_add hl, Real.rpow_one]
        field_simp
  have hm := mul_le_mul_of_nonneg_right hb hweight.le
  unfold zetaLogError
  nlinarith

/-- Every fixed logarithmic saving holds uniformly once the frequency
exceeds the next logarithmic power. This has no prime coefficient. -/
theorem zetaBlock_eventually_log_saving (R K : ℕ) (hK : 2 * R + 4 ≤ K)
    (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ N ≤ M, ∀ s : ℂ, 1 ≤ s.re →
      (Real.log M) ^ (A + 1) ≤ |s.im| → |s.im| ≤ (M : ℝ) ^ (R + 1) →
      ‖zetaBlock M N s‖ ≤ ε / (Real.log M) ^ A := by
  have ht := (zetaLogError_tendsto R (by omega : 0 < K) A).eventually_lt_const hε
  filter_upwards [ht, eventually_ge_atTop 2] with M herror hM
  intro N hN s hs hlo hhi
  have hl : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hl A)).mpr
  exact (zetaBlock_mul_log_bound hM hN R K hK A s hs hlo hhi).trans herror.le

end Erdos421
