import ErdosProblems.Erdos421.RoughCofactorParameters
import ErdosProblems.Erdos421.SqrtBoundaryParameters

/-! # Uniform cutoff thresholds and logarithmic errors at the parent scale -/

namespace Erdos421

open Filter Topology

theorem power_cutoff_large (k : ℕ) (hk : 0 < k) (Y : ℝ) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ z : ℕ, b ≤ (z : ℝ) ^ k →
      Y ≤ z ∧ 1 ≤ Real.log z := by
  let T : ℝ := max Y (Real.exp 1)
  refine ⟨max 2 (T ^ k), (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _), ?_⟩
  intro b hb z hbz
  have hTz : T ≤ z := le_of_pow_le_pow_left₀ hk.ne' (Nat.cast_nonneg z)
    (((le_max_right _ _).trans hb).trans hbz)
  have hez : Real.exp 1 ≤ z := (le_max_right _ _).trans hTz
  have hlog := Real.log_le_log (Real.exp_pos 1) hez
  rw [Real.log_exp] at hlog
  exact ⟨(le_max_left _ _).trans hTz, hlog⟩

theorem scaled_log_saving_le {b z K A ε : ℝ} (hb : 1 < b) (hz : 1 < z)
    (hK : 0 < K) (hA : 0 ≤ A) (hε : 0 ≤ ε) (hscale : Real.log b ≤ K * Real.log z) :
    (ε / K ^ A) / (Real.log z) ^ A ≤ ε / (Real.log b) ^ A := by
  have hLb := Real.log_pos hb
  have hLz := Real.log_pos hz
  have hKA := Real.rpow_pos_of_pos hK A
  have hinv := inverse_rpow_of_lower_scale hK hLb hLz hA
    ((div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hscale))
  calc
    _ = (ε / K ^ A) * (1 / (Real.log z) ^ A) := by ring
    _ ≤ (ε / K ^ A) * (K ^ A / (Real.log b) ^ A) :=
      mul_le_mul_of_nonneg_left hinv (div_nonneg hε hKA.le)
    _ = _ := by field_simp

theorem buchstab_endpoint_log_saving (n : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ z : ℕ, 2 ≤ z → b ≤ (z : ℝ) ^ (n + 3) →
      1 / ((z : ℝ) * Real.log z) ≤ ε / (Real.log b) ^ A := by
  let K : ℝ := (n : ℝ) + 3
  have hK : 0 < K := by dsimp only [K]; positivity
  let η : ℝ := ε / K ^ A
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (eventually_constant_le_log_scale (by norm_num : (0 : ℝ) ≤ 1) hη A)
  obtain ⟨B, hB, hcut⟩ := power_cutoff_large (n + 3) (by omega) Y
  refine ⟨B, hB, ?_⟩
  intro b hb z hz hbz
  obtain ⟨hYz, hlogz⟩ := hcut b hb z hbz
  have hb1 := hB.trans_le hb
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hzp : (0 : ℝ) < z := by linarith
  have hsmall := hY (z : ℝ) hYz
  have hinv : 1 / (z : ℝ) ≤ η / (Real.log z) ^ A := by
    apply (div_le_iff₀ hzp).mpr
    calc
      1 ≤ η * z / (Real.log z) ^ A := hsmall
      _ = _ := by ring
  have hscale : Real.log b ≤ K * Real.log z := by
    have h := log_le_nat_power_scale (by linarith : 0 < b) hbz
    simpa only [Nat.cast_add, Nat.cast_ofNat, K] using h
  calc
    _ ≤ 1 / (z : ℝ) := div_le_div_of_nonneg_left (by norm_num) hzp (by nlinarith)
    _ ≤ η / (Real.log z) ^ A := hinv
    _ ≤ _ := scaled_log_saving_le hb1 hz1 hK hA hε.le hscale

end Erdos421
