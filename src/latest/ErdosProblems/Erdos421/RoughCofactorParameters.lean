import ErdosProblems.Erdos421.RoughSquareCutoff
import ErdosProblems.Erdos421.PrimeReciprocalBands

/-! # Uniform cofactor scales in the finite Buchstab induction -/

namespace Erdos421

theorem log_le_nat_power_scale {b z : ℝ} {k : ℕ}
    (hb : 0 < b) (hpow : b ≤ z ^ k) :
    Real.log b ≤ (k : ℝ) * Real.log z := by
  have h := Real.log_le_log hb hpow
  rwa [Real.log_pow] at h

theorem rough_cofactor_scale {a b : ℝ} {n z p : ℕ}
    (hb : 16 ≤ b) (ha : b / 2 ≤ a) (hab : a ≤ b) (hz : 2 ≤ z)
    (hbz : b ≤ (z : ℝ) ^ (n + 3)) (hp : p ∈ sievePrimes z (roughSquareCutoff b)) :
    2 ≤ p ∧ (p : ℝ) ≤ b / p ∧ b / p ≤ (p : ℝ) ^ (n + 2) ∧
      (b / p) / 2 ≤ a / p ∧ a / p ≤ b / p ∧ Real.sqrt b ≤ b / p ∧
      Real.log b / 2 ≤ Real.log (b / p) ∧ Real.log b ≤ ((n : ℝ) + 3) * Real.log p := by
  obtain ⟨hpp, hzp, hps⟩ := (mem_sievePrimes_square_cutoff b z p).mp hp
  have hpr : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hzr : (0 : ℝ) ≤ z := Nat.cast_nonneg _
  have hzpr : (z : ℝ) ≤ p := by exact_mod_cast hzp
  have hbp : 0 < b := by linarith
  have hsp := Real.sqrt_pos.mpr hbp
  have hsq := Real.sq_sqrt hbp.le
  have hpow : b ≤ (p : ℝ) ^ (n + 3) :=
    hbz.trans (pow_le_pow_left₀ hzr hzpr (n + 3))
  have hpc : (p : ℝ) ≤ b / p := by
    apply (le_div_iff₀ hpr).mpr
    have hp2 := (Real.le_sqrt hpr.le hbp.le).mp hps
    nlinarith
  have hsc : Real.sqrt b ≤ b / p := by
    apply (le_div_iff₀ hpr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hps hsp.le]
  have hlog := Real.log_le_log hsp hsc
  rw [Real.log_sqrt hbp.le] at hlog
  have hscale := log_le_nat_power_scale hbp hpow
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hscale
  refine ⟨hz.trans hzp, hpc, ?_, ?_,
    div_le_div_of_nonneg_right hab hpr.le, hsc, hlog, hscale⟩
  · apply (div_le_iff₀ hpr).mpr
    simpa only [show n + 3 = (n + 2) + 1 by omega, pow_succ] using hpow
  · have h := div_le_div_of_nonneg_right ha hpr.le
    rw [div_right_comm b (p : ℝ) 2]
    exact h

theorem rough_cofactor_reciprocal_mass {b : ℝ} {n z : ℕ}
    (hb : 16 ≤ b) (hz : 2 ≤ z) (hbz : b ≤ (z : ℝ) ^ (n + 3)) :
    (∑ p ∈ sievePrimes z (roughSquareCutoff b), (p : ℝ)⁻¹) ≤ 8 * ((n : ℝ) + 3) := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hbp : 0 < b := by linarith
  have hs : 2 ≤ Real.sqrt b := Real.le_sqrt_of_sq_le (by nlinarith)
  have hm := finite_prime_reciprocal_band_le (sievePrimes z (roughSquareCutoff b)) hz1 hs (by
    intro p hp
    obtain ⟨hpp, hzp, hps⟩ := (mem_sievePrimes_square_cutoff b z p).mp hp
    exact ⟨hpp, by exact_mod_cast hzp, hps⟩)
  have hscale := log_le_nat_power_scale hbp hbz
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hscale
  apply hm.trans
  rw [Real.log_sqrt hbp.le]
  apply (div_le_iff₀ (Real.log_pos hz1)).mpr
  nlinarith

end Erdos421
