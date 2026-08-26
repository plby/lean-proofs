import ErdosProblems.Erdos421.RoundedPrimeCutoffs
import ErdosProblems.Erdos421.RoughEulerHarmonic
import ErdosProblems.Erdos421.PrimeReciprocalBands
import ErdosProblems.Erdos421.RoundedTransferSupport

/-! # The two elementary main-error bounds for the explicit prime cutoffs -/

namespace Erdos421

open Filter Topology

theorem smallPrimeCutoff_euler_error {X β ε : ℝ} (hX : 1 < X) (hβ : 0 < β) (hε : 0 ≤ ε) :
    ε * roughEulerProduct (smallPrimeCutoff X β) ≤ (ε / β) / Real.log X := by
  have hXp : 0 < X := by linarith
  have hlog := Real.log_pos hX
  have hW := smallPrimeCutoff_two_le (β := β) hXp
  have hpow : X ^ β ≤ smallPrimeCutoff X β :=
    (smallPrimeCutoff_bounds hX.le hβ.le).1.trans (by exact_mod_cast
      (Nat.sub_le (smallPrimeCutoff X β) 1))
  have hlogW := Real.log_le_log (Real.rpow_pos_of_pos hXp β) hpow
  rw [Real.log_rpow hXp] at hlogW
  have hV := (roughEulerProduct_le_inv_log hW).trans
    (inv_anti₀ (mul_pos hβ hlog) hlogW)
  calc
    _ ≤ ε * (β * Real.log X)⁻¹ := mul_le_mul_of_nonneg_left hV hε
    _ = _ := by field_simp

theorem eventually_outer_prime_reciprocal_bound :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X), (p : ℝ)⁻¹) ≤ 42 := by
  have hpower : ∀ᶠ X : ℕ in atTop, 2 ≤ (X : ℝ) ^ (51 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 51 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [eventually_outer_cutoff_bound, hpower, eventually_ge_atTop 2] with X hQ hpowerX hX
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hz := (roundedPowerCutoff_bounds hXone.le (by norm_num : (0 : ℝ) ≤ 39 / 200)).1
  have hb := finite_prime_reciprocal_power_band
    (sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X)) hXone
    (by norm_num : (0 : ℝ) < 39 / 200) hpowerX (by
      intro p hp
      obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpZ, hpQ⟩ := Finset.mem_Ico.mp hpI
      refine ⟨hpp, hz.trans (by exact_mod_cast hpZ), ?_⟩
      have hpQr : (p : ℝ) ≤ outerPrimeCutoff X := by exact_mod_cast hpQ.le
      exact hpQr.trans hQ)
  norm_num at hb
  linarith

end Erdos421
