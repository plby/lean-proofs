import ErdosProblems.Erdos67b.MRCofactorPowerCutoff
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic scales for the ordinary cofactor projection

The prime near term requires the Mertens estimate, rather than the crude
harmonic bound. Polynomial logarithmic masses are absorbed by the cutoff.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrTendsto_log_pow_div_cofactorPowerCutoff {delta : ℝ} (hdelta : 0 < delta) (k : ℕ) :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) ^ k / (mrCofactorPowerCutoff delta X : ℝ)) atTop (𝓝 0) := by
  have hpoly : (fun r : ℝ ↦ r ^ k) =o[atTop] (fun r : ℝ ↦ Real.exp (delta * r)) := by
    simpa only [Real.rpow_natCast] using isLittleO_rpow_exp_pos_mul_atTop (k : ℝ) hdelta
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact div_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hX)) _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact div_le_div_of_nonneg_left (pow_nonneg (Real.log_nonneg (by exact_mod_cast hX)) _)
      (Real.exp_pos _) (mrCofactorPowerCutoff_exp_le delta X)
  · exact (hpoly.comp_tendsto EulerSubpower.tendsto_log_nat_atTop).tendsto_div_nhds_zero

theorem mrTendsto_inv_log_cofactorPowerCutoff {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun X : ℕ ↦ (Real.log (mrCofactorPowerCutoff delta X : ℝ))⁻¹) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (mrCofactorPowerCutoff delta X : ℝ)) atTop atTop :=
    EulerSubpower.tendsto_log_nat_atTop.comp (mrTendsto_cofactorPowerCutoff hdelta)
  exact hlog.inv_tendsto_atTop

theorem mrCofactor_log_two_mul_le {X : ℕ} (hX : 2 ≤ X) :
    Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) := by
  have hXpos : (0 : ℝ) < X := by positivity
  have hlog2 : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hX)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hXpos.ne']
  linarith

theorem mrCofactor_harmonic_two_mul_le {X : ℕ} (hX : 2 ≤ X) (hlog : 1 ≤ Real.log (X : ℝ)) :
    (harmonic (2 * X) : ℝ) ≤ 3 * Real.log (X : ℝ) := by
  exact (harmonic_le_one_add_log (2 * X)).trans (by linarith [mrCofactor_log_two_mul_le hX])

def mrCofactorPrimeMajorant (X : ℕ) : ℝ :=
  Real.log (Real.log (X : ℝ)) + (Real.log 2 + PrimeEstimates.mertensBound)

theorem mrCofactor_primeReciprocals_two_mul_le {X : ℕ} (hX : 2 ≤ X) :
    PrimeEstimates.primeReciprocals (2 * X) ≤ mrCofactorPrimeMajorant X := by
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h2L : 0 < Real.log ((2 * X : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hmertens := (abs_le.mp (PrimeEstimates.abs_primeReciprocals_sub_log_log_le
    (show 2 ≤ 2 * X by omega))).2
  have hlog := Real.log_le_log h2L (mrCofactor_log_two_mul_le hX)
  rw [Real.log_mul (by norm_num) hL.ne'] at hlog
  unfold mrCofactorPrimeMajorant
  linarith

theorem mrTendsto_cofactorPrimeMajorant_div_log :
    Tendsto (fun X : ℕ ↦ mrCofactorPrimeMajorant X / Real.log (X : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, pow_one] using
      (Real.isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero.comp
        EulerSubpower.tendsto_log_nat_atTop
  have hconst := EulerSubpower.tendsto_log_nat_atTop.const_div_atTop
    (Real.log 2 + PrimeEstimates.mertensBound)
  simpa only [mrCofactorPrimeMajorant, add_div, zero_add] using hlog.add hconst

theorem mrTendsto_cofactorPrimeMajorant_sq_div_log :
    Tendsto (fun X : ℕ ↦ mrCofactorPrimeMajorant X ^ 2 / Real.log (X : ℝ)) atTop (𝓝 0) := by
  let A := Real.log 2 + PrimeEstimates.mertensBound
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, pow_one] using
      (Real.isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero.comp
        EulerSubpower.tendsto_log_nat_atTop
  have hsq : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)) ^ 2 / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp
        EulerSubpower.tendsto_log_nat_atTop
  have hconst := EulerSubpower.tendsto_log_nat_atTop.const_div_atTop (A ^ 2)
  have ht := (hsq.add (hlog.const_mul (2 * A))).add hconst
  simp only [mul_zero, zero_add] at ht
  convert ht using 1
  funext X
  dsimp only [mrCofactorPrimeMajorant, A]
  ring

theorem mrTendsto_primeReciprocals_two_mul_div_log :
    Tendsto (fun X : ℕ ↦ PrimeEstimates.primeReciprocals (2 * X) / Real.log (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact div_nonneg (PrimeEstimates.primeReciprocals_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact div_le_div_of_nonneg_right (mrCofactor_primeReciprocals_two_mul_le hX)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
  · exact mrTendsto_cofactorPrimeMajorant_div_log

theorem mrTendsto_primeReciprocals_two_mul_sq_div_log :
    Tendsto (fun X : ℕ ↦ PrimeEstimates.primeReciprocals (2 * X) ^ 2 / Real.log (X : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact div_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (PrimeEstimates.primeReciprocals_nonneg _) (mrCofactor_primeReciprocals_two_mul_le hX) 2)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
  · exact mrTendsto_cofactorPrimeMajorant_sq_div_log

theorem mrPrimeReciprocals_mono {X Y : ℕ} (hXY : X ≤ Y) :
    PrimeEstimates.primeReciprocals X ≤ PrimeEstimates.primeReciprocals Y := by
  unfold PrimeEstimates.primeReciprocals Erdos784.Analytic.primeReciprocals
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.2 ⟨(Nat.mem_primesLE.1 hp).1.trans hXY, (Nat.mem_primesLE.1 hp).2⟩
  · intro p hp hnot
    positivity

theorem mrEventually_primeReciprocals_two_mul_le_log :
    ∀ᶠ X : ℕ in atTop, PrimeEstimates.primeReciprocals (2 * X) ≤ Real.log (X : ℝ) := by
  filter_upwards [(tendsto_order.1 mrTendsto_primeReciprocals_two_mul_div_log).2 1 zero_lt_one,
    eventually_ge_atTop 2] with X hsmall hX
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  exact (div_le_one hL).1 hsmall.le

theorem mrEventually_primeReciprocals_le_log :
    ∀ᶠ X : ℕ in atTop, PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ) := by
  filter_upwards [mrEventually_primeReciprocals_two_mul_le_log] with X hX
  exact (mrPrimeReciprocals_mono (show X ≤ 2 * X by omega)).trans hX

theorem mrTendsto_harmonic_two_mul_div_log_sq :
    Tendsto (fun X : ℕ ↦ (harmonic (2 * X) : ℝ) / Real.log (X : ℝ) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero'
  · apply Eventually.of_forall
    intro X
    apply div_nonneg _ (sq_nonneg _)
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun i hi ↦ by positivity)
  · filter_upwards [eventually_ge_atTop 2,
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)] with X hX hlog
    have hL : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlog
    calc
      _ ≤ 3 * Real.log (X : ℝ) / Real.log (X : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mrCofactor_harmonic_two_mul_le hX hlog) (sq_nonneg _)
      _ = 3 / Real.log (X : ℝ) := by field_simp
  · exact EulerSubpower.tendsto_log_nat_atTop.const_div_atTop 3

end

end Erdos67b
