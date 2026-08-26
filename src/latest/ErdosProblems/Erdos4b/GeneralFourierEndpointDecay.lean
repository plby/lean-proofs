/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierMassGrowth

/-!
# Decay of the normalized source endpoint envelope

The first-family support has width `1/10`. Once the companion log scale
and primorial logarithm are sufficiently small fractions of the ambient
log scale, the normalized endpoint error has an exponentially decaying
envelope times a fixed polynomial.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped Topology

theorem sourceSelbergProductMassBound_nonneg (K : ℕ) {C : ℝ} (hC : 0 ≤ C) (A LD LE : ℝ) :
    0 ≤ sourceSelbergProductMassBound K C A LD LE := by
  unfold sourceSelbergProductMassBound
  exact mul_nonneg
    (mul_nonneg hC (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (one_add_log_ceil_exp_nonneg _) _)))
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (one_add_log_ceil_exp_nonneg _) _))

theorem sourceSelbergProductMassBound_le_eighth_exp
    (K : ℕ) {C LE V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hE : 0 ≤ LE) (hEV : LE ≤ V)
    (hsmall : (K : ℝ) * LE ≤ V / 40) :
    sourceSelbergProductMassBound K C (1 / 10) V LE ≤
      4 * C * ((K : ℝ) + 2) ^ (2 * K) * (V + 1) ^ (2 * K) * Real.exp (V / 8) := by
  apply (sourceSelbergProductMassBound_le_exp_poly K hC
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) ≤ 1)
    hV hE le_rfl hEV hV).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
  positivity

theorem normalized_sourceEndpointEnvelope_le
    (K : ℕ) {C LE V P T : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hE : 0 ≤ LE)
    (hEV : LE ≤ V) (hsmall : (K : ℝ) * LE ≤ V / 40)
    (hP0 : 0 ≤ P) (hP : P ≤ Real.exp (V / 8)) (hT : Real.exp (V / 2) ≤ T) :
    4 * V ^ (2 * K) * P * sourceSelbergProductMassBound K C (1 / 10) V LE ^ 2 / T ≤
      64 * C ^ 2 * ((K : ℝ) + 2) ^ (4 * K) * (V + 1) ^ (6 * K) * Real.exp (-V / 8) := by
  have hmass := sourceSelbergProductMassBound_le_eighth_exp K hC hV hE hEV hsmall
  have hmass0 := sourceSelbergProductMassBound_nonneg K hC (1 / 10) V LE
  have hVpow : V ^ (2 * K) ≤ (V + 1) ^ (2 * K) :=
    pow_le_pow_left₀ hV (by linarith) _
  have hexp : Real.exp (V / 8) ^ 3 / Real.exp (V / 2) = Real.exp (-V / 8) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    ring
  calc
    _ ≤ (4 * (V + 1) ^ (2 * K) * Real.exp (V / 8) *
        (4 * C * ((K : ℝ) + 2) ^ (2 * K) * (V + 1) ^ (2 * K) * Real.exp (V / 8)) ^ 2) /
          Real.exp (V / 2) := by
      apply div_le_div₀ (by positivity) _ (Real.exp_pos _) hT
      apply mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hVpow (by norm_num)) hP hP0 (by positivity))
        ((sq_le_sq₀ hmass0 (hmass0.trans hmass)).mpr hmass) (sq_nonneg _) (by positivity)
    _ = (64 * C ^ 2 * ((K : ℝ) + 2) ^ (4 * K) * (V + 1) ^ (6 * K)) *
        (Real.exp (V / 8) ^ 3 / Real.exp (V / 2)) := by
      rw [show 2 * K = K * 2 from Nat.mul_comm _ _,
        show 4 * K = K * 4 from Nat.mul_comm _ _, show 6 * K = K * 6 from Nat.mul_comm _ _]
      simp only [pow_mul]
      ring
    _ = _ := by rw [hexp]

theorem tendsto_shifted_pow_mul_eighth_exp_zero
    {α : Type*} {l : Filter α} (n : ℕ) {V : α → ℝ} (hV : Tendsto V l atTop) :
    Tendsto (fun a ↦ (V a + 1) ^ n * Real.exp (-V a / 8)) l (𝓝 0) := by
  have hplus : Tendsto (fun a ↦ V a + 1) l atTop :=
    hV.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hsmall := isLittleO_pow_exp_pos_mul_atTop n (by norm_num : (0 : ℝ) < 1 / 8)
  have h := hsmall.tendsto_div_nhds_zero.comp hplus
  have hlim := h.const_mul (Real.exp (1 / 8))
  simp only [mul_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro a
  change Real.exp (1 / 8) * ((V a + 1) ^ n / Real.exp ((1 / 8) * (V a + 1))) = _
  simp only [div_eq_mul_inv]
  rw [← Real.exp_neg, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem tendsto_normalized_sourceEndpointEnvelope_zero
    {α : Type*} {l : Filter α} (K : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (V LE P T : α → ℝ) (hV : Tendsto V l atTop)
    (hdata : ∀ᶠ a in l, 0 ≤ LE a ∧ LE a ≤ V a ∧ (K : ℝ) * LE a ≤ V a / 40 ∧
      0 ≤ P a ∧ P a ≤ Real.exp (V a / 8) ∧ Real.exp (V a / 2) ≤ T a) :
    Tendsto (fun a ↦ 4 * V a ^ (2 * K) * P a *
      sourceSelbergProductMassBound K C (1 / 10) (V a) (LE a) ^ 2 / T a) l (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hdata, hV.eventually_ge_atTop 0] with a ha hVa
    have hTa : 0 < T a := (Real.exp_pos _).trans_le ha.2.2.2.2.2
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg hVa _)) ha.2.2.2.1) (sq_nonneg _)) hTa.le
  · filter_upwards [hdata, hV.eventually_ge_atTop 0] with a ha hVa
    exact normalized_sourceEndpointEnvelope_le K hC hVa ha.1 ha.2.1 ha.2.2.1
      ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2
  · have hlim := (tendsto_shifted_pow_mul_eighth_exp_zero (6 * K) hV).const_mul
      (64 * C ^ 2 * ((K : ℝ) + 2) ^ (4 * K))
    simpa only [mul_zero, mul_assoc] using hlim

end

end Erdos4b
