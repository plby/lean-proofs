import ErdosProblems.Erdos237.LogErrorLimit
import BoundedGaps.Maynard.ImprovedGPY.S2TauShiftedAggregation

/-! Generic logarithmic control of the tau-weighted prime-progression error. -/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

def s2HalfLogExponent (H : Finset ℕ) : ℕ :=
  (3 * Fintype.card H) ^ 2 + 4 * Fintype.card H ^ 2 + 3 * (Fintype.card H + 1) + 2

noncomputable def s2TauErrorEnvelope (H : Finset ℕ) (alpha B C : ℝ) (N : ℕ) : ℝ :=
  (B * (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (2 * Fintype.card H ^ 2)) ^ 2 *
    ((∑ h : H, tauIndexedEndpointEnvelope H
      (engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N * engelsmaMaynardRadius alpha N)
      C ((s2HalfLogExponent H * 2 : ℕ) : ℝ) (2 * N + h.val - 1)) +
    ∑ h : H, tauIndexedEndpointEnvelope H
      (engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N * engelsmaMaynardRadius alpha N)
      C ((s2HalfLogExponent H * 2 : ℕ) : ℝ) (N + h.val - 1))

noncomputable def s2TauErrorConstant (H : Finset ℕ) (alpha B C : ℝ) : ℝ :=
  B ^ 2 * (1 + alpha) ^ (4 * Fintype.card H ^ 2) * (2 * Fintype.card H) *
    ((Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
      4 ^ ((3 * Fintype.card H) ^ 2) * 2 ^ s2HalfLogExponent H)

theorem tauEndpoint_le_nearby {H : Finset ℕ} {Q x N b : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hN : 2 ≤ N) (hQpos : 0 < Q) (hQ : Q ≤ N - 1)
    (hxLower : N - 1 ≤ x) (hxUpper : x + 1 ≤ 3 * N)
    (hlogN : max 2 (2 * Real.log 2) ≤ Real.log (N : ℝ)) :
    tauIndexedEndpointEnvelope H Q C ((b * 2 : ℕ) : ℝ) x ≤
      ((Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
        4 ^ ((3 * Fintype.card H) ^ 2) * 2 ^ b) *
        N * Real.log (N : ℝ) ^ ((3 * Fintype.card H) ^ 2) / Real.log (N : ℝ) ^ b := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 2 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlogN
  have hhalf : (N : ℝ) / 2 ≤ x := by
    have hc : (N : ℝ) ≤ 2 * x := by exact_mod_cast (show N ≤ 2 * x by omega)
    linarith
  have hloghalf : Real.log (N : ℝ) / 2 ≤ Real.log ((N : ℝ) / 2) := by
    rw [Real.log_div hn.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have ht := (le_max_right 2 (2 * Real.log 2)).trans hlogN
    linarith
  have hlogx := hloghalf.trans (Real.log_le_log (by positivity) hhalf)
  have hlogQle : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast (show Q ≤ N by omega))
  exact tauIndexedEndpointEnvelope_le_nat_log_ratio hC hln (by exact_mod_cast hxUpper)
    hlogx (by positivity) (by linarith)

theorem eventually_s2TauErrorEnvelope_le_log_ratio {H : Finset ℕ}
    {theta delta B C : ℝ} (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, s2TauErrorEnvelope H (theta / 2 - delta) B C N ≤
      s2TauErrorConstant H (theta / 2 - delta) B C * N *
        Real.log (N : ℝ) ^ ((3 * Fintype.card H) ^ 2 + 4 * Fintype.card H ^ 2) /
          Real.log (N : ℝ) ^ s2HalfLogExponent H := by
  let alpha := theta / 2 - delta
  let k := Fintype.card H
  let p := (3 * k) ^ 2
  let b := s2HalfLogExponent H
  let E : ℝ := (k : ℝ) * (3 * (C + 1)) * 3 * 4 ^ p * 2 ^ b
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_engelsmaMaynard_modulus_radius_cutoff htheta.le hdelta,
    eventually_one_add_log_engelsmaMaynardRadius_le halpha,
    eventually_one_lt_engelsmaMaynardRadius halpha,
    hlog.eventually_ge_atTop (max 2 (2 * Real.log 2)),
    eventually_ge_atTop 2, eventually_ge_atTop (H.sup id)] with N hcut hRlog hR hlogN hN hH
  let Q := engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N * engelsmaMaynardRadius alpha N
  have hQpos : 0 < Q := by
    have hw : 0 < engelsmaMaynardModulus N := primorial_pos _
    dsimp [Q]
    positivity
  have hQ : Q ≤ N - 1 := by
    apply (hcut 0).trans
    simpa using modulusCutoff_le_self (show 1 ≤ N - 1 by omega) (by linarith : theta ≤ 1)
  have hx (h : H) : h.val ≤ N := (le_sup (f := id) h.property).trans hH
  have hupper (h : H) : tauIndexedEndpointEnvelope H Q C ((b * 2 : ℕ) : ℝ)
      (2 * N + h.val - 1) ≤ E * N * Real.log (N : ℝ) ^ p / Real.log (N : ℝ) ^ b :=
    tauEndpoint_le_nearby hC hN hQpos hQ (by omega) (by have := hx h; omega) hlogN
  have hlower (h : H) : tauIndexedEndpointEnvelope H Q C ((b * 2 : ℕ) : ℝ)
      (N + h.val - 1) ≤ E * N * Real.log (N : ℝ) ^ p / Real.log (N : ℝ) ^ b :=
    tauEndpoint_le_nearby hC hN hQpos hQ (by omega) (by have := hx h; omega) hlogN
  have hsum : ((∑ h : H, tauIndexedEndpointEnvelope H Q C ((b * 2 : ℕ) : ℝ)
      (2 * N + h.val - 1)) + ∑ h : H, tauIndexedEndpointEnvelope H Q C ((b * 2 : ℕ) : ℝ)
      (N + h.val - 1)) ≤
      (2 * k : ℝ) * (E * N * Real.log (N : ℝ) ^ p / Real.log (N : ℝ) ^ b) := by
    have hu := sum_le_sum fun h (_ : h ∈ (univ : Finset H)) => hupper h
    have hl := sum_le_sum fun h (_ : h ∈ (univ : Finset H)) => hlower h
    simpa only [sum_const, card_univ, nsmul_eq_mul, ← two_mul, mul_assoc, k] using add_le_add hu hl
  have hcoef : (B * (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (2 * k ^ 2)) ^ 2 ≤
      B ^ 2 * ((1 + alpha) * Real.log (N : ℝ)) ^ (4 * k ^ 2) := by
    rw [mul_pow, ← pow_mul, show 2 * k ^ 2 * 2 = 4 * k ^ 2 by omega]
    gcongr
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hLN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hsum0 : 0 ≤ ((∑ h : H, tauIndexedEndpointEnvelope H Q C ((b * 2 : ℕ) : ℝ)
      (2 * N + h.val - 1)) + ∑ h : H, tauIndexedEndpointEnvelope H Q C ((b * 2 : ℕ) : ℝ)
      (N + h.val - 1)) := by unfold tauIndexedEndpointEnvelope; positivity
  calc
    _ ≤ (B ^ 2 * ((1 + alpha) * Real.log (N : ℝ)) ^ (4 * k ^ 2)) *
        ((2 * k : ℝ) * (E * N * Real.log (N : ℝ) ^ p / Real.log (N : ℝ) ^ b)) :=
      mul_le_mul hcoef hsum hsum0 (by positivity)
    _ = _ := by
      simp only [mul_pow, pow_add, s2TauErrorConstant]
      dsimp [alpha, k, E, p, b]
      ring

theorem tendsto_normalized_s2TauErrorEnvelope {H : Finset ℕ} {theta delta B C : ℝ}
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2) (hC : 0 ≤ C) :
    Tendsto (fun N : ℕ => s2TauErrorEnvelope H (theta / 2 - delta) B C N /
      sieveScale H (theta / 2 - delta) N) atTop (nhds 0) := by
  have halpha : 0 < theta / 2 - delta := by linarith
  apply tendsto_normalized_of_log_bound halpha
    (show 0 ≤ s2TauErrorConstant H (theta / 2 - delta) B C by
      unfold s2TauErrorConstant
      positivity)
    ((3 * Fintype.card H) ^ 2 + 4 * Fintype.card H ^ 2)
  filter_upwards [eventually_s2TauErrorEnvelope_le_log_ratio
    (H := H) (B := B) htheta hthetaHalf hdelta hdeltaTheta hC] with N hN
  rw [abs_of_nonneg (show 0 ≤ s2TauErrorEnvelope H (theta / 2 - delta) B C N by
    unfold s2TauErrorEnvelope tauIndexedEndpointEnvelope
    positivity)]
  exact hN

end Erdos237
