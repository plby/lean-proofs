import ErdosProblems.Erdos6.GenericS2Error

/-!
# Vanishing of the normalized generic `S₂` error
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

private def tupleTauLogPower (H : Finset ℕ) : ℕ :=
  (3 * Fintype.card H) ^ 2

private def tupleCoefficientLogPower (H : Finset ℕ) : ℕ :=
  4 * (Fintype.card H) ^ 2

private def tupleEnvelopeLogPower (H : Finset ℕ) : ℕ :=
  tupleTauLogPower H + tupleCoefficientLogPower H

private def tupleS2TauHalfLogExponent (H : Finset ℕ) : ℕ :=
  tupleTauLogPower H + tupleCoefficientLogPower H +
    3 * (Fintype.card H + 1) + 2

def tupleS2TauEnvelopeConstant
    (H : Finset ℕ) (alpha B C : ℝ) : ℝ :=
  B ^ 2 * (1 + alpha) ^ tupleCoefficientLogPower H *
    ((2 * Fintype.card H : ℕ) *
      ((Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
        4 ^ tupleTauLogPower H * 2 ^ tupleS2TauHalfLogExponent H))

theorem tupleS2TauEnvelopeConstant_nonneg
    {H : Finset ℕ} {alpha B C : ℝ}
    (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ tupleS2TauEnvelopeConstant H alpha B C := by
  unfold tupleS2TauEnvelopeConstant
  positivity

theorem eventually_tupleMaynardScale_ge_nat_div_modulus_pow
    (H : Finset ℕ) {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (maynardModulus N : ℝ) ^ (Fintype.card H + 1) ≤
        tupleMaynardScale H alpha N := by
  have hreal : Tendsto
      (fun N : ℕ => BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
      atTop atTop := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply (tendsto_rpow_atTop halpha).comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hlog : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) := by
    filter_upwards [hreal.eventually (eventually_ge_atTop (Real.exp 1))] with N hN
    have hmono : Real.log (Real.exp 1) ≤
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) :=
      Real.strictMonoOn_log.monotoneOn
        (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
        (by exact lt_of_lt_of_le (by positivity) hN) hN
    simpa using hmono
  filter_upwards [hlog, eventually_ge_atTop 1] with N hlog hN
  have hWpos : 0 < maynardModulus N := primorial_pos _
  have hphi : 1 ≤ (Nat.totient (maynardModulus N) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hWpos))
  have hnum : (N : ℝ) ≤
      (Nat.totient (maynardModulus N) : ℝ) ^ Fintype.card H * (N : ℝ) *
        (Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
          Fintype.card H := by
    calc
      (N : ℝ) = 1 * (N : ℝ) * 1 := by ring
      _ ≤ _ := by
        gcongr
        · exact one_le_pow₀ hphi
        · exact one_le_pow₀ hlog
  unfold tupleMaynardScale BoundedGaps.Maynard.maynardSieveScale
  exact div_le_div_of_nonneg_right hnum (by positivity)

theorem eventually_tupleMaynardS2TauErrorEnvelope_le_log_ratio
    (H : Finset ℕ) {theta delta B C : ℝ}
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      tupleMaynardS2TauErrorEnvelope H (theta / 2 - delta) B
          ((tupleS2TauHalfLogExponent H * 2 : ℕ) : ℝ) C N ≤
        tupleS2TauEnvelopeConstant H (theta / 2 - delta) B C * (N : ℝ) *
          (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H /
            (Real.log (N : ℝ)) ^ tupleS2TauHalfLogExponent H := by
  let alpha := theta / 2 - delta
  let P := tupleS2TauHalfLogExponent H
  let Q := fun N => maynardModulus N * maynardRadius alpha N *
    maynardRadius alpha N
  let E : ℝ := (Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
    4 ^ tupleTauLogPower H * 2 ^ P
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hthetaOne : theta ≤ 1 := by linarith
  have hcut := eventually_tupleMaynardS2_endpoint_cutoffs H htheta.le hdelta
  have hlogR :=
    BoundedGaps.Maynard.eventually_one_add_log_engelsmaMaynardRadius_le halpha
  have hlogN : ∀ᶠ N : ℕ in atTop,
      max 2 (2 * Real.log 2) ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop (max 2 (2 * Real.log 2)))
  have hRpos : ∀ᶠ N : ℕ in atTop, 1 ≤ maynardRadius alpha N := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    unfold maynardRadius BoundedGaps.Maynard.engelsmaMaynardRadius
      BoundedGaps.Maynard.maynardDivisorCutoff
    apply Nat.le_floor
    have hreal := BoundedGaps.Maynard.maynardRealCutoff_gt_one
      (alpha := alpha) (N := N - 1) (show 1 < N - 1 by omega) halpha
    unfold BoundedGaps.Maynard.maynardRealCutoff at hreal
    simpa only [Nat.cast_one] using hreal.le
  filter_upwards [hcut, hlogR, hlogN, hRpos,
    eventually_ge_atTop (max 6 (tupleBound H + 2))] with
      N hcut hlogR hlogN hRpos hN
  have hLN : 2 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlogN
  have hLNpos : 0 < Real.log (N : ℝ) := by linarith
  have hQpos : 1 ≤ Q N := by
    dsimp [Q]
    exact one_le_mul (one_le_mul (primorial_pos _) hRpos) hRpos
  have hlogQnonneg : 0 ≤ 1 + Real.log (Q N) := by
    have hQreal : (1 : ℝ) ≤ (Q N : ℝ) := by exact_mod_cast hQpos
    linarith [Real.log_nonneg hQreal]
  have hendpoint (x : ℕ)
      (hcutx : Q N ≤ BoundedGaps.Maynard.modulusCutoff theta x)
      (hxLower : N - 1 ≤ x) (hxUpper : x + 1 ≤ 3 * N) :
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) x ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ tupleTauLogPower H /
          (Real.log (N : ℝ)) ^ P := by
    have hxOne : 1 ≤ x := by omega
    have hQx : Q N ≤ x := hcutx.trans
      (BoundedGaps.Maynard.modulusCutoff_le_self hxOne hthetaOne)
    have hxcast : ((x + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      exact_mod_cast hxUpper
    have hhalfCast : (N : ℝ) / 2 ≤ (x : ℝ) := by
      have hxcast' : ((N - 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast hxLower
      have hNcast : (N : ℝ) / 2 ≤ ((N - 1 : ℕ) : ℝ) := by
        have hc : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show N ≤ 2 * (N - 1) by omega)
        linarith
      exact hNcast.trans hxcast'
    have hNreal : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hlogHalf : Real.log (N : ℝ) / 2 ≤ Real.log ((N : ℝ) / 2) := by
      rw [Real.log_div hNreal.ne'
        (by norm_num : (2 : ℝ) ≠ 0)]
      have hlog2 := (le_max_right 2 (2 * Real.log 2)).trans hlogN
      linarith
    have hlogx : Real.log (N : ℝ) / 2 ≤ Real.log (x : ℝ) :=
      hlogHalf.trans (Real.log_le_log (by positivity : (0 : ℝ) < N / 2) hhalfCast)
    have hQle : (Q N : ℝ) ≤ 3 * (N : ℝ) := by
      exact_mod_cast (show Q N ≤ 3 * N by omega)
    have hlogQle : Real.log (Q N) ≤ Real.log (3 * (N : ℝ)) :=
      Real.log_le_log (by exact_mod_cast (show 0 < Q N by omega)) hQle
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      norm_num at h
      exact h
    have hlogQBound : 1 + Real.log (Q N) ≤ 4 * Real.log (N : ℝ) := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
        hNreal.ne'] at hlogQle
      nlinarith
    simpa [E, P, tupleTauLogPower] using
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope_le_nat_log_ratio
        (H := H) (Q := Q N) (x := x) (N := N) (B := P)
        hC hLN hxcast hlogx hlogQnonneg hlogQBound
  have hshiftBound (h : H) : h.1 ≤ N := by
    exact (mem_le_tupleBound h.2).trans (by omega)
  have hupper : ∀ h : H,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (2 * N + h.1 - 1) ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ tupleTauLogPower H /
          (Real.log (N : ℝ)) ^ P := by
    intro h
    apply hendpoint
    · exact (hcut h).2
    · omega
    · have hh := hshiftBound h; omega
  have hlower : ∀ h : H,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (N + h.1 - 1) ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ tupleTauLogPower H /
          (Real.log (N : ℝ)) ^ P := by
    intro h
    apply hendpoint
    · exact (hcut h).1
    · omega
    · have hh := hshiftBound h; omega
  have hsumUpper :
      (∑ h : H, BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (2 * N + h.1 - 1)) ≤
        ∑ _h : H, E * (N : ℝ) *
          (Real.log (N : ℝ)) ^ tupleTauLogPower H /
            (Real.log (N : ℝ)) ^ P := by
    apply Finset.sum_le_sum
    intro h _
    exact hupper h
  have hsumLower :
      (∑ h : H, BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (N + h.1 - 1)) ≤
        ∑ _h : H, E * (N : ℝ) *
          (Real.log (N : ℝ)) ^ tupleTauLogPower H /
            (Real.log (N : ℝ)) ^ P := by
    apply Finset.sum_le_sum
    intro h _
    exact hlower h
  have hsum :
      (∑ h : H, BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (2 * N + h.1 - 1)) +
        ∑ h : H, BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (N + h.1 - 1) ≤
        (2 * Fintype.card H : ℕ) *
          (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tupleTauLogPower H /
            (Real.log (N : ℝ)) ^ P) := by
    calc
      _ ≤ (Fintype.card H : ℝ) *
              (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tupleTauLogPower H /
                (Real.log (N : ℝ)) ^ P) +
            (Fintype.card H : ℝ) *
              (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tupleTauLogPower H /
                (Real.log (N : ℝ)) ^ P) := by
          simpa [Finset.sum_const, nsmul_eq_mul] using add_le_add hsumUpper hsumLower
      _ = _ := by push_cast; ring
  have hLRnonneg : 0 ≤ 1 + Real.log (maynardRadius alpha N) := by
    have hRreal : (1 : ℝ) ≤ maynardRadius alpha N := by exact_mod_cast hRpos
    linarith [Real.log_nonneg hRreal]
  have hCoeffPow :
      (1 + Real.log (maynardRadius alpha N)) ^ tupleCoefficientLogPower H ≤
        ((1 + alpha) * Real.log (N : ℝ)) ^ tupleCoefficientLogPower H :=
    pow_le_pow_left₀ hLRnonneg hlogR _
  have hCoeff :
      (tupleMaynardSharpCoefficientEnvelope H alpha B N) ^ 2 ≤
        B ^ 2 * ((1 + alpha) * Real.log (N : ℝ)) ^
          tupleCoefficientLogPower H := by
    unfold tupleMaynardSharpCoefficientEnvelope
    calc
      (B * (1 + Real.log (maynardRadius alpha N)) ^
          (2 * Fintype.card H ^ 2)) ^ 2 =
          B ^ 2 * (1 + Real.log (maynardRadius alpha N)) ^
            tupleCoefficientLogPower H := by
        rw [mul_pow, ← pow_mul]
        congr 2
        unfold tupleCoefficientLogPower
        omega
      _ ≤ _ := mul_le_mul_of_nonneg_left hCoeffPow (sq_nonneg B)
  have hTauSumNonneg : 0 ≤
      (∑ h : H, BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (2 * N + h.1 - 1)) +
        ∑ h : H, BoundedGaps.Maynard.tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (N + h.1 - 1) := by
    apply add_nonneg <;> apply Finset.sum_nonneg <;> intro h _ <;>
      unfold BoundedGaps.Maynard.tauIndexedEndpointEnvelope <;> positivity
  have hlogPower :
      (Real.log (N : ℝ)) ^ tupleCoefficientLogPower H *
          (Real.log (N : ℝ)) ^ tupleTauLogPower H =
        (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H := by
    unfold tupleEnvelopeLogPower
    rw [pow_add]
    ring
  unfold tupleMaynardS2TauErrorEnvelope
  change (tupleMaynardSharpCoefficientEnvelope H alpha B N) ^ 2 * _ ≤ _
  calc
    _ ≤ (B ^ 2 * ((1 + alpha) * Real.log (N : ℝ)) ^
          tupleCoefficientLogPower H) *
        ((2 * Fintype.card H : ℕ) *
          (E * (N : ℝ) * (Real.log (N : ℝ)) ^ tupleTauLogPower H /
            (Real.log (N : ℝ)) ^ P)) :=
      mul_le_mul hCoeff hsum hTauSumNonneg (by positivity)
    _ = tupleS2TauEnvelopeConstant H alpha B C * (N : ℝ) *
          (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H /
            (Real.log (N : ℝ)) ^ tupleS2TauHalfLogExponent H := by
      rw [← hlogPower]
      dsimp [tupleS2TauEnvelopeConstant, E, P, tupleEnvelopeLogPower,
        tupleCoefficientLogPower, tupleTauLogPower]
      rw [mul_pow]
      ring

theorem tendsto_tupleMaynardS2TauErrorEnvelope_div_scale
    (H : Finset ℕ) {theta delta B C : ℝ}
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hC : 0 ≤ C) :
    Tendsto
      (fun N : ℕ =>
        tupleMaynardS2TauErrorEnvelope H (theta / 2 - delta) B
            ((tupleS2TauHalfLogExponent H * 2 : ℕ) : ℝ) C N /
          tupleMaynardScale H (theta / 2 - delta) N)
      atTop (nhds 0) := by
  let alpha := theta / 2 - delta
  let K := tupleS2TauEnvelopeConstant H alpha B C
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hK : 0 ≤ K := tupleS2TauEnvelopeConstant_nonneg halpha hC
  have hEnvelope := eventually_tupleMaynardS2TauErrorEnvelope_le_log_ratio
    H (B := B) htheta hthetaHalf hdelta hdeltaTheta hC
  have hScale := eventually_tupleMaynardScale_ge_nat_div_modulus_pow H halpha
  have hScalePos := eventually_tupleMaynardScale_pos (H := H) halpha
  have hW := BoundedGaps.Maynard.eventually_engelsmaMaynardModulus_le_log_cube
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 1)
  have hmajorant : Tendsto
      (fun N : ℕ => K / (Real.log (N : ℝ)) ^ 2) atTop (nhds 0) := by
    exact ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))).const_div_atTop K
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hmajorant
  filter_upwards [hEnvelope, hScale, hScalePos, hW, hlogN,
    eventually_ge_atTop 1] with N hEnvelope hScale hScalePos hW hlogN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hWpos : 0 < (maynardModulus N : ℝ) := by exact_mod_cast primorial_pos _
  have hLN : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogN
  have hWpow : (maynardModulus N : ℝ) ^ (Fintype.card H + 1) ≤
      (Real.log (N : ℝ)) ^ (3 * (Fintype.card H + 1)) := by
    calc
      _ ≤ ((Real.log (N : ℝ)) ^ 3) ^ (Fintype.card H + 1) :=
        pow_le_pow_left₀ hWpos.le hW _
      _ = _ := by rw [← pow_mul]
  have hLowerPos : 0 < (N : ℝ) /
      (maynardModulus N : ℝ) ^ (Fintype.card H + 1) := by positivity
  have hMajorNonneg : 0 ≤ K * (N : ℝ) *
      (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H /
        (Real.log (N : ℝ)) ^ tupleS2TauHalfLogExponent H := by positivity
  have hEnvelopeNonneg : 0 ≤ tupleMaynardS2TauErrorEnvelope H alpha B
      ((tupleS2TauHalfLogExponent H * 2 : ℕ) : ℝ) C N := by
    unfold tupleMaynardS2TauErrorEnvelope
    apply mul_nonneg (sq_nonneg _)
    apply add_nonneg <;> apply Finset.sum_nonneg <;> intro h _ <;>
      unfold BoundedGaps.Maynard.tauIndexedEndpointEnvelope <;> positivity
  rw [abs_of_nonneg (div_nonneg hEnvelopeNonneg hScalePos.le)]
  calc
    _ ≤ (K * (N : ℝ) *
          (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H /
            (Real.log (N : ℝ)) ^ tupleS2TauHalfLogExponent H) /
        tupleMaynardScale H alpha N :=
      div_le_div_of_nonneg_right hEnvelope hScalePos.le
    _ ≤ (K * (N : ℝ) *
          (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H /
            (Real.log (N : ℝ)) ^ tupleS2TauHalfLogExponent H) /
        ((N : ℝ) / (maynardModulus N : ℝ) ^ (Fintype.card H + 1)) := by
      exact div_le_div_of_nonneg_left hMajorNonneg hLowerPos hScale
    _ = K * (maynardModulus N : ℝ) ^ (Fintype.card H + 1) *
          (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H /
            (Real.log (N : ℝ)) ^ tupleS2TauHalfLogExponent H := by field_simp
    _ ≤ K * (Real.log (N : ℝ)) ^ (3 * (Fintype.card H + 1)) *
          (Real.log (N : ℝ)) ^ tupleEnvelopeLogPower H /
            (Real.log (N : ℝ)) ^ tupleS2TauHalfLogExponent H := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWpow hK)
          (pow_nonneg hLN.le _)
      · positivity
    _ = K / (Real.log (N : ℝ)) ^ 2 := by
      have hExp : tupleS2TauHalfLogExponent H =
          3 * (Fintype.card H + 1) + tupleEnvelopeLogPower H + 2 := by
        unfold tupleS2TauHalfLogExponent tupleEnvelopeLogPower
        omega
      rw [hExp, pow_add, pow_add]
      field_simp

theorem tendsto_normalized_tupleMaynardS2Error_zero_of_primeLevel
    (H : Finset ℕ) (hH : H.Nonempty) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hv : ∀ N h, h ∈ H → Nat.Coprime (v N + h) (maynardModulus N))
    {theta delta : ℝ} (htheta : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2)
    (hlevel : BoundedGaps.Maynard.hasPrimeLevel theta) :
    Tendsto (fun N : ℕ =>
      tupleMaynardS2Error H (theta / 2 - delta) v F N /
        tupleMaynardScale H (theta / 2 - delta) N) atTop (nhds 0) := by
  let A : ℝ := ((tupleS2TauHalfLogExponent H * 2 : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp [A, tupleS2TauHalfLogExponent, tupleTauLogPower,
      tupleCoefficientLogPower]
    positivity
  obtain ⟨C, X₀, hw, hbound⟩ := exists_tupleMaynardS2Error_tau_envelope
    H hH v F B hB hF hv htheta.le hthetaHalf hdelta hlevel hA
  have henv := tendsto_tupleMaynardS2TauErrorEnvelope_div_scale H
    (B := B) htheta hthetaHalf hdelta hdeltaTheta hw.1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [hbound, eventually_tupleMaynardScale_pos
    (H := H) (sub_pos.mpr hdeltaTheta)] with N hbound hscale
  rw [abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right hbound hscale.le

end

end Erdos6.Maynard
