import ErdosProblems.Erdos372.Erdos372AffineError

/-!
# Vanishing of the normalized affine second-moment error
-/

namespace Erdos372.AffineMaynard

open Filter Set
open scoped BigOperators
open Erdos6.Maynard
open BoundedGaps.Maynard

noncomputable section

private def affineTauLogPower (H : Finset ℕ) : ℕ :=
  (3 * Fintype.card H) ^ 2

private def affineCoefficientLogPower (H : Finset ℕ) : ℕ :=
  4 * (Fintype.card H) ^ 2

private def affineEnvelopeLogPower (H : Finset ℕ) : ℕ :=
  affineTauLogPower H + affineCoefficientLogPower H

private def affineS2HalfLogExponent (H : Finset ℕ) : ℕ :=
  affineEnvelopeLogPower H + 3 * (Fintype.card H + 1) + 2

def affineTupleMaynardS2TauErrorEnvelope
    (H : Finset ℕ) (A : H → ℕ) (alpha B E C : ℝ) (N : ℕ) : ℝ :=
  (tupleMaynardSharpCoefficientEnvelope H alpha B N) ^ 2 *
    ((∑ h : H, tauIndexedEndpointEnvelope H
      (maynardModulus N * maynardRadius alpha N * maynardRadius alpha N)
      C E (2 * A h * N)) +
    ∑ h : H, tauIndexedEndpointEnvelope H
      (maynardModulus N * maynardRadius alpha N * maynardRadius alpha N)
      C E (A h * N))

def affineS2TauEnvelopeConstant
    (H : Finset ℕ) (alpha B C : ℝ) : ℝ :=
  B ^ 2 * (1 + alpha) ^ affineCoefficientLogPower H *
    ((2 * Fintype.card H : ℕ) *
      ((Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
        4 ^ affineTauLogPower H * 2 ^ affineS2HalfLogExponent H))

theorem affineS2TauEnvelopeConstant_nonneg
    {H : Finset ℕ} {alpha B C : ℝ}
    (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ affineS2TauEnvelopeConstant H alpha B C := by
  unfold affineS2TauEnvelopeConstant
  positivity

def affineCoefficientSum {H : Finset ℕ} (A : H → ℕ) : ℕ :=
  ∑ h : H, A h

theorem affineCoefficient_le_sum {H : Finset ℕ} (A : H → ℕ)
    (hApos : ∀ h, 0 < A h) (h : H) : A h ≤ affineCoefficientSum A := by
  unfold affineCoefficientSum
  exact Finset.single_le_sum (fun i hi => (hApos i).le) (Finset.mem_univ h)

theorem affineCoefficientSum_pos {H : Finset ℕ} (hH : H.Nonempty)
    (A : H → ℕ) (hApos : ∀ h, 0 < A h) : 0 < affineCoefficientSum A := by
  obtain ⟨h, hh⟩ := hH
  let hs : H := ⟨h, hh⟩
  exact (hApos hs).trans_le (affineCoefficient_le_sum A hApos hs)

theorem eventually_const_mul_radius_sq_le
    {alpha beta : ℝ} (hbeta : 0 < beta) (hab : alpha < beta) (c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      c * maynardRadius alpha N * maynardRadius alpha N ≤
        maynardRadius beta N * maynardRadius beta N := by
  let gap := 2 * (beta - alpha)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hX : Tendsto (fun N : ℕ => ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hgapTop : Tendsto (fun N : ℕ =>
      Real.rpow ((N - 1 : ℕ) : ℝ) gap) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp hX
  have hbetaTop : Tendsto (fun N : ℕ =>
      Real.rpow ((N - 1 : ℕ) : ℝ) beta) atTop atTop :=
    (tendsto_rpow_atTop hbeta).comp hX
  filter_upwards [hgapTop.eventually (eventually_ge_atTop (4 * (c : ℝ))),
    hbetaTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 3] with N hGap hBeta hN
  let X : ℝ := ((N - 1 : ℕ) : ℝ)
  let Ra : ℝ := maynardRadius alpha N
  let Rb : ℝ := maynardRadius beta N
  have hXpos : 0 < X := by
    dsimp [X]
    exact_mod_cast (show 0 < N - 1 by omega)
  have hRaNonneg : 0 ≤ Ra := by positivity
  have hRbNonneg : 0 ≤ Rb := by positivity
  have hRa : Ra ≤ Real.rpow X alpha := by
    dsimp [Ra, X, maynardRadius, engelsmaMaynardRadius, maynardDivisorCutoff]
    exact Nat.floor_le (Real.rpow_nonneg hXpos.le alpha)
  have hRb : Real.rpow X beta / 2 ≤ Rb := by
    dsimp [Rb, X, maynardRadius, engelsmaMaynardRadius, maynardDivisorCutoff]
    have hBetaX : 2 ≤ Real.rpow X beta := by
      simpa [X] using hBeta
    have hsub : Real.rpow X beta / 2 ≤ Real.rpow X beta - 1 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    exact hsub.trans (Nat.sub_one_lt_floor (R := ℝ)
      (Real.rpow X beta)).le
  have hpowA : (Real.rpow X alpha) ^ 2 = Real.rpow X (2 * alpha) := by
    calc
      _ = Real.rpow X alpha * Real.rpow X alpha := pow_two _
      _ = Real.rpow X (alpha + alpha) :=
        (Real.rpow_add hXpos alpha alpha).symm
      _ = _ := by congr 1; ring
  have hpowB : (Real.rpow X beta) ^ 2 = Real.rpow X (2 * beta) := by
    calc
      _ = Real.rpow X beta * Real.rpow X beta := pow_two _
      _ = Real.rpow X (beta + beta) :=
        (Real.rpow_add hXpos beta beta).symm
      _ = _ := by congr 1; ring
  have hfactor : Real.rpow X (2 * beta) =
      Real.rpow X (2 * alpha) * Real.rpow X gap := by
    calc
      _ = Real.rpow X (2 * alpha + gap) := by
        congr 1
        dsimp [gap]
        ring
      _ = _ := Real.rpow_add hXpos (2 * alpha) gap
  have hcast : (c : ℝ) * Ra * Ra ≤ Rb * Rb := by
    have hPowANonneg : 0 ≤ Real.rpow X alpha :=
      Real.rpow_nonneg hXpos.le alpha
    have hPowBNonneg : 0 ≤ Real.rpow X beta :=
      Real.rpow_nonneg hXpos.le beta
    have hGap' : 4 * (c : ℝ) ≤ Real.rpow X gap := by
      simpa [X] using hGap
    have hBetaSq : (Real.rpow X beta) ^ 2 ≤ 4 * Rb ^ 2 := by
      nlinarith [hRb]
    have hRaSq : Ra ^ 2 ≤ (Real.rpow X alpha) ^ 2 :=
      by simpa [pow_two] using mul_self_le_mul_self hRaNonneg hRa
    have hGapMul := mul_le_mul_of_nonneg_left hGap'
      (sq_nonneg (Real.rpow X alpha))
    calc
      (c : ℝ) * Ra * Ra = (c : ℝ) * Ra ^ 2 := by ring
      _ ≤ (c : ℝ) * (Real.rpow X alpha) ^ 2 :=
        mul_le_mul_of_nonneg_left hRaSq (Nat.cast_nonneg _)
      _ ≤ (Real.rpow X alpha) ^ 2 * Real.rpow X gap / 4 := by
        nlinarith [hGapMul]
      _ = (Real.rpow X beta) ^ 2 / 4 := by
        rw [hpowA, hpowB, hfactor]
      _ ≤ Rb ^ 2 := by nlinarith
      _ = Rb * Rb := by ring
  dsimp [Ra, Rb] at hcast
  exact_mod_cast hcast

theorem eventually_affine_endpoint_cutoffs
    {H : Finset ℕ} (A : H → ℕ) (_hH : H.Nonempty)
    (hApos : ∀ h, 0 < A h) {theta delta : ℝ}
    (htheta : 0 ≤ theta) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ h : H,
      A h * (maynardModulus N * maynardRadius (theta / 2 - delta) N *
          maynardRadius (theta / 2 - delta) N) ≤
          modulusCutoff theta (A h * N) ∧
        A h * (maynardModulus N * maynardRadius (theta / 2 - delta) N *
          maynardRadius (theta / 2 - delta) N) ≤
          modulusCutoff theta (2 * A h * N) := by
  let c := affineCoefficientSum A
  let alpha := theta / 2 - delta
  let beta := theta / 2 - delta / 2
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith
  have hab : alpha < beta := by dsimp [alpha, beta]; linarith
  have hrad := eventually_const_mul_radius_sq_le hbeta hab c
  have hbase := eventually_engelsmaMaynard_modulus_radius_cutoff
    htheta (show 0 < delta / 2 by positivity)
  filter_upwards [hrad, hbase] with N hradN hbaseN h
  have hAh : A h ≤ c := affineCoefficient_le_sum A hApos h
  have hcompare : A h *
      (maynardModulus N * maynardRadius alpha N * maynardRadius alpha N) ≤
      maynardModulus N * maynardRadius beta N * maynardRadius beta N := by
    calc
      _ ≤ c * (maynardModulus N * maynardRadius alpha N *
          maynardRadius alpha N) := Nat.mul_le_mul_right _ hAh
      _ = maynardModulus N *
          (c * maynardRadius alpha N * maynardRadius alpha N) := by ring
      _ ≤ maynardModulus N *
          (maynardRadius beta N * maynardRadius beta N) :=
        Nat.mul_le_mul_left _ hradN
      _ = _ := by ring
  have hlow := hcompare.trans (hbaseN ((A h - 1) * N + 1))
  have hupp := hcompare.trans (hbaseN ((2 * A h - 1) * N + 1))
  have hAone : 1 ≤ A h := hApos h
  have h2Aone : 1 ≤ 2 * A h := by omega
  have hlowEq : N + ((A h - 1) * N + 1) - 1 = A h * N := by
    have heq := Nat.sub_add_cancel hAone
    calc
      _ = N + (A h - 1) * N := by omega
      _ = ((A h - 1) + 1) * N := by ring
      _ = _ := by rw [heq]
  have huppEq : N + ((2 * A h - 1) * N + 1) - 1 = 2 * A h * N := by
    have heq := Nat.sub_add_cancel h2Aone
    calc
      _ = N + (2 * A h - 1) * N := by omega
      _ = ((2 * A h - 1) + 1) * N := by ring
      _ = _ := by rw [heq]
  simpa [alpha, beta, hlowEq, huppEq] using And.intro hlow hupp

theorem eventually_affineTupleMaynardS2TauErrorEnvelope_le_log_ratio
    (H : Finset ℕ) (hH : H.Nonempty) (A : H → ℕ)
    (hApos : ∀ h, 0 < A h) {theta delta B C : ℝ}
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      affineTupleMaynardS2TauErrorEnvelope H A (theta / 2 - delta) B
          ((affineS2HalfLogExponent H * 2 : ℕ) : ℝ) C N ≤
        affineS2TauEnvelopeConstant H (theta / 2 - delta) B C *
          (affineCoefficientSum A * N : ℕ) *
          (Real.log (affineCoefficientSum A * N : ℕ)) ^
            affineEnvelopeLogPower H /
          (Real.log (affineCoefficientSum A * N : ℕ)) ^
            affineS2HalfLogExponent H := by
  let alpha := theta / 2 - delta
  let P := affineS2HalfLogExponent H
  let c := affineCoefficientSum A
  let Q := fun N => maynardModulus N * maynardRadius alpha N *
    maynardRadius alpha N
  let E : ℝ := (Fintype.card H : ℝ) * (3 * (C + 1)) * 3 *
    4 ^ affineTauLogPower H * 2 ^ P
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hcpos : 0 < c := affineCoefficientSum_pos hH A hApos
  have hcone : 1 ≤ c := hcpos
  have hthetaOne : theta ≤ 1 := by linarith
  have hbase := eventually_engelsmaMaynard_modulus_radius_cutoff
    htheta.le hdelta
  have hlogR := eventually_one_add_log_engelsmaMaynardRadius_le halpha
  have hlogN : ∀ᶠ N : ℕ in atTop,
      max 2 (2 * Real.log 2) ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop (max 2 (2 * Real.log 2)))
  have hRpos : ∀ᶠ N : ℕ in atTop, 1 ≤ maynardRadius alpha N := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    unfold maynardRadius engelsmaMaynardRadius maynardDivisorCutoff
    apply Nat.le_floor
    have hreal := maynardRealCutoff_gt_one
      (alpha := alpha) (N := N - 1) (show 1 < N - 1 by omega) halpha
    unfold maynardRealCutoff at hreal
    simpa only [Nat.cast_one] using hreal.le
  filter_upwards [hbase, hlogR, hlogN, hRpos,
    eventually_ge_atTop (max c 3)] with N hbase hlogR hlogN hRpos hN
  have hNpos : 0 < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcReal : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hMpos : (0 : ℝ) < (c * N : ℕ) := by positivity
  have hNc : c ≤ N := (le_max_left c 3).trans hN
  have hLN : 2 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlogN
  have hLNpos : 0 < Real.log (N : ℝ) := by linarith
  have hNleM : N ≤ c * N := by
    simpa [one_mul] using Nat.mul_le_mul_right N hcone
  have hlogNleM : Real.log (N : ℝ) ≤ Real.log (c * N : ℕ) :=
    Real.log_le_log hNreal (by exact_mod_cast hNleM)
  have hLM : 2 ≤ Real.log (c * N : ℕ) := hLN.trans hlogNleM
  have hlogcN : Real.log (c * N : ℕ) =
      Real.log (c : ℝ) + Real.log (N : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hcReal.ne' hNreal.ne']
  have hlogc_le_logN : Real.log (c : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hcReal (by exact_mod_cast hNc)
  have hhalfM : Real.log (c * N : ℕ) / 2 ≤ Real.log (N : ℝ) := by
    rw [hlogcN]
    linarith
  have hQN : Q N ≤ N := by
    have hb := hbase 1
    have hb' : Q N ≤ modulusCutoff theta N := by
      simpa [Q] using hb
    exact hb'.trans (modulusCutoff_le_self (by omega) hthetaOne)
  have hQpos : 1 ≤ Q N := by
    dsimp [Q]
    exact one_le_mul (one_le_mul (primorial_pos _) hRpos) hRpos
  have hQleM : Q N ≤ c * N := hQN.trans hNleM
  have hlogQnonneg : 0 ≤ 1 + Real.log (Q N) := by
    have hQreal : (1 : ℝ) ≤ (Q N : ℝ) := by exact_mod_cast hQpos
    linarith [Real.log_nonneg hQreal]
  have hlogQleM : Real.log (Q N) ≤ Real.log (c * N : ℕ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < Q N by omega)
    · exact_mod_cast hQleM
  have hlogQBound : 1 + Real.log (Q N) ≤
      4 * Real.log (c * N : ℕ) := by
    linarith
  have hendpoint (x : ℕ) (hxLower : N ≤ x)
      (hxUpper : x + 1 ≤ 3 * (c * N)) :
      tauIndexedEndpointEnvelope H (Q N) C ((P * 2 : ℕ) : ℝ) x ≤
        E * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
            (Real.log (c * N : ℕ)) ^ P := by
    have hxcast : ((x + 1 : ℕ) : ℝ) ≤ 3 * ((c * N : ℕ) : ℝ) := by
      exact_mod_cast hxUpper
    have hNx : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxLower
    have hlogx : Real.log (c * N : ℕ) / 2 ≤ Real.log (x : ℝ) :=
      hhalfM.trans (Real.log_le_log hNreal hNx)
    simpa [E, P, affineTauLogPower] using
      tauIndexedEndpointEnvelope_le_nat_log_ratio
        (H := H) (Q := Q N) (x := x) (N := c * N) (B := P)
        hC hLM hxcast hlogx hlogQnonneg hlogQBound
  have hupper : ∀ h : H,
      tauIndexedEndpointEnvelope H (Q N) C ((P * 2 : ℕ) : ℝ)
          (2 * A h * N) ≤
        E * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
            (Real.log (c * N : ℕ)) ^ P := by
    intro h
    have hAh := affineCoefficient_le_sum A hApos h
    have hAN : A h * N ≤ c * N := Nat.mul_le_mul_right N hAh
    have hOne : 1 ≤ c * N := Nat.mul_pos hcpos hNpos
    apply hendpoint
    · have hAone : 1 ≤ A h := hApos h
      calc
        N = 1 * N := by ring
        _ ≤ 2 * A h * N := by gcongr <;> omega
    · calc
        2 * A h * N + 1 ≤ 2 * (c * N) + 1 := by
          simpa [mul_assoc] using
            Nat.add_le_add_right (Nat.mul_le_mul_left 2 hAN) 1
        _ ≤ 3 * (c * N) := by omega
  have hlower : ∀ h : H,
      tauIndexedEndpointEnvelope H (Q N) C ((P * 2 : ℕ) : ℝ)
          (A h * N) ≤
        E * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
            (Real.log (c * N : ℕ)) ^ P := by
    intro h
    have hAh := affineCoefficient_le_sum A hApos h
    have hAN : A h * N ≤ c * N := Nat.mul_le_mul_right N hAh
    have hOne : 1 ≤ c * N := Nat.mul_pos hcpos hNpos
    apply hendpoint
    · have hAone : 1 ≤ A h := hApos h
      simpa [one_mul] using Nat.mul_le_mul_right N hAone
    · calc
        A h * N + 1 ≤ c * N + 1 := Nat.add_le_add_right hAN 1
        _ ≤ 3 * (c * N) := by omega
  have hsumUpper :
      (∑ h : H, tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (2 * A h * N)) ≤
        ∑ _h : H, E * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
            (Real.log (c * N : ℕ)) ^ P := by
    apply Finset.sum_le_sum
    intro h _
    exact hupper h
  have hsumLower :
      (∑ h : H, tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (A h * N)) ≤
        ∑ _h : H, E * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
            (Real.log (c * N : ℕ)) ^ P := by
    apply Finset.sum_le_sum
    intro h _
    exact hlower h
  have hsum :
      (∑ h : H, tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (2 * A h * N)) +
        ∑ h : H, tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (A h * N) ≤
        (2 * Fintype.card H : ℕ) *
          (E * (c * N : ℕ) *
            (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
              (Real.log (c * N : ℕ)) ^ P) := by
    calc
      _ ≤ (Fintype.card H : ℝ) *
              (E * (c * N : ℕ) *
                (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
                  (Real.log (c * N : ℕ)) ^ P) +
            (Fintype.card H : ℝ) *
              (E * (c * N : ℕ) *
                (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
                  (Real.log (c * N : ℕ)) ^ P) := by
          simpa [Finset.sum_const, nsmul_eq_mul] using
            add_le_add hsumUpper hsumLower
      _ = _ := by push_cast; ring
  have hLRnonneg : 0 ≤ 1 + Real.log (maynardRadius alpha N) := by
    have hRreal : (1 : ℝ) ≤ maynardRadius alpha N := by
      exact_mod_cast hRpos
    linarith [Real.log_nonneg hRreal]
  have hlogRM : 1 + Real.log (maynardRadius alpha N) ≤
      (1 + alpha) * Real.log (c * N : ℕ) :=
    hlogR.trans (mul_le_mul_of_nonneg_left hlogNleM (by linarith))
  have hCoeffPow :
      (1 + Real.log (maynardRadius alpha N)) ^ affineCoefficientLogPower H ≤
        ((1 + alpha) * Real.log (c * N : ℕ)) ^
          affineCoefficientLogPower H :=
    pow_le_pow_left₀ hLRnonneg hlogRM _
  have hCoeff :
      (tupleMaynardSharpCoefficientEnvelope H alpha B N) ^ 2 ≤
        B ^ 2 * ((1 + alpha) * Real.log (c * N : ℕ)) ^
          affineCoefficientLogPower H := by
    unfold tupleMaynardSharpCoefficientEnvelope
    calc
      (B * (1 + Real.log (maynardRadius alpha N)) ^
          (2 * Fintype.card H ^ 2)) ^ 2 =
          B ^ 2 * (1 + Real.log (maynardRadius alpha N)) ^
            affineCoefficientLogPower H := by
        rw [mul_pow, ← pow_mul]
        congr 2
        unfold affineCoefficientLogPower
        omega
      _ ≤ _ := mul_le_mul_of_nonneg_left hCoeffPow (sq_nonneg B)
  have hTauSumNonneg : 0 ≤
      (∑ h : H, tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (2 * A h * N)) +
        ∑ h : H, tauIndexedEndpointEnvelope H (Q N) C
          ((P * 2 : ℕ) : ℝ) (A h * N) := by
    apply add_nonneg <;> apply Finset.sum_nonneg <;> intro h _ <;>
      unfold tauIndexedEndpointEnvelope <;> positivity
  have hlogPower :
      (Real.log (c * N : ℕ)) ^ affineCoefficientLogPower H *
          (Real.log (c * N : ℕ)) ^ affineTauLogPower H =
        (Real.log (c * N : ℕ)) ^ affineEnvelopeLogPower H := by
    unfold affineEnvelopeLogPower
    rw [pow_add]
    ring
  unfold affineTupleMaynardS2TauErrorEnvelope
  change (tupleMaynardSharpCoefficientEnvelope H alpha B N) ^ 2 * _ ≤ _
  calc
    _ ≤ (B ^ 2 * ((1 + alpha) * Real.log (c * N : ℕ)) ^
          affineCoefficientLogPower H) *
        ((2 * Fintype.card H : ℕ) *
          (E * (c * N : ℕ) *
            (Real.log (c * N : ℕ)) ^ affineTauLogPower H /
              (Real.log (c * N : ℕ)) ^ P)) :=
      mul_le_mul hCoeff hsum hTauSumNonneg (by positivity)
    _ = affineS2TauEnvelopeConstant H alpha B C * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineEnvelopeLogPower H /
            (Real.log (c * N : ℕ)) ^ affineS2HalfLogExponent H := by
      rw [← hlogPower]
      dsimp [affineS2TauEnvelopeConstant, E, P, affineEnvelopeLogPower,
        affineCoefficientLogPower, affineTauLogPower]
      rw [mul_pow]
      ring

theorem tendsto_affineTupleMaynardS2TauErrorEnvelope_div_scale
    (H : Finset ℕ) (hH : H.Nonempty) (A : H → ℕ)
    (hApos : ∀ h, 0 < A h) {theta delta B C : ℝ}
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hC : 0 ≤ C) :
    Tendsto
      (fun N : ℕ =>
        affineTupleMaynardS2TauErrorEnvelope H A (theta / 2 - delta) B
            ((affineS2HalfLogExponent H * 2 : ℕ) : ℝ) C N /
          tupleMaynardScale H (theta / 2 - delta) N)
      atTop (nhds 0) := by
  let alpha := theta / 2 - delta
  let c := affineCoefficientSum A
  let K := affineS2TauEnvelopeConstant H alpha B C
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hcpos : 0 < c := affineCoefficientSum_pos hH A hApos
  have hcReal : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hK : 0 ≤ K := affineS2TauEnvelopeConstant_nonneg halpha hC
  have hEnvelope :=
    eventually_affineTupleMaynardS2TauErrorEnvelope_le_log_ratio
      H hH A hApos (B := B) htheta hthetaHalf hdelta hdeltaTheta hC
  have hScale := eventually_tupleMaynardScale_ge_nat_div_modulus_pow H halpha
  have hScalePos := eventually_tupleMaynardScale_pos (H := H) halpha
  have hW := eventually_engelsmaMaynardModulus_le_log_cube
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop 1)
  have hMtop : Tendsto (fun N : ℕ => (c : ℝ) * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hcReal
  have hmajorant : Tendsto
      (fun N : ℕ => (K * (c : ℝ)) /
        (Real.log (c * N : ℕ)) ^ 2) atTop (nhds 0) := by
    have hlogM : Tendsto (fun N : ℕ => Real.log ((c : ℝ) * (N : ℝ)))
        atTop atTop := Real.tendsto_log_atTop.comp hMtop
    have hpowM := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlogM
    simpa [Nat.cast_mul] using hpowM.const_div_atTop (K * (c : ℝ))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hmajorant
  filter_upwards [hEnvelope, hScale, hScalePos, hW, hlogN,
    eventually_ge_atTop 1] with N hEnvelope hScale hScalePos hW hlogN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hWpos : 0 < (maynardModulus N : ℝ) := by
    exact_mod_cast primorial_pos _
  have hLN : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogN
  have hNleM : N ≤ c * N := by
    simpa [one_mul] using Nat.mul_le_mul_right N (show 1 ≤ c from hcpos)
  have hlogNleM : Real.log (N : ℝ) ≤ Real.log (c * N : ℕ) :=
    Real.log_le_log hNreal (by exact_mod_cast hNleM)
  have hLM : 0 < Real.log (c * N : ℕ) := hLN.trans_le hlogNleM
  have hWpow : (maynardModulus N : ℝ) ^ (Fintype.card H + 1) ≤
      (Real.log (c * N : ℕ)) ^ (3 * (Fintype.card H + 1)) := by
    calc
      _ ≤ ((Real.log (N : ℝ)) ^ 3) ^ (Fintype.card H + 1) :=
        pow_le_pow_left₀ hWpos.le hW _
      _ = (Real.log (N : ℝ)) ^ (3 * (Fintype.card H + 1)) := by
        rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ hLN.le hlogNleM _
  have hLowerPos : 0 < (N : ℝ) /
      (maynardModulus N : ℝ) ^ (Fintype.card H + 1) := by positivity
  have hMajorNonneg : 0 ≤ K * (c * N : ℕ) *
      (Real.log (c * N : ℕ)) ^ affineEnvelopeLogPower H /
        (Real.log (c * N : ℕ)) ^ affineS2HalfLogExponent H := by
    positivity
  have hEnvelopeNonneg : 0 ≤
      affineTupleMaynardS2TauErrorEnvelope H A alpha B
        ((affineS2HalfLogExponent H * 2 : ℕ) : ℝ) C N := by
    unfold affineTupleMaynardS2TauErrorEnvelope
    apply mul_nonneg (sq_nonneg _)
    apply add_nonneg <;> apply Finset.sum_nonneg <;> intro h _ <;>
      unfold tauIndexedEndpointEnvelope <;> positivity
  rw [abs_of_nonneg (div_nonneg hEnvelopeNonneg hScalePos.le)]
  calc
    _ ≤ (K * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineEnvelopeLogPower H /
            (Real.log (c * N : ℕ)) ^ affineS2HalfLogExponent H) /
        tupleMaynardScale H alpha N :=
      div_le_div_of_nonneg_right hEnvelope hScalePos.le
    _ ≤ (K * (c * N : ℕ) *
          (Real.log (c * N : ℕ)) ^ affineEnvelopeLogPower H /
            (Real.log (c * N : ℕ)) ^ affineS2HalfLogExponent H) /
        ((N : ℝ) / (maynardModulus N : ℝ) ^ (Fintype.card H + 1)) := by
      exact div_le_div_of_nonneg_left hMajorNonneg hLowerPos hScale
    _ = (K * (c : ℝ)) *
          (maynardModulus N : ℝ) ^ (Fintype.card H + 1) *
          (Real.log (c * N : ℕ)) ^ affineEnvelopeLogPower H /
            (Real.log (c * N : ℕ)) ^ affineS2HalfLogExponent H := by
      push_cast
      field_simp
    _ ≤ (K * (c : ℝ)) *
          (Real.log (c * N : ℕ)) ^ (3 * (Fintype.card H + 1)) *
          (Real.log (c * N : ℕ)) ^ affineEnvelopeLogPower H /
            (Real.log (c * N : ℕ)) ^ affineS2HalfLogExponent H := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWpow (mul_nonneg hK hcReal.le))
          (pow_nonneg hLM.le _)
      · positivity
    _ = (K * (c : ℝ)) / (Real.log (c * N : ℕ)) ^ 2 := by
      have hExp : affineS2HalfLogExponent H =
          3 * (Fintype.card H + 1) + affineEnvelopeLogPower H + 2 := by
        unfold affineS2HalfLogExponent
        omega
      rw [hExp, pow_add, pow_add]
      field_simp

theorem eventually_affine_endpoint_thresholds
    {H : Finset ℕ} (A : H → ℕ) (hApos : ∀ h, 0 < A h) (X₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ h : H,
      X₀ ≤ A h * N ∧ X₀ ≤ 2 * A h * N := by
  filter_upwards [eventually_ge_atTop X₀] with N hN h
  have hAone : 1 ≤ A h := hApos h
  have hbase : N ≤ A h * N := by
    simpa [one_mul] using Nat.mul_le_mul_right N hAone
  have hdouble : A h * N ≤ 2 * A h * N := by
    calc
      A h * N = 1 * (A h * N) := by ring
      _ ≤ 2 * (A h * N) := Nat.mul_le_mul_right (A h * N) (by omega)
      _ = 2 * A h * N := by ring
  exact ⟨hN.trans hbase, (hN.trans hbase).trans hdouble⟩

theorem bound_abs_affineTupleMaynardS2Error_tau
    {theta alpha E C : ℝ} {X₀ : ℕ}
    (hw : PrimeLevelWitness theta E C X₀)
    (H : Finset ℕ) (hH : H.Nonempty) (A : H → ℕ)
    (hApos : ∀ h, 0 < A h)
    (F : (H → ℝ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (htheta : theta ≤ 1) (N : ℕ)
    (hcoverage : CoversCoefficientPrimes A (maynardModulus N) ∧
      CoversAffineDifferencePrimes A (maynardModulus N))
    (hN : 0 < N)
    (hupper : ∀ h : H, X₀ ≤ 2 * A h * N)
    (hlower : ∀ h : H, X₀ ≤ A h * N)
    (hcutUpper : ∀ h : H,
      A h * (maynardModulus N * maynardRadius alpha N *
        maynardRadius alpha N) ≤ modulusCutoff theta (2 * A h * N))
    (hcutLower : ∀ h : H,
      A h * (maynardModulus N * maynardRadius alpha N *
        maynardRadius alpha N) ≤ modulusCutoff theta (A h * N)) :
    |affineTupleMaynardS2Error H A alpha F N| ≤
      affineTupleMaynardS2TauErrorEnvelope H A alpha B E C N := by
  classical
  let D := tupleMaynardSupport H alpha N
  let lambda := tupleMaynardCoefficient H alpha F N
  let L := tupleMaynardSharpCoefficientEnvelope H alpha B N
  have hW : Squarefree (maynardModulus N) := by
    unfold maynardModulus engelsmaMaynardModulus
    exact BoundedGaps.Maynard.squarefree_primorial _
  have hD : ∀ d ∈ D, IsMaynardDivisorTuple H
      (maynardRadius alpha N) (maynardModulus N) d := by
    intro d hd
    exact tupleMaynardS2SupportProof H alpha N d (by simpa [D] using hd)
  have hL : 0 ≤ L := by
    dsimp [L, tupleMaynardSharpCoefficientEnvelope]
    positivity
  have hbound : ∀ d ∈ D, |lambda d| ≤ L := by
    intro d hd
    exact abs_maynardCoefficient_le_sharp_log H
      (maynardRadius alpha N) (maynardModulus N) F d B hB hF hH
      (by simpa [D, tupleMaynardSupport] using hd)
  have hsizeUpper : ∀ h : H,
      A h * (maynardModulus N * maynardRadius alpha N *
        maynardRadius alpha N) ≤ 2 * A h * N + 1 := by
    intro h
    exact (hcutUpper h).trans
      ((modulusCutoff_le_self
        (Nat.one_le_iff_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero (by norm_num) (hApos h).ne') hN.ne'))
        htheta).trans (Nat.le_succ _))
  have hsizeLower : ∀ h : H,
      A h * (maynardModulus N * maynardRadius alpha N *
        maynardRadius alpha N) ≤ A h * N + 1 := by
    intro h
    exact (hcutLower h).trans
      ((modulusCutoff_le_self
        (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (hApos h).ne' hN.ne'))
        htheta).trans (Nat.le_succ _))
  have herror := PrimeLevelWitness.bound_abs_affineRestrictedS2Error_tau
    hw hH hW hD hApos hcoverage.1 hcoverage.2 hN hL hbound
      hupper hlower hcutUpper hcutLower hsizeUpper hsizeLower
  simpa [affineTupleMaynardS2Error, affineTupleMaynardS2TauErrorEnvelope,
    D, lambda, L] using herror

theorem exists_affineTupleMaynardS2Error_tau_envelope
    (H : Finset ℕ) (hH : H.Nonempty) (A : H → ℕ)
    (hApos : ∀ h, 0 < A h) (hAinj : Function.Injective A)
    (F : (H → ℝ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    {theta delta E : ℝ} (htheta : 0 ≤ theta)
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2)
    (hlevel : hasPrimeLevel theta) (hE : 0 < E) :
    ∃ C : ℝ, ∃ X₀ : ℕ, PrimeLevelWitness theta E C X₀ ∧
      ∀ᶠ N : ℕ in atTop,
        |affineTupleMaynardS2Error H A (theta / 2 - delta) F N| ≤
          affineTupleMaynardS2TauErrorEnvelope H A (theta / 2 - delta) B E C N := by
  obtain ⟨C, X₀, hw⟩ := hasPrimeLevel_exists_witness hlevel hE
  refine ⟨C, X₀, hw, ?_⟩
  filter_upwards [eventually_affine_coverage A hApos hAinj,
    eventually_affine_endpoint_thresholds A hApos X₀,
    eventually_affine_endpoint_cutoffs A hH hApos htheta hdelta hdeltaTheta,
    eventually_ge_atTop 1] with N hcoverage hthresholds hcutoffs hN
  exact bound_abs_affineTupleMaynardS2Error_tau hw H hH A hApos F B hB hF
    (by linarith) N hcoverage (by omega)
    (fun h => (hthresholds h).2) (fun h => (hthresholds h).1)
    (fun h => (hcutoffs h).2) (fun h => (hcutoffs h).1)

theorem tendsto_normalized_affineTupleMaynardS2Error_zero_of_primeLevel
    (H : Finset ℕ) (hH : H.Nonempty) (A : H → ℕ)
    (hApos : ∀ h, 0 < A h) (hAinj : Function.Injective A)
    (F : (H → ℝ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    {theta delta : ℝ} (htheta : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2)
    (hlevel : hasPrimeLevel theta) :
    Tendsto (fun N : ℕ =>
      affineTupleMaynardS2Error H A (theta / 2 - delta) F N /
        tupleMaynardScale H (theta / 2 - delta) N) atTop (nhds 0) := by
  let E : ℝ := ((affineS2HalfLogExponent H * 2 : ℕ) : ℝ)
  have hE : 0 < E := by
    dsimp [E, affineS2HalfLogExponent, affineEnvelopeLogPower,
      affineTauLogPower, affineCoefficientLogPower]
    positivity
  obtain ⟨C, X₀, hw, hbound⟩ :=
    exists_affineTupleMaynardS2Error_tau_envelope H hH A hApos hAinj
      F B hB hF htheta.le hthetaHalf hdelta hdeltaTheta hlevel hE
  have henv := tendsto_affineTupleMaynardS2TauErrorEnvelope_div_scale
    H hH A hApos (B := B) htheta hthetaHalf hdelta hdeltaTheta hw.1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [hbound, eventually_tupleMaynardScale_pos
    (H := H) (sub_pos.mpr hdeltaTheta)] with N hbound hscale
  rw [abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right hbound hscale.le

end

end Erdos372.AffineMaynard
