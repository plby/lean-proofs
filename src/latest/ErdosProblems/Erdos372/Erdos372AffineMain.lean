import ErdosProblems.Erdos372.Erdos372AffinePrime

/-!
# Asymptotics for the main term of the affine Maynard sieve
-/

namespace Erdos372.AffineMaynard

open Filter
open scoped BigOperators
open Erdos6.Maynard
open BoundedGaps.Maynard

noncomputable section

theorem tendsto_log_nat_sub_one_div_log_const_mul
    (c : ℕ) (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      Real.log ((N - 1 : ℕ) : ℝ) / Real.log ((c * N : ℕ) : ℝ))
      atTop (nhds 1) := by
  have hsubNat : Tendsto (fun N : ℕ => N - 1) atTop atTop :=
    tendsto_sub_atTop_nat 1
  have hsubReal : Tendsto (fun N : ℕ => ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsubNat
  have hlogSub : Tendsto (fun N : ℕ =>
      Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hsubReal
  have hratio : Tendsto (fun N : ℕ =>
      ((c * N : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) atTop (nhds (c : ℝ)) := by
    have hsmall : Tendsto (fun N : ℕ =>
        (c : ℝ) / ((N - 1 : ℕ) : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hsubReal
    have hsum : Tendsto (fun N : ℕ =>
        (c : ℝ) + (c : ℝ) / ((N - 1 : ℕ) : ℝ))
        atTop (nhds ((c : ℝ) + 0)) := tendsto_const_nhds.add hsmall
    simpa using hsum.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      have hne : (N : ℝ) - 1 ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show N ≠ 1 by omega)
      field_simp [hne]
      ring)
  have hlogRatio : Tendsto (fun N : ℕ =>
      Real.log (((c * N : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)))
      atTop (nhds (Real.log (c : ℝ))) :=
    hratio.log (by exact_mod_cast hc.ne')
  have hsmall : Tendsto (fun N : ℕ =>
      Real.log (((c * N : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) /
        Real.log ((N - 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    hlogRatio.div_atTop hlogSub
  have hden : Tendsto (fun N : ℕ =>
      1 + Real.log (((c * N : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) /
        Real.log ((N - 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv : Tendsto (fun N : ℕ =>
      1 / (1 + Real.log (((c * N : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) /
        Real.log ((N - 1 : ℕ) : ℝ))) atTop (nhds 1) := by
    change Tendsto ((fun _ : ℕ => (1 : ℝ)) /
      (fun N : ℕ => 1 +
        Real.log (((c * N : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) /
          Real.log ((N - 1 : ℕ) : ℝ))) atTop (nhds 1)
    simpa only [div_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1)).div hden one_ne_zero)
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hsubPos : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N - 1 by omega)
  have hmulPos : (0 : ℝ) < ((c * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hc (by omega : 0 < N)
  have hlogSubNe : Real.log ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by exact_mod_cast (show 1 < N - 1 by omega))
  have hlogMulNe : Real.log ((c * N : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by
      exact_mod_cast (show 1 < c * N by
        have hNc : N ≤ c * N := Nat.le_mul_of_pos_left N hc
        omega))
  have hlogEq :
      Real.log ((c * N : ℕ) : ℝ) =
        Real.log ((N - 1 : ℕ) : ℝ) +
          Real.log (((c * N : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) := by
    rw [Real.log_div hmulPos.ne' hsubPos.ne']
    ring
  rw [hlogEq]
  field_simp [hlogSubNe, hlogMulNe]

theorem tendsto_log_radius_div_log_const_mul
    {alpha : ℝ} (halpha : 0 < alpha) (c : ℕ) (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      Real.log (maynardRadius alpha N) / Real.log ((c * N : ℕ) : ℝ))
      atTop (nhds alpha) := by
  have hr := BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_log_sub
    halpha
  have hs := tendsto_log_nat_sub_one_div_log_const_mul c hc
  have hmul := hr.mul hs
  simpa only [mul_one] using hmul.congr' (by
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hlogSub : Real.log ((N - 1 : ℕ) : ℝ) ≠ 0 := by
      apply ne_of_gt
      exact Real.log_pos (by exact_mod_cast (show 1 < N - 1 by omega))
    field_simp [hlogSub])

theorem tendsto_affinePrimeIntervalFactor
    {alpha : ℝ} (halpha : 0 < alpha) (A : ℕ) (hA : 0 < A) :
    Tendsto (fun N : ℕ =>
      (affinePrimeIntervalCount N A / (N : ℝ)) *
        Real.log (maynardRadius alpha N)) atTop (nhds alpha) := by
  have hpnt : Tendsto
      (fun n : ℕ => (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    simpa only [primeCountTotal, BoundedGaps.ordinaryPrimeNumberTheorem] using
      BoundedGaps.unconditional_ordinaryPrimeNumberTheorem
  have hmulAtTop (c : ℕ) (hc : 0 < c) :
      Tendsto (fun N : ℕ => c * N) atTop atTop := by
    have ht : Tendsto (fun N : ℕ => c • N) atTop atTop :=
      tendsto_id.nsmul_atTop hc
    simpa [nsmul_eq_mul, mul_comm] using ht
  have hPntLower : Tendsto (fun N : ℕ =>
      (primeCountTotal (A * N) : ℝ) * Real.log ((A * N : ℕ) : ℝ) /
        ((A * N : ℕ) : ℝ)) atTop (nhds 1) := by
    simpa [Function.comp_def] using hpnt.comp (hmulAtTop A hA)
  have h2A : 0 < 2 * A := Nat.mul_pos (by norm_num) hA
  have hPntUpper : Tendsto (fun N : ℕ =>
      (primeCountTotal (2 * A * N) : ℝ) *
        Real.log ((2 * A * N : ℕ) : ℝ) /
          ((2 * A * N : ℕ) : ℝ)) atTop (nhds 1) := by
    simpa [Function.comp_def, mul_assoc] using hpnt.comp (hmulAtTop (2 * A) h2A)
  have hLogLower := tendsto_log_radius_div_log_const_mul halpha A hA
  have hLogUpper := tendsto_log_radius_div_log_const_mul halpha (2 * A) h2A
  have hLower := hPntLower.mul hLogLower
  have hUpper := hPntUpper.mul hLogUpper
  have hcomb := hUpper.const_mul 2 |>.sub hLower
  have hlim : (2 : ℝ) * (1 * alpha) - 1 * alpha = alpha := by ring
  rw [hlim] at hcomb
  apply hcomb.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hANpos : 0 < A * N := Nat.mul_pos hA (by omega)
  have h2ANpos : 0 < 2 * A * N := Nat.mul_pos h2A (by omega)
  have hlogAN : Real.log ((A * N : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by exact_mod_cast (show 1 < A * N by
      have hle : N ≤ A * N := Nat.le_mul_of_pos_left N hA
      omega))
  have hlog2AN : Real.log ((2 * A * N : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by
      exact_mod_cast (show 1 < 2 * A * N by
        have hANone : 1 ≤ A * N := Nat.one_le_iff_ne_zero.mpr hANpos.ne'
        have htwo : 2 ≤ 2 * (A * N) := Nat.mul_le_mul_left 2 hANone
        simpa [mul_assoc] using (show 1 < 2 * (A * N) by omega)))
  have hAreal : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold affinePrimeIntervalCount
  simp only [mul_comm, mul_left_comm]
  push_cast
  have hlogAN' : Real.log ((A : ℝ) * (N : ℝ)) ≠ 0 := by
    simpa [Nat.cast_mul] using hlogAN
  have hlog2AN' : Real.log ((A : ℝ) * (N : ℝ) * 2) ≠ 0 := by
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hlog2AN
  field_simp [hlogAN', hlog2AN', hAreal, hNreal]
  have hcanc : Real.log ((A : ℝ) * (N : ℝ) * 2) *
      (Real.log ((A : ℝ) * (N : ℝ) * 2))⁻¹ = 1 :=
    mul_inv_cancel₀ hlog2AN'
  calc
    _ = Real.log (maynardRadius alpha N) *
          (primeCountTotal (A * N * 2) : ℝ) *
          (Real.log ((A : ℝ) * (N : ℝ) * 2) *
            (Real.log ((A : ℝ) * (N : ℝ) * 2))⁻¹) -
        Real.log (maynardRadius alpha N) *
          (primeCountTotal (A * N) : ℝ) := by ring
    _ = _ := by rw [hcanc]; ring

def affineTupleMaynardS2Main
    (H : Finset ℕ) (A : H → ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  affineRestrictedS2Main H A (tupleMaynardSupport H alpha N)
    (maynardModulus N) N (tupleMaynardCoefficient H alpha F N)

def affineTupleMaynardS2Error
    (H : Finset ℕ) (A : H → ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  affineRestrictedS2Error H A (tupleMaynardSupport H alpha N)
    (maynardRadius alpha N) (maynardModulus N) N
    (tupleMaynardCoefficient H alpha F N)
    (tupleMaynardS2SupportProof H alpha N)

theorem eventually_affineTupleMaynardS2_eq_main_add_error
    {H : Finset ℕ} (A : H → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A) {theta delta : ℝ}
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta)
    (hdeltaTheta : delta < theta / 2) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      affinePrimeWeightedSieveSum H A N
          (affineTupleMaynardWeight H A (theta / 2 - delta) F N) =
        affineTupleMaynardS2Main H A (theta / 2 - delta) F N +
          affineTupleMaynardS2Error H A (theta / 2 - delta) F N := by
  filter_upwards [eventually_affine_coverage A hApos hAinj,
    BoundedGaps.Maynard.eventually_engelsmaMaynardRadius_le
      hthetaHalf hdelta hdeltaTheta] with N hcover hRN
  let D := tupleMaynardSupport H (theta / 2 - delta) N
  let lambda := tupleMaynardCoefficient H (theta / 2 - delta) F N
  have hD : ∀ d ∈ D, IsMaynardDivisorTuple H
      (maynardRadius (theta / 2 - delta) N) (maynardModulus N) d := by
    intro d hd
    exact tupleMaynardS2SupportProof H (theta / 2 - delta) N d
      (by simpa [D] using hd)
  have hpair := affinePrimeWeightedSieveSum_eq_compatiblePairSum
    (A := A) (D := D) (lambda := lambda) (N := N)
    (R := maynardRadius (theta / 2 - delta) N)
    hD hcover.2
  have hsplit := affineCompatiblePrimeWeightedPairSum_eq_main_add_error
    (A := A) (D := D) (lambda := lambda)
    (R := maynardRadius (theta / 2 - delta) N)
    hApos hcover.1 (primorial_pos _) hD hRN
  calc
    affinePrimeWeightedSieveSum H A N
        (affineTupleMaynardWeight H A (theta / 2 - delta) F N) =
        affineCompatiblePrimeWeightedPairSum H A D (maynardModulus N) N
          lambda := by
      simpa [affineTupleMaynardWeight, D, lambda] using hpair
    _ = affineTupleMaynardS2Main H A (theta / 2 - delta) F N +
        affineTupleMaynardS2Error H A (theta / 2 - delta) F N := by
      simpa [affineTupleMaynardS2Main, affineTupleMaynardS2Error,
        D, lambda] using hsplit

private theorem affine_restricted_main_term_normalized_eq
    {H : Finset ℕ} {alpha P : ℝ} {N : ℕ} (m : H)
    (hN : 0 < N)
    (hRnat : 0 < Real.log (maynardRadius alpha N))
    (hRreal : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) :
    (P * ((Nat.totient (maynardModulus N) : ℝ)⁻¹ *
          tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m)) /
        tupleMaynardScale H alpha N =
      ((P / (N : ℝ)) * Real.log (maynardRadius alpha N)) *
        (Real.log (maynardRadius alpha N) /
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
            Fintype.card H *
        (tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (maynardRadius alpha N) ^ 2 *
            tupleNaturalScale (tupleOffFace H m) alpha N)) := by
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := maynardModulus N
  let S := BoundedGaps.Maynard.preSieveSingularSeries D
  let Ln := Real.log (maynardRadius alpha N)
  let Lr := Real.log
    (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
  let K := Fintype.card H
  have hWnat : 0 < W := by
    dsimp [W, maynardModulus]
    exact primorial_pos _
  have hW : (0 : ℝ) < W := by exact_mod_cast hWnat
  have hphiNat : 0 < Nat.totient W := Nat.totient_pos.mpr hWnat
  have hphi : (0 : ℝ) < Nat.totient W := by exact_mod_cast hphiNat
  have hS : 0 < S := by
    dsimp [S]
    exact BoundedGaps.Maynard.preSieveSingularSeries_pos _
  have hK : 0 < K := Fintype.card_pos_iff.mpr ⟨m⟩
  have hcard : Fintype.card (tupleOffFace H m) = K - 1 := by
    calc
      Fintype.card (tupleOffFace H m) = (tupleOffFace H m).card :=
        Fintype.card_coe _
      _ = H.card - 1 := by
        unfold tupleOffFace
        rw [Finset.card_erase_of_mem m.2]
      _ = K - 1 := by simp [K]
  have hnatScale :
      S ^ 2 * Ln ^ 2 * tupleNaturalScale (tupleOffFace H m) alpha N =
        (S * Ln) ^ (K + 1) := by
    have hExp : K + 1 = 2 + (K - 1) := by omega
    unfold tupleNaturalScale
    rw [hcard, hExp, pow_add]
    ring
  change
    (P * ((Nat.totient W : ℝ)⁻¹ *
      tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m)) /
      tupleMaynardScale H alpha N = _
  rw [show
      BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (maynardRadius alpha N) ^ 2 *
          tupleNaturalScale (tupleOffFace H m) alpha N =
        (S * Ln) ^ (K + 1) by simpa [S, Ln, D] using hnatScale]
  unfold tupleMaynardScale BoundedGaps.Maynard.maynardSieveScale
  change
    (P * ((Nat.totient W : ℝ)⁻¹ *
        tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m)) /
      (((Nat.totient W : ℝ) ^ K * (N : ℝ) * Lr ^ K) /
        (W : ℝ) ^ (K + 1)) = _
  have hSeq : S = (Nat.totient W : ℝ) / (W : ℝ) := by
    simpa [S, W, D, maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div D
  rw [hSeq]
  dsimp [Ln, Lr, K]
  simp only [div_pow]
  ring_nf
  field_simp [hW.ne', hphi.ne', (Nat.cast_pos.mpr hN).ne',
    hRnat.ne', hRreal.ne', inv_inv]
  let T := P * tupleRestrictedGKernel H alpha
    (tupleLargeCandidate H) N m
  change T = T * Real.log (maynardRadius alpha N) ^ Fintype.card H *
    (1 / Real.log (maynardRadius alpha N)) ^ Fintype.card H
  have hcancel :
      Real.log (maynardRadius alpha N) ^ Fintype.card H *
          (1 / Real.log (maynardRadius alpha N)) ^ Fintype.card H = 1 := by
    rw [← mul_pow]
    field_simp [hRnat.ne']
    exact one_pow _
  rw [mul_assoc, hcancel, mul_one]

theorem eventually_largeAffineS2Main_normalized_gt
    (A : largePowerTuple → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A)
    {alpha beta c : ℝ} (halpha : 0 < alpha)
    (hbeta : 0 < beta) (hbetaAlpha : beta < alpha)
    (hc : 0 < c) (hcCoeff : c < largeFiberLowerCoefficient) :
    ∀ᶠ N : ℕ in atTop,
      (largeK : ℝ) * beta * c <
        affineTupleMaynardS2Main largePowerTuple A alpha
            largeTupleCandidate N /
          tupleMaynardScale largePowerTuple alpha N := by
  let factor := fun (m : largePowerTuple) (N : ℕ) =>
    ((affinePrimeIntervalCount N (A m) / (N : ℝ)) *
        Real.log (maynardRadius alpha N)) *
      (Real.log (maynardRadius alpha N) /
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
          Fintype.card largePowerTuple
  let kernel := fun (m : largePowerTuple) (N : ℕ) =>
    tupleRestrictedGKernel largePowerTuple alpha
        (tupleLargeCandidate largePowerTuple) N m /
      (BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
        Real.log (maynardRadius alpha N) ^ 2 *
        tupleNaturalScale (largeOffFace m) alpha N)
  have hfactor (m : largePowerTuple) :
      Tendsto (factor m) atTop (nhds alpha) := by
    have hp := tendsto_affinePrimeIntervalFactor halpha (A m) (hApos m)
    have hr :=
      (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
        halpha).pow (Fintype.card largePowerTuple)
    simpa [factor] using hp.mul hr
  have hall : ∀ᶠ N : ℕ in atTop,
      ∀ m : largePowerTuple, beta < factor m N ∧ c < kernel m N := by
    have hall' := (Finset.univ : Finset largePowerTuple).eventually_all.mpr
      (fun m hm =>
        ((hfactor m).eventually (eventually_gt_nhds hbetaAlpha)).and
          (eventually_tupleRestrictedGKernel_normalized_gt
            m halpha hcCoeff))
    simpa [kernel] using hall'
  have hRnat :=
    BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hRreal : Tendsto (fun N : ℕ =>
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N))
      atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply (tendsto_rpow_atTop halpha).comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  filter_upwards [hall, hRnat.eventually (eventually_gt_atTop 0),
    hRreal.eventually (eventually_gt_atTop 0),
    eventually_ge_atTop 1, eventually_affine_coverage A hApos hAinj] with
      N hallN hLn hLr hN hcover
  have hmain := affineRestrictedS2Main_eq_shift_sum
    (N := N) (D := tupleMaynardSupport largePowerTuple alpha N)
    (R := maynardRadius alpha N) (W := maynardModulus N)
    (lambda := tupleMaynardCoefficient largePowerTuple alpha
      largeTupleCandidate N)
    hApos hcover.1 (primorial_pos _)
    (tupleMaynardS2SupportProof largePowerTuple alpha N)
  change affineTupleMaynardS2Main largePowerTuple A alpha
      largeTupleCandidate N / tupleMaynardScale largePowerTuple alpha N > _
  have hmain' : affineTupleMaynardS2Main largePowerTuple A alpha
      largeTupleCandidate N =
      ∑ m ∈ largePowerTuple.attach,
        affinePrimeIntervalCount N (A m) *
          tupleRestrictedMainCoefficient largePowerTuple alpha
            largeTupleCandidate N m := by
    simpa [affineTupleMaynardS2Main, tupleRestrictedMainCoefficient] using hmain
  rw [hmain', Finset.sum_div]
  have hattach : largePowerTuple.attach.Nonempty := by
    let m : largePowerTuple := ⟨2, mem_largePowerTuple.mpr
      ⟨0, largeK_pos, by norm_num⟩⟩
    exact ⟨m, Finset.mem_attach largePowerTuple m⟩
  calc
    (largeK : ℝ) * beta * c =
        ∑ _m ∈ largePowerTuple.attach, beta * c := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_attach,
        largePowerTuple_card]
      ring
    _ < ∑ m ∈ largePowerTuple.attach, factor m N * kernel m N := by
      apply Finset.sum_lt_sum_of_nonempty hattach
      intro m hm
      have hf := (hallN m).1
      have hk := (hallN m).2
      exact mul_lt_mul hf hk.le hc (hbeta.trans hf).le
    _ = ∑ m ∈ largePowerTuple.attach,
        (affinePrimeIntervalCount N (A m) *
          tupleRestrictedMainCoefficient largePowerTuple alpha
            largeTupleCandidate N m) /
          tupleMaynardScale largePowerTuple alpha N := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [tupleRestrictedMainCoefficient_eq_invTotient_mul_GKernel]
      rw [← tupleLargeCandidate_largePowerTuple_eq]
      have heq := affine_restricted_main_term_normalized_eq
        (P := affinePrimeIntervalCount N (A m)) m (by omega) hLn hLr
      dsimp only [factor, kernel]
      rw [← tupleOffFace_largePowerTuple]
      exact heq.symm

end

end Erdos372.AffineMaynard
